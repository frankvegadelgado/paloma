#!/usr/bin/env python3
"""Upload the paloma goal theorem to Prove2Me: definitions bundle, theorem stub, solution.

Usage: upload.py --platform prove2me/platform [--public] [--execute]
Reads the API key from the environment variable P2M_API_KEY (never printed).
Without --execute it only prints what it would send. Private by default.
"""
import argparse, json, os, sys, time, uuid, urllib.request, urllib.error, urllib.parse

BASE = 'https://prove2.me/api/v1'
ap = argparse.ArgumentParser()
ap.add_argument('--platform', required=True)
ap.add_argument('--public', action='store_true')
ap.add_argument('--execute', action='store_true')
ap.add_argument('--skip-definition', action='store_true', help='reuse the definition bundle already published under the same name')
args = ap.parse_args()
private = not args.public
sha = os.environ.get('GITHUB_SHA', '<commit-sha>')
repo = 'https://github.com/frankvegadelgado/paloma'

goal = json.load(open(f'{args.platform}/upload_goal.json'))
DEF = goal['definition_name']; THM = goal['theorem_name']; SLUG = goal['slug']
defs_src = open(f'{args.platform}/Definitions/Def_{DEF}.lean', encoding='utf-8').read()
sol_src = open(f'{args.platform}/Solutions/Sol_{SLUG}.lean', encoding='utf-8').read()

paper = f'{repo}/blob/{sha}/doc/paper.tex'
meta = json.load(open(f'{args.platform}/meta.json')) if os.path.exists(f'{args.platform}/meta.json') else {}
DEF_NL = (r"Formal model of the three-occurrence Horn formula $T_H$ of a simple $d$-regular graph $H$ "
          r"with a port labelling (`PortGraph`), its independent sets and independence number, and the "
          r"number of clauses of $T_H$ satisfied by an assignment (`satCount`), together with the "
          r"assignment obtained from an independent set. Definitions and the port-structure bijection "
          r"used by them, as in Sections 2 and 3 of the paper.")
THM_NL = (r"Let $G$ be a $D$-regular graph with a port labelling, $D\ge1$, on $n$ vertices and $m$ edges, "
          r"let $\alpha$ be its independence number and let $T_G$ be the three-occurrence Horn formula of "
          r"the paper. Then $\tfrac{83}{84}>0.94615981>0.94016567$, and for every independent set $I$ with "
          r"$18785\,\alpha\le 20000\,|I|$ the assignment obtained from $I$ satisfies "
          r"$$84\cdot\operatorname{sat}(T_G)\ \ge\ 83\,\bigl((D+1)n+m+\alpha\bigr),$$ "
          r"that is, at least $83/84$ of the optimum $(D+1)n+m+\alpha$ of $T_G$. The hypothesis on $I$ is the "
          r"size guaranteed by a Goemans--Williamson cut lifted to the conflict graph (Theorem `thm:cutclass`); "
          r"the cut guarantee itself is not part of the statement. The numbers $0.94615981$ and $0.94016567$ "
          r"are the Unique Games thresholds of Brakensiek--Huang--Zwick and Lewin--Livnat--Zwick.")
EXPL = (r"The comparison $83/84>0.94615981>0.94016567$ is a numerical check (`norm_num`). The second part is the "
        r"lifting step of Theorem `thm:cutclass`: an independent set $I$ with $18785\,\alpha\le20000\,|I|$ yields, "
        r"for every degree $D\ge1$, the threshold inequality $83\,(\text{opt})\le 84\,(\text{opt}-\alpha+|I|)$, and the "
        r"assignment that sets every clone of a vertex outside $I$ to true and every clone of a vertex of $I$ to false satisfies "
        r"$(D+1)n+m+|I|$ clauses (`satCount_eq_score_proof`, `lift_satCount`). Combining the two gives the claim.")

def call(method, path, token=None, body=None, form=None):
    url = BASE + path
    headers = {}
    data = None
    if token: headers['Authorization'] = 'Bearer ' + token
    if body is not None:
        data = json.dumps(body).encode(); headers['Content-Type'] = 'application/json'
    if form is not None:
        boundary = uuid.uuid4().hex
        parts = []
        for k, v in form.items():
            if isinstance(v, tuple):
                fn, content = v
                parts.append(f'--{boundary}\r\nContent-Disposition: form-data; name="{k}"; filename="{fn}"\r\nContent-Type: text/plain\r\n\r\n{content}\r\n')
            else:
                parts.append(f'--{boundary}\r\nContent-Disposition: form-data; name="{k}"\r\n\r\n{v}\r\n')
        data = (''.join(parts) + f'--{boundary}--\r\n').encode()
        headers['Content-Type'] = f'multipart/form-data; boundary={boundary}'
    req = urllib.request.Request(url, data=data, method=method, headers=headers)
    try:
        with urllib.request.urlopen(req, timeout=60) as r:
            return r.status, json.loads(r.read() or b'{}')
    except urllib.error.HTTPError as e:
        return e.code, {'error': e.read().decode(errors='replace')[:2000]}

definition_body = {'definition_name': DEF, 'definition_title': meta.get('definition_title', r'Port graphs, independent sets and the formula $T_H$ (three-occurrence Horn class)'),
                   'definition': defs_src, 'natural_language_statement': meta.get('definition_nl', DEF_NL), 'source': paper,
                   'tags': ['paloma-max2sat'], 'private': private}
THM_NL = meta.get('natural_language_statement', THM_NL); EXPL = meta.get('explanation', EXPL)
problem_body = {'theorem_name': THM, 'theorem_title': meta.get('theorem_title', r'Ratio $83/84$ above the Unique Games thresholds'),
                'formal_statement': goal['formal_statement'], 'natural_language_statement': THM_NL,
                'preamble': goal['preamble'], 'source': paper + '#L' + str(meta.get('source_line', 295)), 'tags': ['paloma-max2sat'], 'private': private}

print('mode:', 'EXECUTE' if args.execute else 'DRY RUN', '| visibility:', 'private' if private else 'PUBLIC')
print('definition:', DEF, len(defs_src), 'chars'); print('theorem:', THM); print('solution:', len(sol_src), 'chars'); print('source:', paper)
if not args.execute: sys.exit(0)

key = os.environ['P2M_API_KEY']
st, r = call('POST', '/agent/refresh', body={'api_key': key})
if st != 200: sys.exit(f'refresh failed: {st}')
token = r['access_token']; t0 = time.time()
def tok():
    global token, t0
    if time.time() - t0 > 2400:
        s, r = call('POST', '/agent/refresh', body={'api_key': key}); token = r['access_token']; t0 = time.time()
    return token

def wait_job(job_id):
    for _ in range(120):
        s, r = call('GET', f'/publish-jobs/{job_id}', tok())
        if r.get('status') in ('PUBLISHED', 'FAILED', 'ERROR'): return r
        time.sleep(10)
    sys.exit('timed out waiting for job ' + job_id)

if args.skip_definition:
    print('submit-definition skipped (reusing the published bundle', DEF + ')')
else:
    st, r = call('POST', '/submit-definition', tok(), definition_body); print('submit-definition', st, {k: r.get(k) for k in ('job_id', 'status', 'error')})
    if st not in (200, 202): sys.exit(1)
    job = wait_job(r['job_id']); print('definition job:', job.get('status'), job.get('error_message', '')[:1500])
    if job.get('status') != 'PUBLISHED': sys.exit(1)

st, r = call('POST', '/submit-problem', tok(), problem_body); print('submit-problem', st, {k: r.get(k) for k in ('jobs', 'errors', 'error')})
if st not in (200, 202) or r.get('errors') or not r.get('jobs'): sys.exit(1)
job = wait_job(r['jobs'][0]['job_id']); print('theorem job:', job.get('status'), job.get('error_message', '')[:1500])
if job.get('status') != 'PUBLISHED': sys.exit(1)
theorem_id = job['theorem_id']; print('theorem_id:', theorem_id)

st, r = call('POST', '/verify', tok(), form={'theorem_id': theorem_id, 'proof_type': 'prove', 'explanation': EXPL, 'file': ('solution.lean', sol_src)})
print('verify', st, {k: r.get(k) for k in ('submission_id', 'status', 'error')})
if st not in (200, 202): sys.exit(1)
sid = r['submission_id']
for _ in range(180):
    s, r = call('GET', f'/verify?submission_id={sid}', tok())
    if r.get('status') != 'PENDING': break
    time.sleep(10)
print('final status:', r.get('status')); print(json.dumps({k: v for k, v in r.items() if k != 'solution'}, ensure_ascii=False)[:2500])
sys.exit(0 if r.get('status') in ('ACCEPTED', 'SKETCH_ACCEPTED') else 1)
