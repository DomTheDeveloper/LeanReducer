"""Three Responses API calls. Only a local renderer produces candidate Lean text."""
import json
import os
from pathlib import Path
import re
import urllib.error
import urllib.request

from .source import IDENT

PROMPTS = Path(__file__).resolve().parents[1] / 'agents'
BASIC = ('assumption', 'rfl', 'simp', 'simp_all', 'omega', 'grind', 'aesop',
         'ring', 'linarith', 'nlinarith', 'positivity', 'fun_prop', 'exact?')


def render(proposal):
    if not isinstance(proposal, dict) or set(proposal) != {'tactic', 'lemmas'}:
        raise ValueError('expected a tactic and an array of lemma names')
    tactic, lemmas = proposal['tactic'], proposal['lemmas']
    if not isinstance(lemmas, list) or len(lemmas) > 8 or any(
            not isinstance(s, str) or len(s) > 180 or not re.fullmatch(IDENT, s)
            for s in lemmas):
        raise ValueError('expected up to eight ordinary Lean identifiers')
    if tactic in BASIC and not lemmas:
        return tactic
    if tactic in ('apply', 'exact') and len(lemmas) == 1:
        return f'{tactic} {lemmas[0]}'
    if tactic in ('simp', 'simp_all', 'grind', 'linarith', 'nlinarith') and lemmas:
        return f"{tactic} [{', '.join(lemmas)}]"
    raise ValueError('unsupported tactic or argument count')


def ask(role, model, payload, *, transport=None):
    instructions = (PROMPTS / (role + '.md')).read_text()
    body = {'model': model, 'instructions': instructions, 'input': json.dumps(payload),
            'store': False, 'max_output_tokens': 2000, 'text': {'format': {'type': 'json_object'}}}
    if transport is None:
        key = os.environ.get('OPENAI_API_KEY')
        if not key:
            raise ValueError('AI mode requires OPENAI_API_KEY')
        request = urllib.request.Request('https://api.openai.com/v1/responses',
            json.dumps(body).encode(), {'Authorization': 'Bearer ' + key, 'Content-Type': 'application/json'})
        try:
            with urllib.request.urlopen(request, timeout=120) as response:
                data = json.load(response)
        except urllib.error.HTTPError as exc:
            raise ValueError(f'Responses API returned HTTP {exc.code} for {role}') from exc
    else:
        data = transport(body)
    if data.get('status') != 'completed':
        raise ValueError(f'incomplete {role} response')
    text = ''.join(c['text'] for out in data.get('output', []) if out.get('type') == 'message'
                   for c in out.get('content', []) if c.get('type') == 'output_text')
    return json.loads(text)


def choose(options, model, *, request=ask):
    items = [{'id': i, 'name': b.name, 'module': b.module, 'body_lines': b.lines,
              'statement': b.header[:650]} for i, b in enumerate(options)]
    i = request('planner', model, {'candidates': items})['id']
    if type(i) is not int or i not in range(len(options)):
        raise ValueError('planner selected an unknown declaration')
    return options[i]


def suggestions(source, model, *, request=ask):
    payload = {'lean': source, 'tactics': list(BASIC) + ['apply', 'exact']}
    proposed = request('prover', model, payload)['proposals']
    if not isinstance(proposed, list) or len(proposed) > 8:
        raise ValueError('invalid proposal list')
    attempts = list(dict.fromkeys(render(p) for p in proposed))
    if not attempts:
        return []
    ids = request('reviewer', model, {'lean': source, 'candidates': attempts})['order']
    if not isinstance(ids, list) or any(type(i) is not int or i not in range(len(attempts)) for i in ids):
        raise ValueError('reviewer selected an unknown proposal')
    return list(dict.fromkeys(attempts[i] for i in ids))
