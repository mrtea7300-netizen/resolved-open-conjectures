# Reporting the A157218 counterexample

Authors (order as given by Yotam): Yotam Moshe, Idan Gan Levi, Ohav Betito, Boaz Cohen, Shay Gez Akiva.

| Channel | State |
|---|---|
| X post | **Posted** 2026-11-25 — <https://x.com/YotamMe/status/2125702785434034283> |
| Public code | **Published** 2026-11-25 — <https://github.com/yotam1001/sun-a157218-counterexample> (a separate repo; this working repo stays private) |
| Paper | Draft PDF in the public repo: `paper/paper.pdf` |
| Email to Prof. Sun | **Sent** by Yotam (he confirmed it on 2026-11-26; text in [`email_to_sun.txt`](email_to_sun.txt)); no reply recorded yet |
| OEIS | **Account approved; edits to A157218 and A157225 proposed 2026-11-26**, waiting for an OEIS editor (<https://oeis.org/draft/A157218>, <https://oeis.org/draft/A157225>). See section 1. |

## 1a. OEIS account request — submitted 2026-11-26

OEIS now signs in by an emailed one-time link (or Google / GitHub); the old wiki request form is gone.
Submitted at <https://oeis.org/account> with Yotam's approval of the text and of the terms of use:

- **Name to be known by:** Yotam Moshe
- **About you** (this becomes the public OEIS wiki user page):

> I am a 17-year-old student at ORT Ironi D in Israel, interested in number theory and
> computational mathematics. Together with four friends (Idan Gan Levi, Ohav Betito, Boaz Cohen and
> Shay Gez Akiva) I run computer searches on conjectures of Zhi-Wei Sun recorded in the OEIS. We
> found that the conjecture in A157218 fails at 2n-1 = 445466268731, and that A157225 has three
> further counterexamples below 10^12; I would like to contribute these comments and the related
> verification bounds for A157237 and A155904. The searches were done with the help of an AI
> assistant (Claude), and every claim is backed by code that anyone can rerun:
> https://github.com/yotam1001/sun-a157218-counterexample

To check the status: open <https://oeis.org/login>, enter the email, and open the link it sends.

## 1. OEIS edits

OEIS comments are signed by the account holder; the other finders are credited in the text.
Yotam's rule from 2026-11-26: OEIS uploads are allowed; everything else about new results stays in
this repository until the end-of-week choice.

### Proposed 2026-11-26 (waiting for an editor)

Both were submitted from the account "Yotam Moshe" and are in state *proposed*. Before submitting,
the PARI programs below were run with `.tools/gp.exe`: they reproduce the first 50 terms of each
entry and return 0 at every claimed counterexample; the "342 values, all composite" count was
recomputed as well.

**A157218 — comment** (edit #17/#18)

> The conjecture is false: a(222733134366) = 0, that is, the odd number 445466268731 = 11^3*2999*111599
> cannot be written as p + 2^x + 7*2^y with p a prime congruent to 1 mod 6 and x, y positive integers.
> (Since 445466268731 == 5 (mod 6), x and y must both be odd, and all 342 positive values of
> 445466268731 - 2^x - 7*2^y with x, y odd are composite.) A search found no other counterexample
> among the odd integers below 10^13. Found by Yotam Moshe, Idan Gan Levi, Ohav Betito, Boaz Cohen
> and Shay Gez Akiva. - _Yotam Moshe_, Nov 26 2026

**A157218 — link**

> Yotam Moshe et al., <a href="https://github.com/yotam1001/sun-a157218-counterexample">A counterexample to Sun's conjecture in A157218: verification script, certificate and search code</a>, GitHub, 2026.

**A157218 — program**

> (PARI) a(n)=my(m=2*n-1, c=0, q); for(x=1, logint(m, 2), for(y=1, logint(m, 2), q=m-2^x-7*2^y; if(q>1 && q%6==1 && isprime(q), c++))); c \\ _Yotam Moshe_, Nov 26 2026

**A157225 — comment** (edit #15/#16; sister sequence, p == 5 mod 6)

> Besides n = 716993899, also a(n) = 0 for n = 22741830739, 42652775884, 183542134826 and
> 786325016174, that is, the odd numbers 45483661477, 85305551767, 367084269651 and 1572650032347
> cannot be written in this form either. A search found no further n > 992 with a(n) = 0 and
> 2n-1 < 10^13. - _Yotam Moshe_, Nov 26 2026

**A157225 — program**

> (PARI) a(n)=my(m=2*n-1, c=0, q); for(x=1, logint(m, 2), for(y=1, logint(m, 2), q=m-2^x-7*2^y; if(q>1 && q%6==5 && isprime(q), c++))); c \\ _Yotam Moshe_, Nov 26 2026

### Next batch (not submitted; send after the first two are approved)

OEIS asks new contributors to keep only a few proposals open at a time.

- **A303540** (also A303539): 210107364447 is not of the form x^2 + y^2 + C(2k,k) + C(2m,m)
  (quote the entry's exact wording when drafting).
- **A302982**: 558556427 is not of the form x^2 + 5y^2 + 2^z + 3*2^w.
- **A157237**: "Sun's conjecture has been verified for odd integers below 10^13."
- **A155904**: "a(n) > 0 has been verified for all odd integers 15 <= 2n-1 < 10^12."
- The four incomplete "a(n) = 1 only for ..." lists (A262945, A270594, A270920, A352356).

The "no other counterexample" statements rest on our own engine only (validated, but not
independently re-implemented), which is why they are worded "a search found". The single-number
statements are independently verified.

## 2. Email to Prof. Zhi-Wei Sun (zwsun@nju.edu.cn)

Subject: `A counterexample to your conjecture in OEIS A157218`. Body: [`email_to_sun.txt`](email_to_sun.txt).

## 3. X post — POSTED 2026-11-25 by @YotamMe

- Main post: https://x.com/YotamMe/status/2125702785434034283
- Reply tagging collaborators: https://x.com/YotamMe/status/2125702895622365565

> Conjecture (Zhi-Wei Sun, 2009, OEIS A157218): every odd integer > 34 can be written as
> p + 2^x + 7·2^y, where p is a prime ≡ 1 (mod 6) and x, y ≥ 1.
>
> 445466268731 is a counterexample to this problem.
>
> It is the only one below 10^12 (previously verified up to 1.5·10^8).

Reply: `@MrTeaEnjoyer1 @shl0mpy @boazcohenj @wbtytw29423`

Format for future results (requested by Yotam): state the conjecture, then "N is a counterexample
to this problem"; tag the collaborators in a reply, not in the main post.

Suggested follow-up reply (not posted):

> Code, a certificate and a short paper: https://github.com/yotam1001/sun-a157218-counterexample
> The sister conjecture A157225 has four counterexamples below 10^12 — three of them new.
