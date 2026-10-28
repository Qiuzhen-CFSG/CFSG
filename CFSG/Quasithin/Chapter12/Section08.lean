module

public import CFSG.Quasithin.Chapter12.Section08.RankTwo
public import CFSG.Quasithin.Chapter12.Section08.SourceGeometry
public import CFSG.Quasithin.Chapter12.Section08.Parabolic

/-!
# General techniques for a binary natural module

Aschbacher–Smith, *The Classification of Quasithin Groups*, combined manuscript
of 1 March 2004, §12.8, printed pp.849–857. Lemma 12.8.13 ends on p.857.

This assembly exports the exact rank-two hypothesis, the elementary order-four
seed deduction, and the actual flag, residuals, parabolic and quotient markings.
It also exports the conjugate-intersection criterion for 12.8.6(1–3), conditional
on the transitivity and escape assertions of 12.8.3, and the elementary
parabolic containments in 12.8.13(1–2).
The marked parabolic exports include the binary core factorization and
natural-module decomposition in 12.8.9(2), and the three fixed/moved-space
equalities in (3). The literal elementary quotient and its action are
constructed from the earlier S₃ quotient, supplement, commutator and square
inputs. The equality [E,I₂]=V₂ follows from the two original point
commutators, retaining the source generation and index hypotheses.

The higher-rank setup, 12.8.4–5, the F.8/F.9 identifications, and the remaining
almost-extraspecial and parabolic analysis through 12.8.13 remain required for
the complete section. None is replaced by a conclusion-bearing record.

There is a source typo in the first equality of 12.8.9(1), printed p.852:
`⟨Uᴴ⟩ = I₂` cannot hold because H already normalizes U. The proof on p.853
explicitly establishes the intended `⟨Uᴳ²⟩ = I₂`, with G₂ = N_G(V₂).
-/
