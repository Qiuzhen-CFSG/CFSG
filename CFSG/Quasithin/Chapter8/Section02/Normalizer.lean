module

public import CFSG.Quasithin.Chapter8.Section02.Normalizer.GroupDeductions
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.TensorDimension

/-!
# Determining the normalizer N_G(U)

Aschbacher–Smith, *The Classification of Quasithin Groups*, §8.2.2,
Lemmas and Propositions 8.2.6–10, printed pp.717–721 (PDF pp.734–738).

The current exports prove the relative-normality, commutator, conjugate-action
and residual deductions, and the opening commutator argument of 8.2.10.
They retain the literal N_L(U)^∞, I = ⟨V,V^h⟩ and O₂(I), with O²(I)
kept separate. Their earlier source premises remain explicit.

The complete natural-action table, quasisimplicity exclusion, marked tensor
recognition, small overgroup inspections, minimal-parabolic exclusions and
covering-group argument are still needed. This module does not claim the
complete source conclusions 8.2.6–10. Their assembly remains here; the Section02
owner supplies the genuine setup and complete conclusions 8.2.2–5.
-/
