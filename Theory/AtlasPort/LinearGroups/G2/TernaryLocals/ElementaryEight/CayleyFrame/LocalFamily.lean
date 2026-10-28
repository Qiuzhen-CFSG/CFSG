module

public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.ElementaryEight.CayleyFrame
public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.Involution

/-!
# Three actual two-local subgroups of the ternary octonion group

Retain the old involution and torus/Weyl-eight normalizers and adjoin the
normalizer of the all-norm-one Cayley-frame eight. Each is the ambient normalizer
of a proved nonidentity two-subgroup. Their intrinsic two-cores are
self-centralizing, and none of their orders is divisible by 27.

The first two calculations are reused from `Involution` and `ElementaryEight`;
the third is proved in `CayleyFrame`. This family does not assert coverage of
maximal two-locals. That is the remaining geometric input for its consumers.

Source context: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Theorem 0.1.2(4), pp.3–4 and 481–482; §I.4(G1–G2), p.417.
The concrete groups use the licensed ATLAS octonion port; see LICENSES/ATLAS.txt
and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

namespace Atlas.G2.TernaryLocals.CayleyEight

/-- Both old local normalizers, followed by the new Cayley-frame normalizer. -/
def localFamily : Fin 3 → Subgroup (Model (ZMod 3)) :=
  ![localSubgroup false, localSubgroup true, normalizer]

@[simp] theorem localFamily_zero : localFamily 0 = localSubgroup false := rfl
@[simp] theorem localFamily_one : localFamily 1 = localSubgroup true := rfl
@[simp] theorem localFamily_two : localFamily 2 = normalizer := rfl

/-- Every family member has its actual nonidentity two-group normalizer witness. -/
theorem localFamily_isTwoLocal (i : Fin 3) : IsTwoLocal (localFamily i) := by
  fin_cases i
  · exact localSubgroup_isTwoLocal false
  · exact localSubgroup_isTwoLocal true
  · exact normalizer_isTwoLocal

/-- All three local orders satisfy the required three-rank divisibility bound. -/
theorem localFamily_three_cube_not_dvd_card (i : Fin 3) :
    ¬ 3^3 ∣ Nat.card (localFamily i) := by
  fin_cases i
  · change ¬ 3^3 ∣ Nat.card Involution.P
    rw [Involution.card]
    decide
  · exact ElementaryEight.three_cube_not_dvd_card_localSubgroup_true
  · exact three_cube_not_dvd_card_normalizer

/-- All three actual locals have a self-centralizing intrinsic two-core. -/
theorem localFamily_centralizer_pCore (i : Fin 3) :
    Subgroup.centralizer (pCore 2 (localFamily i) : Set (localFamily i)) ≤
      pCore 2 (localFamily i) := by
  fin_cases i
  · exact Involution.centralizer_pCore
  · exact ElementaryEight.localSubgroup_true_centralizer_pCore
  · exact normalizer_centralizer_pCore

end Atlas.G2.TernaryLocals.CayleyEight
