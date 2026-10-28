module
public import Theory.GroupTheory.GeneralizedFitting.CenterlessTwoQuotient
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.NormalClosureCentralizerCore

/-!
# The centralizer in a quasisimple group with a two-subgroup supplement

For a centerless normal quasisimple subgroup K and a two-subgroup P,
the centralizer of K inside KP is exactly O₂(KP). Restrict K to the
literal join, identify its two-group quotient, and apply the existing
centerless-extension calculation. Normality is relative to that join.

Source application: Aschbacher--Smith 5.1.23, printed pp.645--646,
refs/quasithin.pdf; comparison with the original H-image.
-/

public noncomputable section
open Subgroup

namespace Theory.GroupTheory
variable {X : Type*} [Group X] [Finite X]

theorem centralizer_inf_sup_eq_twoCore
    (K P : Subgroup X) [K.Normal] [IsQuasisimple K]
    (hz : center K = ⊥) (hP : IsPGroup 2 P) :
    (K ⊔ P) ⊓ centralizer (K : Set X) = (K ⊔ P).pCoreIn 2 := by
  let J := K ⊔ P
  let K₀ := K.subgroupOf J
  let e : K₀ ≃* K := subgroupOfEquivOfLe (show K ≤ J from le_sup_left)
  let : IsQuasisimple K₀ := IsQuasisimple.of_mulEquiv e.symm
  have hz₀ : center K₀ = ⊥ := by
    apply card_eq_one.mp
    rw [Nat.card_congr (centerCongr e).toEquiv,hz]
    simp
  have hquot : IsPGroup 2 (J ⧸ K₀) :=
    isPGroup_quotient_of_sup_eq_top K₀ (P.subgroupOf J) hP.comap_subtype
      (by rw [← subgroupOf_sup le_sup_left le_sup_right]; exact subgroupOf_self J)
  have hh := congrArg (Subgroup.map J.subtype)
    (centralizer_eq_twoCore_of_centerless_quasisimple_quotient K₀ hz₀ hquot)
  rw [map_centralizer_subtype,map_subgroupOf_eq_of_le (show K ≤ J from le_sup_left)] at hh
  exact hh
end Theory.GroupTheory
