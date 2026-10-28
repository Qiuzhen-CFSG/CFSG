module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.NonseedOppositeImpurity

/-!
# Original involution nonfusion across the two nonseed extensions

The whole original point core is transitive on the exterior of either
sixteen extension. A marked-class point in the opposite extension would
therefore make that entire extension pure, contradicting the original
point-core incidence obstruction.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- The opposite reflection differs from the original marked involution
class. All groups, cores and generators belong to the original group. -/
theorem TypeAt.opposite_nonseed_reflection_not_isConj (h : TypeAt z V)
    (E : pointCoreEights z) (hEn : E.val ∉ pointCoreSeedOrbit z V)
    (A B : Subgroup G) [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hA : Nat.card A=16) (hB : Nat.card B=16) (hEA : E.val ≤ A) (hEB : E.val ≤ B)
    (c b : G) (hc2 : c^2=z)
    (hcZ : c ∈ (center ((involutionCentralizer z).pCoreIn 2)).map
      ((involutionCentralizer z).pCoreIn 2).subtype)
    (hbA : b ∈ A) (hbE : b ∉ E.val) (hcbB : c*b ∈ B) (hcbE : c*b ∉ E.val)
    (hbc : b*c*b⁻¹=c⁻¹)
    (hpureA : ∀ a ∈ A, a≠1 → IsConj a z) : ¬ IsConj (c*b) z := by
  intro hcbz
  apply h.opposite_nonseed_extensions_not_both_pure E hEn A B hA hB hEA hEB
    c b hc2 hcZ hbA hbE hcbB hcbE hbc hpureA
  intro x hx hx1
  by_cases hxE : x∈E.val
  · let : IsElementaryAbelian 2 E.val := E.property.2.2.1
    exact h.centralizer_core_involution_isConj x (E.property.1 hxE)
      (orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian x hxE) hx1)
  · obtain ⟨q,_,hq⟩ := h.nonseed_extension_exterior_transitive E hEn B hB hEB
      (c*b) hcbB hcbE x hx hxE
    exact (isConj_iff.mpr ⟨q,hq⟩).symm.trans hcbz

end CFSG.Quasithin.HigmanSims
