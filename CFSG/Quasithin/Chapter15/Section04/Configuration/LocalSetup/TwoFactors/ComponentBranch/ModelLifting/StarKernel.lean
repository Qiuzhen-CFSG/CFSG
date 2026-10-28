module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.Classification
public import Theory.GroupTheory.GeneralizedFitting.ComponentCenterPrimeCore
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# The kernel on the original component of the mixed group

F.6.11 makes O_{3′}(I) solvable, so it cannot contain a component and hence
centralizes every component. Trivial O(I) makes the component center its
two-core. Subnormal core containment puts that center in O₂(I) ≤ O_{3′}(I).
Thus the literal star map has kernel exactly Z(L), and its image is a
nontrivial simple component, canonically isomorphic to L/Z(L).

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, F.6.11,
printed pp.306–307, and the component paragraph of 15.4.18, pp.1162–1163.
This identifies a central quotient, not the original component carrier.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors
open ComponentBranch
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.ModelLifting

variable {I : Type*} [Group I] [Finite I]

/-- The original component has two-group center, with its intrinsic core. -/
theorem component_center_eq_twoCore (L : Subgroup I) (hL : IsComponent I L)
    (hodd : pPrimeCore 2 I = ⊥) : center L = pCore 2 L := by
  let := hL.2
  exact IsQuasisimple.center_eq_pCore (hL.1.pPrimeCore_eq_bot hodd L)

/-- The actual star map restricted to the original component kills precisely its center. -/
theorem star_kernel_eq_center (L : Subgroup I) (hL : IsComponent I L)
    (hodd : pPrimeCore 2 I = ⊥) (hs : Group.IsSolvable (pPrimeCore 3 I)) :
    ((QuotientGroup.mk' (pPrimeCore 3 I)).subgroupMap L).ker = center L := by
  let := hL.2
  let := hs
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  have hnot : ¬ L ≤ pPrimeCore 3 I := by
    intro hle
    let : Group.IsSolvable L := Group.isSolvable_of_isSolvable_injective
      (inclusion_injective hle)
    exact Group.IsPerfect.not_isSolvable L inferInstance
  have hc := (hL.normal_dichotomy (pPrimeCore 3 I)).resolve_left hnot
  have h23 : pCore 2 I ≤ pPrimeCore 3 I := by
    apply le_sSup
    refine ⟨inferInstance, ?_⟩
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := I)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  apply le_antisymm
  · intro x hx
    have hxN : (x : I) ∈ pPrimeCore 3 I :=
      (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hx)
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (((commutator_eq_bot_iff_le_centralizer.mp hc) y.property x hxN).symm)
  · intro x hx
    have hx2 : x ∈ pCore 2 L := component_center_eq_twoCore L hL hodd ▸ hx
    have hxI : (x : I) ∈ pCore 2 I :=
      (pCoreIn_le_of_subnormal 2 hL.1) (mem_map_of_mem L.subtype hx2)
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff _).mpr (h23 hxI)

/-- The first isomorphism theorem for the literal star map on L. -/
noncomputable def centralQuotientEquivStar (L : Subgroup I) (hL : IsComponent I L)
    (hodd : pPrimeCore 2 I = ⊥) (hs : Group.IsSolvable (pPrimeCore 3 I)) :
    (L ⧸ center L) ≃* FFBranch.ClassificationComparison.threePrimeImage L :=
  (QuotientGroup.quotientMulEquivOfEq (star_kernel_eq_center L hL hodd hs).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      ((QuotientGroup.mk' (pPrimeCore 3 I)).subgroupMap_surjective L))

/-- The central-quotient equivalence agrees with the original star map on every element. -/
theorem centralQuotientEquivStar_apply (L : Subgroup I) (hL : IsComponent I L)
    (hodd : pPrimeCore 2 I = ⊥) (hs : Group.IsSolvable (pPrimeCore 3 I)) (x : L) :
    (centralQuotientEquivStar L hL hodd hs (QuotientGroup.mk' (center L) x) :
      I ⧸ pPrimeCore 3 I) = QuotientGroup.mk' (pPrimeCore 3 I) (x : I) := rfl

/-- The star image is nontrivial, simple, and subnormal in the actual star quotient. -/
theorem star_isComponent_and_simple (L : Subgroup I) (hL : IsComponent I L)
    (hodd : pPrimeCore 2 I = ⊥) (hs : Group.IsSolvable (pPrimeCore 3 I)) :
    IsComponent (I ⧸ pPrimeCore 3 I) (FFBranch.ClassificationComparison.threePrimeImage L) ∧
      IsSimpleGroup (FFBranch.ClassificationComparison.threePrimeImage L) := by
  let := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let e := centralQuotientEquivStar L hL hodd hs
  let : IsSimpleGroup (FFBranch.ClassificationComparison.threePrimeImage L) := e.symm.isSimpleGroup
  refine ⟨?_, inferInstance⟩
  exact (hL.map_surjective _ (QuotientGroup.mk'_surjective _)).resolve_left
    ((nontrivial_iff_ne_bot _).mp inferInstance)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.ModelLifting
