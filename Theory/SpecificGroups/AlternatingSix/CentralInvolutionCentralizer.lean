module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.Inner
public import Theory.GroupTheory.DihedralGeneratedFactor

/-!
# The center of an involution centralizer in A₆

An involution centralizer in A₆ is dihedral of order eight, so its center
has order two. Consequently a subgroup central in a marked involution
centralizer has order at most two. The statement retains an arbitrary
equivalence with A₆ and the original centralizer subgroup.

Source: the A₆ alternative in Aschbacher–Smith E.2.7, printed p.220;
the dihedral centralizer calculation is the standard A₆ local geometry.
-/

public section
open Subgroup
namespace AlternatingSix
variable {G : Type*} [Group G]

/-- The original involution centralizer has center of order two under an
actual equivalence with A₆. -/
theorem involution_centralizer_center_card
    (e : G ≃* alternatingGroup (Fin 6)) (z : G) (hz : orderOf z = 2) :
    Nat.card (center (centralizer ({z} : Set G))) = 2 := by
  let C := centralizer ({z} : Set G)
  let D := centralizer ({e z} : Set (alternatingGroup (Fin 6)))
  let f : C ≃* D := {
    toFun x := ⟨e x, mem_centralizer_singleton_iff.mpr (by
      simpa only [map_mul] using congrArg e (mem_centralizer_singleton_iff.mp x.property))⟩
    invFun x := ⟨e.symm x, mem_centralizer_singleton_iff.mpr (by
      simpa only [map_mul, MulEquiv.symm_apply_apply] using
        congrArg e.symm (mem_centralizer_singleton_iff.mp x.property))⟩
    left_inv x := Subtype.ext (e.symm_apply_apply x)
    right_inv x := Subtype.ext (e.apply_symm_apply x)
    map_mul' x y := Subtype.ext (e.map_mul x y) }
  obtain ⟨d⟩ := ShadowLocal.inner_involution_fixed_equiv_dihedral
    (e z) ((e.orderOf_eq z).trans hz)
  rw [ShadowLocal.inner_fixed_eq_centralizer] at d
  exact DihedralGroup.center_card_of_equiv (n := 2) (by decide) (f.trans d)

/-- A central subgroup of a marked involution centralizer in A₆ has order
at most two. -/
theorem central_subgroup_card_le_two
    (e : G ≃* alternatingGroup (Fin 6)) (U V : Subgroup G)
    (z : G) (hz : orderOf z = 2) (hC : centralizer ({z} : Set G) = U)
    (hc : V ≤ (center U).map U.subtype) : Nat.card V ≤ 2 := by
  let : Finite G := Finite.of_equiv (alternatingGroup (Fin 6)) e.toEquiv.symm
  have h := card_le_of_le hc
  rw [card_map_of_injective U.subtype_injective, ← hC,
    involution_centralizer_center_card e z hz] at h
  exact h

end AlternatingSix
