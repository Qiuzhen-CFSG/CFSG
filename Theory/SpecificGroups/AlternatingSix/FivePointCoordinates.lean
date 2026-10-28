module
public import Theory.SpecificGroups.AlternatingSix.PerfectSubgroups
public import Theory.GroupAction.SimpleCosets

/-!
# Actual order-sixty subgroups in the six-letter coordinates

The faithful action of A₆ on the six cosets of an order-sixty subgroup
is an automorphism of A₆. It carries that same subgroup to the stabilizer
of the identity coset. The subgroup marking is retained, rather than
merely identifying its abstract isomorphism type.
-/

public noncomputable section
namespace AlternatingSix.FivePointCoordinates
open Subgroup
local notation "A6" => alternatingGroup (Fin 6)

/-- The actual order-sixty subgroup becomes a point stabilizer under an
actual automorphism of A₆. -/
theorem exists_marked_point_automorphism (H : Subgroup A6) (hH : Nat.card H = 60) :
    ∃ α : MulAut A6, ∃ i : Fin 6,
      H.map α.toMonoidHom = MulAction.stabilizer A6 i := by
  let : IsSimpleGroup A6 := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect A6 := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  have hc : Nat.card A6 = 360 := by
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hi : H.index = 6 := by
    have hh := H.card_mul_index
    rw [hH,hc] at hh
    omega
  have ht : H ≠ ⊤ := by intro h; simp [h] at hi
  let e : (A6 ⧸ H) ≃ Fin 6 := Finite.equivFinOfCardEq hi
  let f : A6 →* Equiv.Perm (Fin 6) :=
    e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom A6 (A6 ⧸ H))
  have hf : Function.Injective f := by
    apply e.permCongrHom.injective.comp
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [← normalCore_eq_ker]
    exact H.normalCore_eq_bot_of_simple ht
  let sign := Equiv.Perm.sign.comp f
  let : Group.IsPerfect sign.range := Group.IsPerfect.range sign
  have hsign (a : A6) : f a ∈ A6 := by
    apply Equiv.Perm.mem_alternatingGroup.mpr
    exact congrArg Subtype.val (Subsingleton.elim (sign.rangeRestrict a) 1)
  let j : A6 →* A6 := f.codRestrict _ hsign
  have hj : Function.Injective j := by
    intro a b hab
    exact hf (congrArg Subtype.val hab)
  let α : MulAut A6 := MulEquiv.ofBijective j ((Nat.bijective_iff_injective_and_card j).mpr ⟨hj,rfl⟩)
  let i : Fin 6 := e (QuotientGroup.mk (1 : A6))
  refine ⟨α,i,eq_of_le_of_card_ge ?_ ?_⟩
  · rintro _ ⟨a,ha,rfl⟩
    apply MulAction.mem_stabilizer_iff.mpr
    change (e.permCongr (MulAction.toPermHom A6 (A6 ⧸ H) a))
      (e (QuotientGroup.mk (1 : A6))) = e (QuotientGroup.mk (1 : A6))
    rw [Equiv.permCongr_apply,e.symm_apply_apply]
    apply congrArg e
    change QuotientGroup.mk a = QuotientGroup.mk (1 : A6)
    exact QuotientGroup.eq.mpr (by simpa using ha)
  · rw [card_map_of_injective (f := α.toMonoidHom) α.injective,hH,
      Nat.card_congr (SmallIndex.pointEquiv (n := 5) i).toEquiv,
      nat_card_alternatingGroup]
    norm_num [Nat.factorial]
end AlternatingSix.FivePointCoordinates
