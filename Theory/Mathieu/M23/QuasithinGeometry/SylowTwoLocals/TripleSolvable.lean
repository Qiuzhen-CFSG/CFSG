module

public import Theory.Mathieu.M23.QuasithinGeometry.SylowTwoLocals.TripleSolvable.PointComparison
public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.PairQuotients
public import Mathlib.GroupTheory.IsPerfect

/-!
# Solvable normal subgroups of the native M₂₃ triple stabilizer

Intersect a solvable normal subgroup with the stabilizer of one of the three
points. The actual M₂₂ pair-stabilizer comparison and its surjection onto S₅
force this intersection into the kernel of order 16: a nontrivial normal
subgroup of S₅ contains the nonsolvable A₅. The intersection has index at most
three in the original subgroup, by its action on the triple. Hence the
original subgroup cannot have order divisible by nine.

Normality throughout is relative to the triple stabilizer, and then to its
point stabilizer; ambient normality in M₂₃ is not required.

Source: GLS3, Table 5.3d, printed p.265; Aschbacher--Smith, the local
inspection in 15.3.41--42, printed p.1138.
-/

public section
open Subgroup
open scoped Pointwise
namespace Sporadic.Mathieu.M23Geometry.SylowTwoLocals.TripleSolvable
open M22ValueBound.Concrete

private theorem first_normal_solvable_card_dvd (N : Subgroup first) [N.Normal]
    [Group.IsSolvable N] : Nat.card N ∣ 16 := by
  let R := N.map pairAction
  let : R.Normal := (inferInstance : N.Normal).map pairAction pairAction_surjective
  let : Group.IsSolvable R :=
    Group.isSolvable_of_surjective (pairAction.subgroupMap_surjective N)
  have hR : R = ⊥ := by
    by_contra h
    let : Nontrivial R := (nontrivial_iff_ne_bot _).mpr h
    have hA := Equiv.Perm.alternatingGroup_le_of_normal
      (by simp : 5 ≤ Nat.card (Fin 5)) (inferInstance : Nontrivial R)
    let : Group.IsSolvable (alternatingGroup (Fin 5)) :=
      Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion hA) (Subgroup.inclusion_injective hA)
    let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5)) inferInstance
  have hN : N ≤ pairAction.ker := (Subgroup.map_eq_bot_iff N).mp hR
  simpa only [pairAction_ker_card] using card_dvd_of_le hN

private noncomputable def intersectionEquiv (D : Subgroup markedStabilizer) :
    MulAction.stabilizer D (9 : Fin 23) ≃* D.subgroupOf markedPointStabilizer where
  toFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  invFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  map_mul' _ _ := rfl

private theorem marked_normal_solvable_not_nine (D : Subgroup markedStabilizer)
    [D.Normal] [Group.IsSolvable D] : ¬ 9 ∣ Nat.card D := by
  let K := MulAction.stabilizer D (9 : Fin 23)
  let N := D.subgroupOf markedPointStabilizer
  let : Group.IsSolvable N := Group.isSolvable_of_surjective
    (f := (intersectionEquiv D).toMonoidHom) (intersectionEquiv D).surjective
  let e := firstEquivMarkedPoint.symm
  let R := N.map e.toMonoidHom
  let : R.Normal := (inferInstance : N.Normal).map e.toMonoidHom e.surjective
  let : Group.IsSolvable R := Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective N)
  have hc : Nat.card K ∣ 16 := by
    have h := first_normal_solvable_card_dvd R
    rw [card_map_of_injective e.injective] at h
    rwa [Nat.card_congr (intersectionEquiv D).toEquiv]
  have hi : K.index ≤ 3 := by
    rw [MulAction.index_stabilizer]
    have ho : MulAction.orbit D (9 : Fin 23) ⊆ (markedTriple : Set (Fin 23)) := by
      intro x hx
      obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hx
      have hm : (9 : Fin 23) ∈ markedTriple := by
        simp [m22M23AugmentedBlock]
      have h := Finset.smul_mem_smul_finset (a := g.val.val) hm
      rwa [show g.val.val • markedTriple = markedTriple from g.val.property] at h
    have h := Set.ncard_le_ncard ho
    have ht : markedTriple.card = 3 := by decide +kernel
    simpa only [Set.ncard_coe_finset, ht] using h
  have hpos : 0 < K.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  intro h9
  have hdiv : 9 ∣ 16 * K.index := by
    apply h9.trans
    rw [← K.card_mul_index]
    exact Nat.mul_dvd_mul hc (dvd_refl _)
  have hsmall : K.index = 1 ∨ K.index = 2 ∨ K.index = 3 := by omega
  rcases hsmall with h | h | h <;> rw [h] at hdiv <;> norm_num at hdiv

end TripleSolvable

/-- A solvable subgroup normal inside the literal triple stabilizer has order
not divisible by nine. -/
theorem triple_normal_solvable_not_nine
    (D : Subgroup tripleStabilizer) [D.Normal] [Group.IsSolvable D] :
    ¬ 9 ∣ Nat.card D := by
  obtain ⟨g, hg⟩ := TripleSolvable.exists_triple_transport
  let e : tripleStabilizer ≃* TripleSolvable.markedStabilizer :=
    MulAction.stabilizerEquivStabilizer hg.symm
  let N := D.map e.toMonoidHom
  let : N.Normal := (inferInstance : D.Normal).map e.toMonoidHom e.surjective
  let : Group.IsSolvable N := Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective D)
  have h := TripleSolvable.marked_normal_solvable_not_nine N
  rwa [card_map_of_injective e.injective] at h

end Sporadic.Mathieu.M23Geometry.SylowTwoLocals
