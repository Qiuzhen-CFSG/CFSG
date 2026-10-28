module

public import Theory.Representation.BinarySevenCode.WeightTwoCore
public import Theory.SpecificGroups.Alternating.SevenComponent.PointSix
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Weight-six stabilizers and their two-core action

A weight-six binary word has one omitted letter. Its stabilizers in A₇
and S₇ are the literal point stabilizers A₆ and S₆. Any actor fixing this
word and containing the entire A₆ stabilizer has trivial two-core image:
its image has index at most two in S₆, so is normal, and O₂(S₆) is trivial.

The source consumer applies this to C_L(e₆)∞T on the original natural
module to identify its two-core with O₂(LT). No faithfulness of that
ambient action is assumed.

Source: Aschbacher--Smith, 3.3.22, printed p.597, and 12.3.4(3), p.809.
-/

@[expose] public noncomputable section

open Subgroup
open scoped Pointwise
namespace BinarySevenCode.WeightSixGeometry
open WeightTwoGeometry

lemma exists_omitted (w : EvenWord) (hw : weight w.val = 6) :
    ∃ i : Fin 7, (support w)ᶜ = {i} := by
  apply Finset.card_eq_one.mp
  rw [Finset.card_compl]
  change 7 - weight w.val = 1
  rw [hw]

lemma fixes_iff (w : EvenWord) {i : Fin 7} (hi : (support w)ᶜ = {i})
    (g : Equiv.Perm (Fin 7)) : evenRepresentation g w = w ↔ g i = i := by
  have hz (j : Fin 7) : w.val j = 0 ↔ j = i := by
    have h := Finset.ext_iff.mp hi j
    simpa [support] using h
  constructor
  · intro h
    have he := congrArg (fun x : EvenWord => x.val (g i)) h
    simp only [evenRepresentation_apply, Equiv.symm_apply_apply] at he
    exact (hz _).mp (he.symm.trans ((hz i).mpr rfl))
  · intro h
    apply Subtype.ext
    funext j
    change w.val (g.symm j) = w.val j
    apply (by decide : ∀ a b : ZMod 2, (a = 0 ↔ b = 0) → a = b)
    rw [hz, hz, Equiv.symm_apply_eq, h, eq_comm]

lemma stabilizer_eq_point (w : EvenWord) {i : Fin 7} (hi : (support w)ᶜ = {i}) :
    stabilizer w = MulAction.stabilizer (alternatingGroup (Fin 7)) i := by
  ext a
  rw [mem_stabilizer, fixes_iff w hi]
  rfl

lemma symmetricStabilizer_eq_point (w : EvenWord) {i : Fin 7}
    (hi : (support w)ᶜ = {i}) :
    symmetricStabilizer w = MulAction.stabilizer (Equiv.Perm (Fin 7)) i := by
  ext a
  rw [mem_symmetricStabilizer, fixes_iff w hi]
  rfl

noncomputable def sixEquiv (w : EvenWord) (hw : weight w.val = 6) :
    stabilizer w ≃* alternatingGroup (Fin 6) :=
  (MulEquiv.subgroupCongr (stabilizer_eq_point w (Classical.choose_spec (exists_omitted w hw)))).trans
    (AlternatingSix.SmallIndex.pointEquiv _)

lemma stabilizer_perfect (w : EvenWord) (hw : weight w.val = 6) :
    Group.IsPerfect (stabilizer w) := by
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  exact Group.IsPerfect.ofSurjective (f := (sixEquiv w hw).symm.toMonoidHom)
    (sixEquiv w hw).symm.surjective

lemma symmetric_core_eq_bot (w : EvenWord) (hw : weight w.val = 6) :
    pCore 2 (symmetricStabilizer w) = ⊥ := by
  obtain ⟨i,hi⟩ := exists_omitted w hw
  let e := (MulEquiv.subgroupCongr (symmetricStabilizer_eq_point w hi)).trans
    (alternatingGroup.SevenComponent.symmetricPointEquiv i)
  apply (map_eq_bot_iff_of_injective (f := e.toMonoidHom) _ e.injective).mp
  rw [pCore_map_iso, alternatingGroup.SevenComponent.symmetric_six_twoCore]

lemma twoCore_maps_trivially {H : Type*} [Group H] (w : EvenWord)
    (hw : weight w.val = 6) (f : H →* symmetricStabilizer w)
    (hf : ∀ a : stabilizer w, ∃ h : H, (f h).val = a.val.val)
    (q : pCore 2 H) : f q = 1 := by
  let A := stabilizer w
  let D := symmetricStabilizer w
  let j : A →* D := {
    toFun a := ⟨a.val.val, (mem_symmetricStabilizer _ _).mpr
      ((mem_stabilizer _ _).mp a.property)⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hj : Function.Injective j := by
    intro a b h
    exact Subtype.ext (Subtype.ext (congrArg (fun x : D => x.val) h))
  have hA : Nat.card j.range = 360 := by
    rw [Nat.card_congr (MonoidHom.ofInjective hj).toEquiv.symm,
      Nat.card_congr (sixEquiv w hw).toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hD : Nat.card D = 720 := by
    obtain ⟨i,hi⟩ := exists_omitted w hw
    let e := (MulEquiv.subgroupCongr (symmetricStabilizer_eq_point w hi)).trans
      (alternatingGroup.SevenComponent.symmetricPointEquiv i)
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    rfl
  have hi : j.range.index = 2 := by
    have h := j.range.card_mul_index
    rw [hA,hD] at h
    omega
  have hle : j.range ≤ f.range := by
    rintro _ ⟨a,rfl⟩
    obtain ⟨h,hh⟩ := hf a
    exact ⟨h,Subtype.ext hh⟩
  have hn : f.range.Normal := by
    rcases (Nat.dvd_prime Nat.prime_two).mp (hi ▸ index_dvd_of_le hle) with h | h
    · rw [index_eq_one.mp h]
      infer_instance
    · exact normal_of_index_eq_two h
  have hz : pCore 2 f.range = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 hn.isSubnormal, symmetric_core_eq_bot w hw,
      MonoidHom.comap_bot]
    exact f.range.subtype.ker_eq_bot_iff.mpr f.range.subtype_injective
  have hmap : (pCore 2 H).map f.rangeRestrict ≤ pCore 2 f.range :=
    le_sSup ⟨(inferInstance : (pCore 2 H).Normal).map _ f.rangeRestrict_surjective,
      pCore_isPGroup.map _⟩
  have hq := hmap (mem_map_of_mem _ q.property)
  rw [hz] at hq
  exact congrArg Subtype.val (show f.rangeRestrict q = 1 from hq)
end BinarySevenCode.WeightSixGeometry
