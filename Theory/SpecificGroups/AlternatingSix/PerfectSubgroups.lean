module
public import Theory.SpecificGroups.AlternatingSix.SmallIndex
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Theory.GroupTheory.PerfectSylowTwo
public import Theory.GroupTheory.SolvableResidual
public import Mathlib.GroupTheory.Nilpotent

/-!
# Perfect subgroups of A₆

Small subgroup indices reduce a proper perfect subgroup to order sixty.
Its index-six coset action places it inside a point stabilizer, producing an
actual isomorphism with A₅. This supplies the degree-four constituent case
in Aschbacher--Smith G.10.15, printed p.363, using the original small actor.
-/

public noncomputable section
open Subgroup
namespace AlternatingSix.PerfectSubgroups
local notation "A6" => alternatingGroup (Fin 6)

private theorem small_index_solvable {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [Group.IsSolvable H] (hi : H.index ≤ 4) : Group.IsSolvable G := by
  classical
  let : Fintype (G ⧸ H) := Fintype.ofFinite _
  have hc : Fintype.card (G ⧸ H) ≤ Fintype.card (Fin 4) := by
    simpa only [index_eq_card, ← Nat.card_eq_fintype_card, Nat.card_fin] using hi
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hc
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm (G ⧸ H)) :=
    Group.isSolvable_of_isSolvable_injective (Equiv.Perm.viaEmbeddingHom_injective e)
  apply Group.isSolvable_of_ker_le_range H.subtype (MulAction.toPermHom G (G ⧸ H))
  rw [range_subtype, ← H.normalCore_eq_ker]
  exact H.normalCore_le

private theorem small_sylow_solvable {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (P : Sylow p G) (hi : (P : Subgroup G).index ≤ 4) :
    Group.IsSolvable G := by
  let : Group.IsNilpotent P := P.isPGroup'.isNilpotent
  exact small_index_solvable P hi

private theorem solvable_le_five {G : Type*} [Group G] [Finite G]
    (hc : Nat.card G ≤ 5) : Group.IsSolvable G := by
  have hp := Nat.card_pos (α := G)
  have hn : Nat.card G=1 ∨ Nat.card G=2 ∨ Nat.card G=3 ∨ Nat.card G=4 ∨ Nat.card G=5 := by omega
  rcases hn with h|h|h|h|h
  · let : Group.IsNilpotent G := (IsPGroup.of_card (p := 2) (n := 0) (by simpa using h)).isNilpotent
    infer_instance
  · let : Group.IsNilpotent G := (IsPGroup.of_card (p := 2) (n := 1) (by simpa using h)).isNilpotent
    infer_instance
  · let : Group.IsNilpotent G := (IsPGroup.of_card (p := 3) (n := 1) (by simpa using h)).isNilpotent
    infer_instance
  · let : Group.IsNilpotent G := (IsPGroup.of_card (p := 2) (n := 2) (by simpa using h)).isNilpotent
    infer_instance
  · let : Fact (Nat.Prime 5) := ⟨by decide⟩
    let : Group.IsNilpotent G := (IsPGroup.of_card (p := 5) (n := 1) (by simpa using h)).isNilpotent
    infer_instance

private theorem solvable_dvd_seventyTwo {G : Type*} [Group G] [Finite G]
    (hd : Nat.card G ∣ 72) (hb : Nat.card G < 72) : Group.IsSolvable G := by
  have hn : Nat.card G=1 ∨ Nat.card G=2 ∨ Nat.card G=3 ∨ Nat.card G=4 ∨
      Nat.card G=6 ∨ Nat.card G=8 ∨ Nat.card G=9 ∨ Nat.card G=12 ∨
      Nat.card G=18 ∨ Nat.card G=24 ∨ Nat.card G=36 := by
    interval_cases hc : Nat.card G <;> omega
  by_cases hs : Nat.card G≤5
  · exact solvable_le_five hs
  rcases hn with h|h|h|h|h|h|h|h|h|h|h
  all_goals try omega
  · let : Fact (Nat.Prime 3) := ⟨by decide⟩
    let P : Sylow 3 G := Classical.choice inferInstance
    apply small_sylow_solvable 3 P
    have hP : Nat.card P=3 := by rw [Sylow.card_eq_multiplicity,h]; decide +kernel
    have hp := (P : Subgroup G).card_mul_index
    rw [hP,h] at hp
    omega
  · let : Group.IsNilpotent G := (IsPGroup.of_card (p := 2) (n := 3) (by simpa using h)).isNilpotent
    infer_instance
  · let : Group.IsNilpotent G := (IsPGroup.of_card (p := 3) (n := 2) (by simpa using h)).isNilpotent
    infer_instance
  · let : Fact (Nat.Prime 3) := ⟨by decide⟩
    let P : Sylow 3 G := Classical.choice inferInstance
    apply small_sylow_solvable 3 P
    have hP : Nat.card P=3 := by rw [Sylow.card_eq_multiplicity,h]; decide +kernel
    have hp := (P : Subgroup G).card_mul_index
    rw [hP,h] at hp
    omega
  · let : Fact (Nat.Prime 3) := ⟨by decide⟩
    let P : Sylow 3 G := Classical.choice inferInstance
    apply small_sylow_solvable 3 P
    have hP : Nat.card P=9 := by rw [Sylow.card_eq_multiplicity,h]; decide +kernel
    have hp := (P : Subgroup G).card_mul_index
    rw [hP,h] at hp
    omega
  · let : Fact (Nat.Prime 2) := ⟨by decide⟩
    let P : Sylow 2 G := Classical.choice inferInstance
    apply small_sylow_solvable 2 P
    have hP : Nat.card P=8 := by rw [Sylow.card_eq_multiplicity,h]; decide +kernel
    have hp := (P : Subgroup G).card_mul_index
    rw [hP,h] at hp
    omega
  · let : Fact (Nat.Prime 3) := ⟨by decide⟩
    let P : Sylow 3 G := Classical.choice inferInstance
    apply small_sylow_solvable 3 P
    have hP : Nat.card P=9 := by rw [Sylow.card_eq_multiplicity,h]; decide +kernel
    have hp := (P : Subgroup G).card_mul_index
    rw [hP,h] at hp
    omega

private theorem card_A6 : Nat.card A6=360 := by
  rw [nat_card_alternatingGroup]
  norm_num [Nat.factorial]

/-- A nontrivial proper perfect subgroup of A6 has index six. -/
theorem index_six (H : Subgroup A6) [Group.IsPerfect H] (hne : H ≠ ⊥) (hproper : H ≠ ⊤) :
    H.index=6 := by
  let : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).mpr hne
  let : IsSimpleGroup A6 := alternatingGroup.isSimpleGroup (by simp)
  have hprod := H.card_mul_index
  rw [card_A6] at hprod
  have hlo : 6 ≤ H.index := by
    by_contra hn
    apply hproper
    apply Atlas.GroupTheory.subgroup_eq_top_of_index_factorial_lt
    have hf := Nat.factorial_le (show H.index≤5 by omega)
    rw [card_A6]
    norm_num [Nat.factorial] at hf ⊢
    omega
  have hb : Nat.card H ≤60 := by nlinarith
  have hi : H.index≤63 := by
    by_contra h
    have hc : Nat.card H≤5 := by nlinarith
    exact Group.IsPerfect.not_isSolvable H (solvable_le_five hc)
  rcases SmallIndex.index_divisible_by_five_or_six_or_thirtySix H hproper hi with h5|h6|h36
  · obtain ⟨k,hk⟩ := h5
    have hd : Nat.card H∣72 := ⟨k,by nlinarith⟩
    exact (Group.IsPerfect.not_isSolvable H (solvable_dvd_seventyTwo hd (by omega))).elim
  · exact h6
  · have hc : Nat.card H=10 := by rw [h36] at hprod; omega
    let : Fact (Nat.Prime 2) := ⟨by decide⟩
    let P : Sylow 2 H := Classical.choice inferInstance
    have hP : Nat.card P=2 := by rw [Sylow.card_eq_multiplicity,hc]; decide +kernel
    have hg := Theory.GroupTheory.perfect_sylow_two_card_gt_two P (hc ▸ (by decide : Even 10))
    omega

/-- The index-six coset action identifies an order-sixty subgroup with A5. -/
theorem equiv_five_of_index_six (H : Subgroup A6) (hi : H.index=6) :
    Nonempty (H ≃* alternatingGroup (Fin 5)) := by
  let : IsSimpleGroup A6 := alternatingGroup.isSimpleGroup (by simp)
  let e : (A6 ⧸ H) ≃ Fin 6 := Finite.equivFinOfCardEq hi
  let f : A6 →* Equiv.Perm (Fin 6) :=
    e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom A6 (A6 ⧸ H))
  have hf : Function.Injective f := by
    apply e.permCongrHom.injective.comp
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [← normalCore_eq_ker]
    rcases (inferInstance : H.normalCore.Normal).eq_bot_or_eq_top with hn|hn
    · exact hn
    · have ht : H=⊤ := top_unique (hn ▸ H.normalCore_le)
      simp only [ht,index_top] at hi
      omega
  let : Group.IsPerfect A6 := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let sign := Equiv.Perm.sign.comp f
  let : Group.IsPerfect sign.range := Group.IsPerfect.range sign
  have hsign (a : A6) : f a∈A6 := by
    apply Equiv.Perm.mem_alternatingGroup.mpr
    exact congrArg Subtype.val (Subsingleton.elim (sign.rangeRestrict a) 1)
  let j : A6 →* A6 := f.codRestrict _ hsign
  let i : Fin 6 := e (QuotientGroup.mk (1 : A6))
  have hj (a : H) : j a ∈ MulAction.stabilizer A6 i := by
    apply MulAction.mem_stabilizer_iff.mpr
    change (e.permCongr (MulAction.toPermHom A6 (A6 ⧸ H) (a : A6))) (e (QuotientGroup.mk (1 : A6))) = e (QuotientGroup.mk (1 : A6))
    rw [Equiv.permCongr_apply, e.symm_apply_apply]
    change e ((a : A6) • QuotientGroup.mk (1 : A6)) = e (QuotientGroup.mk (1 : A6))
    apply congrArg e
    change QuotientGroup.mk (a : A6) = QuotientGroup.mk (1 : A6)
    exact QuotientGroup.eq.mpr (by simp)
  let g : H →* MulAction.stabilizer A6 i :=
    (j.comp H.subtype).codRestrict _ hj
  have hg : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    apply hf
    exact congrArg (fun x : MulAction.stabilizer A6 i => x.val.val) hab
  have hc : Nat.card H=60 := by
    have hp := H.card_mul_index
    rw [hi,card_A6] at hp
    omega
  have hd : Nat.card H=Nat.card (MulAction.stabilizer A6 i) := by
    rw [hc,Nat.card_congr (SmallIndex.pointEquiv (n := 5) i).toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  exact ⟨(MulEquiv.ofBijective g ((Nat.bijective_iff_injective_and_card g).mpr ⟨hg,hd⟩)).trans
    (SmallIndex.pointEquiv (n := 5) i)⟩

/-- Every nontrivial proper perfect subgroup of A6 is an actual A5 carrier. -/
theorem equiv_five (H : Subgroup A6) [Group.IsPerfect H] (hne : H≠⊥) (hproper : H≠⊤) :
    Nonempty (H ≃* alternatingGroup (Fin 5)) :=
  equiv_five_of_index_six H (index_six H hne hproper)

/-- A nontrivial perfect subgroup of S₆ is A₆ or an actual A₅ carrier. -/
theorem symmetric_six (H : Subgroup (Equiv.Perm (Fin 6)))
    [Group.IsPerfect H] (hne : H≠⊥) :
    H=alternatingGroup (Fin 6) ∨ Nonempty (H ≃* alternatingGroup (Fin 5)) := by
  let sign := Equiv.Perm.sign.comp H.subtype
  let : Group.IsPerfect sign.range := Group.IsPerfect.range sign
  have hle : H≤alternatingGroup (Fin 6) := by
    intro a ha
    apply Equiv.Perm.mem_alternatingGroup.mpr
    exact congrArg Subtype.val (Subsingleton.elim (sign.rangeRestrict ⟨a,ha⟩) 1)
  let J := H.subgroupOf (alternatingGroup (Fin 6))
  let e : J ≃* H := subgroupOfEquivOfLe hle
  let : Group.IsPerfect J := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  by_cases ht : J=⊤
  · left
    have hm := map_subgroupOf_eq_of_le hle
    change J.map (alternatingGroup (Fin 6)).subtype=H at hm
    simpa only [ht,← MonoidHom.range_eq_map,range_subtype] using hm.symm
  · right
    have hn : J≠⊥ := by
      intro hz
      have hm := map_subgroupOf_eq_of_le hle
      change J.map (alternatingGroup (Fin 6)).subtype=H at hm
      exact hne (by simpa only [hz,Subgroup.map_bot] using hm.symm)
    obtain ⟨f⟩ := equiv_five J hn ht
    exact ⟨e.symm.trans f⟩

/-- The perfect-subgroup dichotomy respects the literal inclusion in any
specified S₆ overgroup. -/
theorem in_symmetric_six {G : Type*} [Group G]
    (K D : Subgroup G) (e : D ≃* Equiv.Perm (Fin 6))
    [Group.IsPerfect K] (hne : K≠⊥) (hle : K≤D) :
    K=(solvableResidual D).map D.subtype ∨
      Nonempty (K ≃* alternatingGroup (Fin 5)) := by
  let : Finite D := Finite.of_injective e e.injective
  let f := e.toMonoidHom.comp (Subgroup.inclusion hle)
  have hf : Function.Injective f := e.injective.comp (Subgroup.inclusion_injective hle)
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hn : f.range≠⊥ := by
    intro hz
    apply hne
    apply bot_unique
    intro a ha
    apply mem_bot.mpr
    have hh : f ⟨a,ha⟩=1 := mem_bot.mp (hz ▸ (show f ⟨a,ha⟩∈f.range from ⟨⟨a,ha⟩,rfl⟩))
    exact congrArg Subtype.val (hf (hh.trans f.map_one.symm))
  rcases symmetric_six f.range hn with ht|ha
  · left
    have hres : solvableResidual (Equiv.Perm (Fin 6))=alternatingGroup (Fin 6) := by
      let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
        ⟨commutator_alternatingGroup_eq_top (by simp)⟩
      apply le_antisymm
      · exact (solvableResidual_le_derivedSeries 1).trans_eq
          (alternatingGroup.commutator_perm_eq (by simp))
      · exact le_solvableResidual_of_isPerfect _
    have hj : K.subgroupOf D=solvableResidual D := by
      apply map_injective (f := e.toMonoidHom) e.injective
      rw [map_solvableResidual_eq _ e.surjective,hres,← ht]
      ext a
      constructor
      · rintro ⟨b,hb,rfl⟩
        exact ⟨⟨b.val,hb⟩,rfl⟩
      · rintro ⟨b,rfl⟩
        exact ⟨⟨b.val,hle b.property⟩,b.property,rfl⟩
    rw [← hj,map_subgroupOf_eq_of_le hle]
  · right
    obtain ⟨a⟩ := ha
    exact ⟨(MonoidHom.ofInjective hf).trans a⟩

end AlternatingSix.PerfectSubgroups
