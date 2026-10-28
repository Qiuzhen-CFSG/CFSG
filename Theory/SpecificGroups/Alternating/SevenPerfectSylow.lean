module
public import Theory.SpecificGroups.AlternatingSix.PerfectSubgroups
public import Theory.SpecificGroups.Alternating.SevenComponent.PointSix
public import Theory.GroupTheory.Commutator.PerfectSmallIndex
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
public import Mathlib.GroupTheory.Perm.Closure
public import Theory.SpecificGroups.SymmetricSix.Parabolics
public import Theory.Order.UniqueMaximalOver

/-!
# Perfect Sylow-normalized subgroups in the full seven-letter action

A seven-cycle and a transposition generate S₇. Thus a proper nontrivial
perfect subgroup normalized by a full Sylow two-subgroup of S₇ has no
seven-element. Its small orbits are fixed, so it fixes a letter and the
A₆ perfect-subgroup theorem gives A₅ or the whole point stabilizer A₆.
In the latter case its Sylow join is S₆, whose two distinct Sylow
parabolics exclude a unique maximal Sylow overgroup.

This is the finite recognition step for the proper A₇ overcomponent in
Aschbacher–Smith 12.2.7(2), printed p.797, used in 12.3.12, p.811.
The application in TerminalComponentProperSeven retains the original
central cover and its marked action.
-/

public section
open Subgroup Equiv MulAction
namespace Theory.SpecificGroups.Alternating.SevenPerfectSylow
local notation "S7" => Perm (Fin 7)
local notation "A7" => alternatingGroup (Fin 7)

theorem sylow_contains_swap (S : Sylow 2 S7) : ∃ a ∈ (S : Subgroup S7), a.IsSwap := by
  have hp : IsPGroup 2 (zpowers (swap (0 : Fin 7) 1)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, (Perm.isCycle_swap (by decide)).orderOf]; decide)
  obtain ⟨U,hU⟩ := hp.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq S7 U S
  refine ⟨g * swap 0 1 * g⁻¹, ?_, ?_⟩
  · rw [←hg]
    change g * swap 0 1 * g⁻¹ ∈ (U : Subgroup S7).map (MulAut.conj g).toMonoidHom
    exact mem_map_of_mem _ (hU (mem_zpowers _))
  · rw [mul_swap_eq_swap_mul, mul_inv_cancel_right]
    exact ⟨g 0,g 1,g.injective.ne (by decide),rfl⟩

theorem seven_not_dvd (B : Subgroup S7) [Group.IsPerfect B]
    (hne : B ≠ ⊥) (hproper : B ≠ A7)
    (S : Sylow 2 S7) (hSB : (S : Subgroup S7) ≤ normalizer (B : Set S7)) :
    ¬ 7 ∣ Nat.card B := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  intro hd
  obtain ⟨b,hb⟩ := exists_prime_orderOf_dvd_card' (G := B) 7 hd
  have hb' : orderOf (b : S7) = 7 := (orderOf_coe b).trans hb
  have hc : (b : S7).IsCycle := Perm.isCycle_of_prime_order'' (by decide) hb'
  have hsupp : (b : S7).support = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [← hc.orderOf,hb']
    rfl
  obtain ⟨a,ha,has⟩ := sylow_contains_swap S
  have hn : normalizer (B : Set S7) = ⊤ := by
    apply top_unique
    rw [← Perm.closure_prime_cycle_swap (by decide) hc hsupp has,closure_le]
    exact Set.insert_subset_iff.mpr ⟨B.le_normalizer b.property,
      Set.singleton_subset_iff.mpr (hSB ha)⟩
  let : B.Normal := normalizer_eq_top_iff.mp hn
  let : Nontrivial B := (nontrivial_iff_ne_bot B).mpr hne
  apply hproper
  exact le_antisymm (le_of_isPerfect_of_index_eq_two B A7 (alternatingGroup.index_eq_two))
    (Perm.alternatingGroup_le_of_normal (by simp) inferInstance)

private theorem fixed_of_small_orbit (B : Subgroup S7) [Group.IsPerfect B]
    (i : Fin 7) (hi : (orbit B i).ncard ≤ 4) : i ∈ fixedPoints B (Fin 7) := by
  have ht : stabilizer B i = ⊤ := top_unique
    (le_of_isPerfect_of_index_le_four ⊤ _ (by rwa [index_stabilizer]))
  intro b
  exact (show b ∈ stabilizer B i from ht ▸ mem_top b)

theorem exists_fixed (B : Subgroup S7) [Group.IsPerfect B]
    (h7 : ¬ 7 ∣ Nat.card B) : ∃ i : Fin 7, i ∈ fixedPoints B (Fin 7) := by
  classical
  have hb (i : Fin 7) : (orbit B i).ncard ≤ 6 := by
    have hle : (orbit B i).ncard ≤ 7 := by
      simpa using Set.ncard_le_ncard (Set.subset_univ (orbit B i))
    have hn : (orbit B i).ncard ≠ 7 := by
      intro he
      apply h7
      rw [←index_stabilizer] at he
      have hh := (stabilizer B i).index_dvd_card
      rwa [he] at hh
    omega
  by_cases hsmall : (orbit B (0 : Fin 7)).ncard ≤ 4
  · exact ⟨0,fixed_of_small_orbit B 0 hsmall⟩
  have hout : ∃ j : Fin 7, j ∉ orbit B (0 : Fin 7) := by
    by_contra! h
    have he : orbit B (0 : Fin 7) = Set.univ := Set.eq_univ_of_forall h
    have hh := hb 0
    rw [he,Set.ncard_univ,Nat.card_fin] at hh
    omega
  obtain ⟨j,hj⟩ := hout
  have hd : Disjoint (orbit B (0 : Fin 7)) (orbit B j) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    have he := (orbit_eq_iff.mpr hx).symm.trans (orbit_eq_iff.mpr hy)
    exact hj (he ▸ mem_orbit_self j)
  have hsum : (orbit B (0 : Fin 7)).ncard + (orbit B j).ncard ≤ 7 := by
    rw [← Set.ncard_union_eq hd]
    simpa using Set.ncard_le_ncard (Set.subset_univ (orbit B (0 : Fin 7) ∪ orbit B j))
  exact ⟨j,fixed_of_small_orbit B j (by omega)⟩

theorem five_or_point_six (B : Subgroup A7) [Group.IsPerfect B]
    (hne : B ≠ ⊥) (hproper : B ≠ ⊤)
    (S : Sylow 2 S7)
    (hSB : (S : Subgroup S7) ≤ normalizer (B.map (alternatingGroup (Fin 7)).subtype : Set S7)) :
    Nonempty (B ≃* alternatingGroup (Fin 5)) ∨
      ∃ i : Fin 7, B = stabilizer A7 i := by
  let C := B.map (alternatingGroup (Fin 7)).subtype
  let e : B ≃* C := B.equivMapOfInjective (alternatingGroup (Fin 7)).subtype (alternatingGroup (Fin 7)).subtype_injective
  let : Group.IsPerfect C := Group.IsPerfect.map _
  have hn : C ≠ ⊥ := by
    intro he
    have hh := congrArg (comap (alternatingGroup (Fin 7)).subtype) he
    rw [comap_map_eq_self_of_injective (alternatingGroup (Fin 7)).subtype_injective,MonoidHom.comap_bot] at hh
    exact hne (hh.trans (alternatingGroup (Fin 7)).ker_subtype)
  have hp : C ≠ A7 := by
    intro he
    have hh := congrArg (comap (alternatingGroup (Fin 7)).subtype) he
    rw [comap_map_eq_self_of_injective (alternatingGroup (Fin 7)).subtype_injective] at hh
    exact hproper (hh.trans (subgroupOf_self A7))
  obtain ⟨i,hi⟩ := exists_fixed C (seven_not_dvd C hn hp S hSB)
  let A := stabilizer A7 i
  have hBA : B ≤ A := by
    intro b hb
    exact hi (e ⟨b,hb⟩)
  let D := B.subgroupOf A
  let d : D ≃* B := subgroupOfEquivOfLe hBA
  let f := AlternatingSix.SmallIndex.pointEquiv i
  let E := D.map f.toMonoidHom
  let c : D ≃* E := D.equivMapOfInjective f.toMonoidHom f.injective
  let : Group.IsPerfect D := Group.IsPerfect.ofSurjective (f := d.symm.toMonoidHom) d.symm.surjective
  let : Group.IsPerfect E := Group.IsPerfect.map _
  by_cases ht : E = ⊤
  · right
    refine ⟨i,le_antisymm hBA ?_⟩
    have hD : D = ⊤ := by
      apply map_injective (f := f.toMonoidHom) f.injective
      rw [map_top_of_surjective _ f.surjective]
      exact ht
    exact subgroupOf_eq_top.mp hD
  · left
    have he : E ≠ ⊥ := by
      intro he
      have hs : Subsingleton E := by rw [he]; infer_instance
      let := hs
      have hsD : Subsingleton D := c.injective.subsingleton
      let := hsD
      have hsB : Subsingleton B := d.symm.injective.subsingleton
      let := hsB
      exact hne B.eq_bot_of_subsingleton
    obtain ⟨q⟩ := AlternatingSix.PerfectSubgroups.equiv_five E he ht
    exact ⟨d.symm.trans (c.trans q)⟩

private theorem point_fixed (i : Fin 7) :
    fixedPoints (stabilizer A7 i) (Fin 7) = {i} := by
  have := alternatingGroup.isMultiplyPretransitive (Fin 7)
  have ht : IsMultiplyPretransitive A7 (Fin 7) 2 :=
    isMultiplyPretransitive_of_le (n := Nat.card (Fin 7) - 2) (by simp) (Nat.sub_le _ _)
  ext j
  constructor
  · intro hj
    by_contra hij
    have hji : j ≠ i := fun h => hij (Set.mem_singleton_iff.mpr h)
    obtain ⟨k,hki,hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by decide)
    obtain ⟨g,hgi,hgj⟩ := is_two_pretransitive_iff.mp ht hji.symm hki.symm
    have he := hj (⟨g,hgi⟩ : stabilizer A7 i)
    exact hkj (hgj.symm.trans he)
  · rintro rfl
    intro g
    exact g.property

private theorem normalizer_point_le (i : Fin 7) :
    normalizer ((stabilizer A7 i).map (alternatingGroup (Fin 7)).subtype : Set S7) ≤
      stabilizer S7 i := by
  let B := (stabilizer A7 i).map (alternatingGroup (Fin 7)).subtype
  intro g hg
  have hf : g i ∈ fixedPoints (stabilizer A7 i) (Fin 7) := by
    intro b
    have hb : g⁻¹ * b.val.val * g ∈ B :=
      (mem_normalizer_iff''.mp hg b.val.val).mp (mem_map_of_mem _ b.property)
    obtain ⟨c,hc,he⟩ := hb
    have hh : (g⁻¹ * b.val.val * g) i = i := he ▸ hc
    have hh' := congrArg g hh
    change b.val.val (g i) = g i
    change g (g.symm (b.val.val (g i))) = g i at hh'
    simpa only [apply_symm_apply] using hh'
  exact Set.mem_singleton_iff.mp (point_fixed i ▸ hf)

theorem symmetric_six_not_unique (S : Sylow 2 (Perm (Fin 6))) :
    ¬ Order.HasUniqueMaximalOver (S : Subgroup (Perm (Fin 6))) ⊤ := by
  intro hu
  obtain ⟨g,_,hg⟩ := Theory.SpecificGroups.SymmetricSix.coatoms_over_sylow S
  let e := (MulAut.conj g).mapSubgroup
  have hp := (hg (e Theory.SpecificGroups.SymmetricSix.duadStabilizer)).mpr (Or.inl rfl)
  have hq := (hg (e Theory.SpecificGroups.SymmetricSix.synthemeStabilizer)).mpr (Or.inr rfl)
  exact Theory.SpecificGroups.SymmetricSix.parabolics_ne (e.injective
    (hu.2.unique ⟨hp.2,hp.1.covBy_top⟩ ⟨hq.2,hq.1.covBy_top⟩))

/-- A perfect proper subgroup in the seven-letter alternating group, normalized
by a full symmetric Sylow, is A₅ when its Sylow join has a unique maximal
Sylow overgroup. The excluded A₆ branch has the two ordinary S₆ parabolics. -/
theorem five_of_uniqueMaximal (B : Subgroup A7) [Group.IsPerfect B]
    (hne : B ≠ ⊥) (hproper : B ≠ ⊤)
    (S : Sylow 2 S7)
    (hSB : (S : Subgroup S7) ≤ normalizer (B.map (alternatingGroup (Fin 7)).subtype : Set S7))
    (hu : Order.HasUniqueMaximalOver
      ((S : Subgroup S7).subgroupOf (B.map (alternatingGroup (Fin 7)).subtype ⊔ (S : Subgroup S7))) ⊤) :
    Nonempty (B ≃* alternatingGroup (Fin 5)) := by
  rcases five_or_point_six B hne hproper S hSB with he | ⟨i,rfl⟩
  · exact he
  let C := (stabilizer A7 i).map (alternatingGroup (Fin 7)).subtype
  let J := C ⊔ (S : Subgroup S7)
  let A := stabilizer S7 i
  have hJA : J ≤ A :=
    (sup_le C.le_normalizer hSB).trans (normalizer_point_le i)
  have hc : Nat.card C = 360 := by
    rw [card_map_of_injective (alternatingGroup (Fin 7)).subtype_injective,
      Nat.card_congr (AlternatingSix.SmallIndex.pointEquiv i).toEquiv,
      nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hs : Nat.card S = 16 := by
    rw [Sylow.card_eq_multiplicity,Nat.card_perm,Nat.card_fin]
    decide +kernel
  have ha : Nat.card A = 720 := by
    rw [Nat.card_congr (alternatingGroup.SevenComponent.symmetricPointEquiv i).toEquiv,
      Nat.card_perm,Nat.card_fin]
    rfl
  have hdC : 360 ∣ Nat.card J := hc ▸ card_dvd_of_le (show C ≤ J from le_sup_left)
  have hdS : 16 ∣ Nat.card J := hs ▸ card_dvd_of_le (show (S : Subgroup S7) ≤ J from le_sup_right)
  have hj : J = A := eq_of_le_of_card_ge hJA (by
    have hp := Nat.card_pos (α := J)
    have hb := Nat.card_le_card_of_injective (inclusion hJA) (inclusion_injective hJA)
    rw [ha] at hb ⊢
    omega)
  let e : J ≃* Perm (Fin 6) := (MulEquiv.subgroupCongr hj).trans
    (alternatingGroup.SevenComponent.symmetricPointEquiv i)
  let U := (S.subtype (show (S : Subgroup S7) ≤ J from le_sup_right)).mapSurjective (f := e.toMonoidHom) e.surjective
  apply False.elim
  apply symmetric_six_not_unique U
  have hh := hu.map e.mapSubgroup
  change Order.HasUniqueMaximalOver
    (((S : Subgroup S7).subgroupOf J).map e.toMonoidHom)
    ((⊤ : Subgroup J).map e.toMonoidHom) at hh
  rw [map_top_of_surjective _ e.surjective] at hh
  exact hh
end Theory.SpecificGroups.Alternating.SevenPerfectSylow
