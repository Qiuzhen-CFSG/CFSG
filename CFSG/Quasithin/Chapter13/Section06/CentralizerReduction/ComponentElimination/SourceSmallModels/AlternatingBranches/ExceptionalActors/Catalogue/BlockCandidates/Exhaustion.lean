module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors.Catalogue.BlockCandidates.Structure

/-!
# Exhausting the cubic-quotient subgroups of the A₇ block stabilizer

The block has exponent twelve, so two-perfectness gives generation by cubics.
Those cubics lie in the even-by-even A₄ × C₃. The common four-group belongs to
any Sylow two-subgroup inside the block. A cubic outside the tail C₃ has all
four-group elements as commutators, forcing that four-group into a normalized
actor. It is then the entire embedded two-core. The cubic quotient gives order
twelve, and a bounded word calculation identifies the literal A₄ candidate.
If no cubic leaves the tail, the quotient order forces the tail itself.

This is the representation-independent calculation behind the exceptional A₇
case of Aschbacher–Smith, combined manuscript of 1 March 2004, Lemma 13.6.22,
printed p.932. All residual and core operations retain their stated prime two.
-/

@[expose] public section
open Subgroup Equiv
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors.Catalogue
local instance : Fintype (Perm (Fin 4)) := fintypePerm
local instance : Fintype (Perm (Fin 3)) := fintypePerm
/-- All three noncyclic candidates lie in the actual block stabilizer. -/
theorem fourActor_le_block (k : Fin 3) : fourActor k ≤ blockStabilizer := by
  fin_cases k
  · rw [show (⟨0, by decide⟩ : Fin 3) = 0 from rfl, fourActor_zero]; exact naturalActor_le_block
  · change fourActor 1 ≤ blockStabilizer
    rw [fourActor_one]; exact diagonalPlus_le_block
  · change fourActor 2 ≤ blockStabilizer
    rw [fourActor_two]; exact diagonalMinus_le_block

theorem commonFour_isPGroup : IsPGroup 2 commonFour := by
  rw [← fourActor_core 0]
  exact pCore_isPGroup.map _

theorem commonFour_le_block : commonFour ≤ blockStabilizer := by
  rw [← fourActor_core 0]
  exact (map_subtype_le _).trans (fourActor_le_block 0)

theorem block_normalizes_commonFour : blockStabilizer ≤ normalizer (commonFour : Set A7) := by
  rw [← fourActor_core 0]
  apply le_normalizer_iff.mpr
  intro g hg x hx
  obtain ⟨y, hy, rfl⟩ := hx
  let f := (fourActor 0).normalizerMonoidHom ⟨g, block_normalizes_fourActor 0 hg⟩
  have hf : f y ∈ pCore 2 (fourActor 0) :=
    characteristic_iff_le_comap.mp inferInstance f hy
  exact ⟨f y, hf, rfl⟩

theorem commonFour_le_sylow (S : Sylow 2 A7) (hS : (S : Subgroup A7) ≤ blockStabilizer) :
    commonFour ≤ S := by
  have hp := S.isPGroup'.to_sup_of_normal_right' commonFour_isPGroup
    (hS.trans block_normalizes_commonFour)
  have he := S.is_maximal' hp le_sup_left
  exact le_sup_right.trans he.le

private theorem block_exponent (p : Perm (Fin 4) × Perm (Fin 3)) :
    AlternatingSeven.ThreeResidualLocals.blockHom p ^ 12 = 1 := by
  rcases p with ⟨p, q⟩
  fin_cases q <;> decide +revert +kernel

theorem block_pow_twelve (g : A7) (hg : g ∈ blockStabilizer) : g ^ 12 = 1 := by
  have hg' : g.val ∈ AlternatingSeven.ThreeResidualLocals.blockHom.range := by
    rw [AlternatingSeven.ThreeResidualLocals.blockHom_range]
    exact hg
  obtain ⟨p, hp⟩ := hg'
  apply Subtype.ext
  change g.val ^ 12 = 1
  rw [← hp]
  exact block_exponent p

/-- Two-perfectness, rather than a three-residual assumption, supplies cubic generation. -/
theorem cubic_generation (D : Subgroup A7) (hD : D ≤ blockStabilizer)
    (hperfect : IsPPerfect 2 D) :
    closure {g : A7 | g ∈ D ∧ g ^ 3 = 1} = D := by
  let K : Subgroup D := closure {g : D | g ^ 3 = 1}
  have hinv (g : D) : K.map (MulAut.conj g).toMonoidHom ≤ K := by
    change (Subgroup.closure _).map _ ≤ Subgroup.closure _
    rw [MonoidHom.map_closure, closure_le]
    rintro _ ⟨x, hx, rfl⟩
    apply Subgroup.subset_closure
    change ((MulAut.conj g) x) ^ 3 = 1
    rw [← map_pow, hx, map_one]
  have hN : K.Normal := ⟨fun n hn g => hinv g ⟨n, hn, rfl⟩⟩
  let := hN
  have hp : IsPGroup 2 (D ⧸ K) := by
    intro q
    obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective K q
    refine ⟨2, ?_⟩
    change (QuotientGroup.mk' K d) ^ 4 = 1
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    apply Subgroup.subset_closure
    change (d ^ 4) ^ 3 = 1
    rw [← pow_mul]
    exact Subtype.ext (block_pow_twelve d (hD d.property))
  have hK := hperfect K hN hp
  have hm := congrArg (fun N : Subgroup D => N.map D.subtype) hK
  change (Subgroup.closure _).map D.subtype = _ at hm
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, range_subtype] at hm
  convert hm using 2
  ext g
  constructor
  · rintro ⟨hg, hc⟩
    exact ⟨⟨g, hg⟩, Subtype.ext hc, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g.property, congrArg Subtype.val hg⟩

/-- The even-by-even subgroup A₄ × C₃ in the chosen block. -/
def expandedActor : Subgroup A7 :=
  AlternatingSeven.ThreeResidualLocals.expandedFour.comap (alternatingGroup (Fin 7)).subtype

theorem twoPerfect_le_expanded (D : Subgroup A7) (hD : D ≤ blockStabilizer)
    (hperfect : IsPPerfect 2 D) : D ≤ expandedActor := by
  rw [← cubic_generation D hD hperfect]
  apply (closure_le _).mpr
  rintro g ⟨hg, h3⟩
  have hg' : g.val ∈ AlternatingSeven.ThreeResidualLocals.blockHom.range := by
    rw [AlternatingSeven.ThreeResidualLocals.blockHom_range]
    exact hD hg
  obtain ⟨p, hp⟩ := hg'
  change g.val ∈ AlternatingSeven.ThreeResidualLocals.expandedFour
  rw [← hp]
  apply AlternatingSeven.ThreeResidualLocals.blockHom_cube_mem_expanded
  have hc : g.val ^ 3 = 1 := congrArg Subtype.val h3
  simpa only [hp] using hc

def coreWord (i : Fin 2 × Fin 2) : A7 :=
  fourFlip ^ i.1.val * (naturalThree * fourFlip * naturalThree⁻¹) ^ i.2.val

theorem coreWord_mem (i : Fin 2 × Fin 2) : coreWord i ∈ commonFour :=
  commonFour.mul_mem (commonFour.pow_mem (subset_closure (by simp)) _)
    (commonFour.pow_mem (subset_closure (by simp)) _)

def expandedActorWord (i : Fin 12 × Fin 3) : A7 := actorWord 0 i.1 * tailThree ^ i.2.val

theorem mem_expandedActor_iff (g : A7) :
    g ∈ expandedActor ↔ ∃ i : Fin 12 × Fin 3, expandedActorWord i = g := by
  change g.val ∈ AlternatingSeven.ThreeResidualLocals.expandedFour ↔ _
  rw [AlternatingSeven.ThreeResidualLocals.mem_expandedFour_iff]
  have he (i : Fin 12 × Fin 3) :
      (expandedActorWord i).val = AlternatingSeven.ThreeResidualLocals.expandedWord i := by
    rcases i with ⟨i, j⟩
    fin_cases i <;> simp [expandedActorWord, actorWord, words,
      AlternatingSeven.ThreeResidualLocals.expandedWord,
      AlternatingSeven.ThreeResidualLocals.words12, naturalThree, fourFlip, tailThree,
      AlternatingSeven.ThreeResidualLocals.tailThree]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, Subtype.ext ((he i).trans hi)⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, (he i).symm⟩

private theorem cubic_commutators (i : Fin 12 × Fin 3)
    (h3 : expandedActorWord i ^ 3 = 1)
    (htail : ∀ j : Fin 3, tailThree ^ j.val ≠ expandedActorWord i) :
    (∃ v : Fin 2 × Fin 2, fourFlip =
      expandedActorWord i * (coreWord v * (expandedActorWord i)⁻¹ * (coreWord v)⁻¹)) ∧
    (∃ v : Fin 2 × Fin 2, naturalThree * fourFlip * naturalThree⁻¹ =
      expandedActorWord i * (coreWord v * (expandedActorWord i)⁻¹ * (coreWord v)⁻¹)) := by
  revert h3 htail
  rcases i with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem commonFour_le_of_cubic (S : Sylow 2 A7) (hS : (S : Subgroup A7) ≤ blockStabilizer)
    (D : Subgroup A7) (hn : (S : Subgroup A7) ≤ normalizer (D : Set A7))
    (g : A7) (hg : g ∈ D) (he : g ∈ expandedActor) (h3 : g ^ 3 = 1)
    (htail : g ∉ cyclicActor) : commonFour ≤ D := by
  obtain ⟨i, rfl⟩ := (mem_expandedActor_iff g).mp he
  have ht : ∀ j : Fin 3, tailThree ^ j.val ≠ expandedActorWord i := by
    intro j hj
    exact htail (hj ▸ npow_mem_zpowers _ _)
  obtain ⟨⟨v, hv⟩, ⟨w, hw⟩⟩ := cubic_commutators i h3 ht
  have hm (v : Fin 2 × Fin 2) :
      expandedActorWord i * (coreWord v * (expandedActorWord i)⁻¹ * (coreWord v)⁻¹) ∈ D :=
    D.mul_mem hg ((hn (commonFour_le_sylow S hS (coreWord_mem v)) _).mp (D.inv_mem hg))
  exact (closure_le _).mpr (by
    rw [Set.pair_subset_iff]
    exact ⟨hv ▸ hm v, hw ▸ hm w⟩)

private theorem coprime_word_in_core (i : Fin 12 × Fin 3)
    (hc : Nat.Coprime (expandedActorWord i).val.cycleType.lcm 3) :
    ∃ v : Fin 2 × Fin 2, coreWord v = expandedActorWord i := by
  decide +revert +kernel

/-- Inside the even-by-even subgroup, every two-core is contained in the common four-group. -/
theorem core_le_commonFour (D : Subgroup A7) (hD : D ≤ expandedActor) :
    (pCore 2 D).map D.subtype ≤ commonFour := by
  rintro _ ⟨d, hd, rfl⟩
  obtain ⟨i, hi⟩ := (mem_expandedActor_iff d).mp (hD d.property)
  have hc := (pCore_isPGroup (p := 2) (G := D)).orderOf_coprime
    (by decide : Nat.Coprime 2 3) (⟨d, hd⟩ : pCore 2 D)
  rw [Subgroup.orderOf_mk, ← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe,
    ← hi, ← Perm.lcm_cycleType] at hc
  obtain ⟨v, hv⟩ := coprime_word_in_core i hc
  change d.val ∈ commonFour
  rw [← hi, ← hv]
  exact coreWord_mem v

theorem core_eq_commonFour (D : Subgroup A7) (hD : D ≤ blockStabilizer)
    (he : D ≤ expandedActor) (hV : commonFour ≤ D) :
    (pCore 2 D).map D.subtype = commonFour := by
  apply le_antisymm (core_le_commonFour D he)
  have hn : (commonFour.subgroupOf D).Normal :=
    (normal_subgroupOf_iff_le_normalizer hV).mpr (hD.trans block_normalizes_commonFour)
  have hp : IsPGroup 2 (commonFour.subgroupOf D) :=
    commonFour_isPGroup.of_equiv (subgroupOfEquivOfLe hV).symm
  have hl : commonFour.subgroupOf D ≤ pCore 2 D := le_sSup ⟨hn, hp⟩
  simpa only [map_subgroupOf_eq_of_le hV] using map_mono (f := D.subtype) hl

private theorem cubic_contains_generator (i : Fin 12 × Fin 3)
    (h3 : expandedActorWord i ^ 3 = 1)
    (htail : ∀ j : Fin 3, tailThree ^ j.val ≠ expandedActorWord i) :
    ∃ k : Fin 3, ∃ r : Fin 3, ∃ v : Fin 2 × Fin 2,
      naturalThree * tailThree ^ k.val = expandedActorWord i ^ r.val * coreWord v := by
  decide +revert +kernel

/-- A cubic element outside the tail, together with the common four-group,
contains one of the three literal A₄ candidates. -/
theorem exists_fourActor_le (D : Subgroup A7) (hV : commonFour ≤ D)
    (g : A7) (hg : g ∈ D) (he : g ∈ expandedActor) (h3 : g ^ 3 = 1)
    (htail : g ∉ cyclicActor) : ∃ k : Fin 3, fourActor k ≤ D := by
  obtain ⟨i, rfl⟩ := (mem_expandedActor_iff g).mp he
  have ht : ∀ j : Fin 3, tailThree ^ j.val ≠ expandedActorWord i := by
    intro j hj
    exact htail (hj ▸ npow_mem_zpowers _ _)
  obtain ⟨k, r, v, hv⟩ := cubic_contains_generator i h3 ht
  refine ⟨k, (closure_le _).mpr ?_⟩
  rw [Set.pair_subset_iff]
  exact ⟨hv ▸ D.mul_mem (D.pow_mem hg r.val) (hV (coreWord_mem v)),
    hV (subset_closure (by simp))⟩

/-- Exhaustion uses the actual Sylow normalizer, two-perfectness and cubic
quotient; it assumes no representation or classification of subgroup families. -/
theorem four_candidates (S : Sylow 2 A7) (hS : (S : Subgroup A7) ≤ blockStabilizer)
    (D : Subgroup A7) (hD : D ≤ blockStabilizer)
    (hn : (S : Subgroup A7) ≤ normalizer (D : Set A7))
    (hp : IsPPerfect 2 D) (hq : Nat.card (D ⧸ pCore 2 D) = 3) :
    D = cyclicActor ∨ D = naturalActor ∨ D = diagonalPlus ∨ D = diagonalMinus := by
  have he := twoPerfect_le_expanded D hD hp
  by_cases ht : D ≤ cyclicActor
  · left
    apply eq_of_le_of_card_ge ht
    rw [cyclicActor_card]
    have hd := (pCore 2 D).card_quotient_dvd_card
    rw [hq] at hd
    exact Nat.le_of_dvd Nat.card_pos hd
  · have hg : ∃ g : A7, g ∈ D ∧ g ^ 3 = 1 ∧ g ∉ cyclicActor := by
      by_contra h
      push Not at h
      apply ht
      rw [← cubic_generation D hD hp]
      exact (closure_le _).mpr (fun g hg => h g hg.1 hg.2)
    obtain ⟨g, hg, h3, htail⟩ := hg
    have hV := commonFour_le_of_cubic S hS D hn g hg (he hg) h3 htail
    have hcore : Nat.card (pCore 2 D) = 4 := by
      rw [← card_map_of_injective D.subtype_injective, core_eq_commonFour D hD he hV,
        commonFour_card]
    have hcard : Nat.card D = 12 := by
      rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 D), hq, hcore]
    obtain ⟨k, hk⟩ := exists_fourActor_le D hV g hg (he hg) h3 htail
    have hd : D = fourActor k := (eq_of_le_of_card_ge hk (by rw [hcard, fourActor_card])).symm
    fin_cases k
    · exact Or.inr (Or.inl (hd.trans fourActor_zero))
    · exact Or.inr (Or.inr (Or.inl (hd.trans fourActor_one)))
    · exact Or.inr (Or.inr (Or.inr (hd.trans fourActor_two)))


end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors.Catalogue
