module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveSourceGeometry
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondarySourceGeometry
public import Theory.SpecificGroups.SU3.MovedTwoGroups
public import BenderSuzuki.External.Huppert.II.theorem_10_13
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Theory.GroupTheory.PerfectSmallTwoAction
public import Theory.GroupTheory.PGroup.MutualNormalizerCommutator
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.Representation.SU3.BinaryDegree.ProjectiveOrder

/-!
# Unitary root geometry from moved-core generation

Only Q is moved by the torus. Its literal action image is therefore inner
in PSU₃(5); generation by Q and the radical-secondary commutators puts the
whole radical image inside the inner group. The projected secondary group
has central two-core of order at most four, so perfectness and mutual
normalization make it centralize the inner radical. Its order-five subgroup
is thus centralized by an actual quotient involution.

This repairs the inner-action step of the legacy marking without assuming
whole-radical torus movement. The ambient generation premise is discharged
by the original natural-action calculation in the source marking consumer.
Source: Aschbacher--Smith, original 4.3.11--16 and the unitary endgame,
printed pp.617--618.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceEndgame
open EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}

/-- The original core action is inner using only its genuine torus movement. -/
theorem unitaryFive_core_action_inner (s : SecondarySourceData c n)
    (hunitary : ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 5) :
    ((Q c).subgroupOf (rootNormalizer c)).map s.action ≤ MulAut.innerSubgroup (s.component ⧸ pCore 2 s.component) := by
  obtain ⟨F, _, _, J, hF, hc, ⟨e⟩⟩ := hunitary
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hfixed : Nat.card {x : F // J.conj x = x} = 5 := by
    simpa only [pow_one] using FiniteField.card_fixed_of_quadratic_frobenius
      J.conj 5 1 (by decide) (by simpa only [pow_one] using hF)
      (by simpa only [pow_one] using hc)
  let : IsSimpleGroup (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
    BenderSuzuki.External.huppert_II_10_13 J 5 (by decide) hF hfixed
  let k := MulAut.congr e
  have hm := BenderSuzuki.MatrixGroups.HermitianForm.PrimeTwoActors.moved_twoGroup_le_inner_of_prime
    J (by decide : Nat.Prime 5) (by decide : Odd 5) hF hfixed
    ((((Q c).subgroupOf (rootNormalizer c)).map s.action).map k.toMonoidHom)
    (((s.torus.subgroupOf (rootNormalizer c)).map s.action).map k.toMonoidHom)
    ((((isPGroup_pCoreIn 2 (secondary c ⊔ S c)).to_le (core_le_radical c)).comap_subtype.map s.action).map k.toMonoidHom)
    (by rw [← map_commutator, s.core_action_moved])
  intro a ha
  have ht := hm (mem_map_of_mem k.toMonoidHom ha)
  rw [← MulAut.map_innerSubgroup_congr e] at ht
  obtain ⟨b, hb, he⟩ := ht
  exact k.injective he ▸ hb

/-- Generation puts every element of the literal radical image inside the
inner group; no movement of R₂ by the torus is used. -/
theorem unitaryFive_radical_action_inner (s : SecondarySourceData c n)
    (hunitary : ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 5)
    (hgen : Q c ⊔ ⁅R₂ c, secondary c⁆ = R₂ c) :
    ((R₂ c).subgroupOf (rootNormalizer c)).map s.action ≤
      MulAut.innerSubgroup (s.component ⧸ pCore 2 s.component) := by
  let := s.normal
  rw [← s.action_generation_of_generation hgen]
  exact sup_le (unitaryFive_core_action_inner s hunitary)
    ((commutator_mono le_rfl (SourceImages.secondary_inner c s.component s.secondary_le)).trans
      (commutator_le_right _ _))

omit [Finite G] in
private theorem quotient_center_eq_bot (s : SecondarySourceData c n)
    (hunitary : ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 5) :
    center (s.component ⧸ pCore 2 s.component) = ⊥ := by
  let E := s.component ⧸ pCore 2 s.component
  have hsimple : IsSimpleGroup E := by
    obtain ⟨F, _, _, J, hF, hc, ⟨e⟩⟩ := hunitary
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    have hfixed : Nat.card {x : F // J.conj x = x} = 5 := by
      simpa only [pow_one] using FiniteField.card_fixed_of_quadratic_frobenius
        J.conj 5 1 (by decide) (by simpa only [pow_one] using hF)
        (by simpa only [pow_one] using hc)
    let := BenderSuzuki.External.huppert_II_10_13 J 5 (by decide) hF hfixed
    exact e.isSimpleGroup
  let := hsimple
  let : IsQuasisimple E := s.quasisimple
  have hz : center E = ⊥ := by
    rcases (inferInstance : (center E).Normal).eq_bot_or_eq_top with hz | hz
    · exact hz
    · exact (Group.IsPerfect.not_isMulCommutative E (center_eq_top_iff.mp hz)).elim
  exact hz

/-- A quotient involution implements an element of the original radical action. -/
theorem unitaryFive_radical_involution (s : SecondarySourceData c n)
    (hunitary : ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 5)
    (hgen : Q c ⊔ ⁅R₂ c, secondary c⁆ = R₂ c) :
    ∃ x : s.component ⧸ pCore 2 s.component, orderOf x = 2 ∧
      MulAut.conj x ∈ ((R₂ c).subgroupOf (rootNormalizer c)).map s.action := by
  let E := s.component ⧸ pCore 2 s.component
  have hz : center E = ⊥ := quotient_center_eq_bot s hunitary
  have hinj : Function.Injective (MulAut.conj : E →* MulAut E) :=
    Theory.GroupTheory.conj_injective_of_center_eq_bot hz
  let A := ((R₂ c).subgroupOf (rootNormalizer c)).map s.action
  let : Nontrivial A := A.nontrivial_iff_ne_bot.mpr s.radical_action
  have hA : IsPGroup 2 A :=
    ((isPGroup_pCoreIn 2 (secondary c ⊔ S c)).comap_subtype).map s.action
  obtain ⟨m, hm, hcard⟩ := hA.nontrivial_iff_card.mp (inferInstance : Nontrivial A)
  have hd : 2 ∣ Nat.card A := by
    rw [hcard]
    exact dvd_pow_self 2 (by omega)
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := A) 2 hd
  obtain ⟨x, hx⟩ := unitaryFive_radical_action_inner s hunitary hgen a.property
  refine ⟨x, ?_, hx.symm ▸ a.property⟩
  rw [← orderOf_injective (MulAut.conj : E →* MulAut E) hinj x, hx,
    Subgroup.orderOf_coe, ha]

omit [Finite G] in
private theorem quotient_card (s : SecondarySourceData c n)
    (hm : ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 5) :
    Nat.card (s.component ⧸ pCore 2 s.component) = 126000 := by
  obtain ⟨F, _, _, J, hF, hc, ⟨e⟩⟩ := hm
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hf : Nat.card {x : F // J.conj x = x} = 5 := by
    simpa only [pow_one] using FiniteField.card_fixed_of_quadratic_frobenius
      J.conj 5 1 (by decide) (by simpa only [pow_one] using hF)
      (by simpa only [pow_one] using hc)
  rw [Nat.card_congr e.toEquiv, Representation.SU3.BinaryDegree.card_projective J hF hf]
  norm_num

private theorem projection_core_central (s : SecondarySourceData c 2)
    (hm : ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 5) :
    pCore 2 (SourceImages.secondaryProjection c s.component s.secondary_le).range ≤
      center (SourceImages.secondaryProjection c s.component s.secondary_le).range := by
  let B := (SourceImages.secondaryProjection c s.component s.secondary_le).range
  let := SourceImages.secondaryProjection_perfect c s.component s.secondary_le
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := SourceImages.secondaryProjection_model c s.component s.secondary_le s.secondary_model
  obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (show Nat.card F = 4 from hF)
  have hquot : Nat.card (B ⧸ pCore 2 B) = 60 := by
    rw [Nat.card_congr (e.trans a).toEquiv, nat_card_alternatingGroup]
    norm_num
  have hmul := card_eq_card_quotient_mul_card_subgroup (pCore 2 B)
  rw [hquot] at hmul
  obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 2) (G := B)).exists_card_eq
  have hd : 60 * 2 ^ k ∣ 126000 := by
    rw [← hk, ← hmul, ← quotient_card s hm]
    exact B.card_subgroup_dvd_card
  have hk3 : k < 3 := by
    by_contra h
    have hd8 : 2 ^ 3 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
    have hbad : 480 ∣ 126000 := (Nat.mul_dvd_mul_left 60 hd8).trans hd
    norm_num at hbad
  have hsmall : Nat.card (pCore 2 B) ≤ 4 := by
    rw [hk]
    exact Nat.pow_le_pow_right (by decide) (by omega : k ≤ 2)
  have hcentral := le_centralizer_of_isPerfect_of_card_le_four
    (⊤ : Subgroup B) (pCore 2 B) hsmall
  intro x hx
  exact mem_center_iff.mpr fun y => (hcentral (mem_top y) x hx).symm

/-- Mutual normalization and the small central two-core make the actual
secondary quotient image centralize every inner implementer of R₂. -/
theorem unitaryFive_secondary_centralizes_inner_radical (s : SecondarySourceData c 2)
    (hm : ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 5)
    (hz : center (s.component ⧸ pCore 2 s.component) = ⊥) :
    (SourceImages.secondaryProjection c s.component s.secondary_le).range ≤
      centralizer ((((R₂ c).subgroupOf (rootNormalizer c)).map s.action).comap MulAut.conj : Set _) := by
  let := s.normal
  let E := s.component ⧸ pCore 2 s.component
  let f : E →* MulAut E := MulAut.conj
  have hi : Function.Injective f := Theory.GroupTheory.conj_injective_of_center_eq_bot hz
  let A := ((R₂ c).subgroupOf (rootNormalizer c)).map s.action
  let B := (SourceImages.secondaryProjection c s.component s.secondary_le).range
  let R := A.comap f
  have hB : B.map f = ((secondary c).subgroupOf (rootNormalizer c)).map s.action :=
    (SourceImages.secondary_action_image c s.component s.secondary_le).symm
  have hpre : (((secondary c).subgroupOf (rootNormalizer c)).map s.action).comap f = B := by
    rw [← hB, comap_map_eq, (MonoidHom.ker_eq_bot_iff f).mpr hi, sup_bot_eq]
  have hn1 : B ≤ normalizer (R : Set E) :=
    ((map_le_iff_le_comap.mp (hB ▸ (SourceImages.radical_geometry c s.component s.radical_normalizer).2.2.2.1))).trans
      (A.le_normalizer_comap f)
  have hn2 : R ≤ normalizer (B : Set E) := by
    rw [← hpre]
    exact (comap_mono (SourceImages.radical_geometry c s.component s.radical_normalizer).2.2.2.2).trans
      ((((secondary c).subgroupOf (rootNormalizer c)).map s.action).le_normalizer_comap f)
  have hp : IsPGroup 2 R := (((isPGroup_pCoreIn 2 (secondary c ⊔ S c)).comap_subtype).map s.action).comap_of_injective f hi
  let := SourceImages.secondaryProjection_perfect c s.component s.secondary_le
  have hcomm : ⁅B, R⁆ ≤ (pCore 2 B).map B.subtype :=
    commutator_le_pCore_of_mutual_normalization B R hp hn1 hn2
  have hcentral : (pCore 2 B).map B.subtype ≤ centralizer (B : Set E) := by
    rintro _ ⟨z, hz', rfl⟩ b hb
    exact congrArg Subtype.val (mem_center_iff.mp (projection_core_central s hm hz') ⟨b, hb⟩)
  apply commutator_eq_bot_iff_le_centralizer.mp
  rw [commutator_comm]
  apply commutator_eq_bot_of_iterated_eq_bot
  apply commutator_eq_bot_iff_le_centralizer.mpr
  rw [commutator_comm]
  exact hcomm.trans hcentral

/-- The original secondary image contains a quintic subgroup centralized by
an actual quotient involution supplied by the nontrivial R₂ action. -/
theorem unitaryFive_quotient_involution_witness (s : SecondarySourceData c 2)
    (hm : ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 5)
    (hgen : Q c ⊔ ⁅R₂ c, secondary c⁆ = R₂ c) :
    ∃ X : Subgroup (s.component ⧸ pCore 2 s.component), Nat.card X = 5 ∧
      X ≤ (SourceImages.secondaryProjection c s.component s.secondary_le).range ∧
      ∃ t : s.component ⧸ pCore 2 s.component, orderOf t = 2 ∧
        X ≤ centralizer ({t} : Set _) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let B := (SourceImages.secondaryProjection c s.component s.secondary_le).range
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := SourceImages.secondaryProjection_model c s.component s.secondary_le s.secondary_model
  obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (show Nat.card F = 4 from hF)
  have hcard : Nat.card (B ⧸ pCore 2 B) = 60 := by
    rw [Nat.card_congr (e.trans a).toEquiv, nat_card_alternatingGroup]
    norm_num
  have hd : 5 ∣ Nat.card B :=
    (show 5 ∣ Nat.card (B ⧸ pCore 2 B) by rw [hcard]; decide).trans
      (card_dvd_of_surjective (QuotientGroup.mk' (pCore 2 B))
        (QuotientGroup.mk'_surjective _))
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := B) 5 hd
  let X := (zpowers x).map B.subtype
  have hXB : X ≤ B := map_subtype_le _
  obtain ⟨t, ht, hta⟩ := unitaryFive_radical_involution s hm hgen
  refine ⟨X, ?_, hXB, t, ht, ?_⟩
  · rw [card_map_of_injective B.subtype_injective, Nat.card_zpowers, hx]
  · intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (unitaryFive_secondary_centralizes_inner_radical s hm (quotient_center_eq_bot s hm)
        (hXB hx) t hta).symm

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceEndgame
