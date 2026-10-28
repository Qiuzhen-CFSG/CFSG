module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveImages
public import Theory.SpecificGroups.SU3.MovedTwoGroups
public import BenderSuzuki.External.Huppert.II.theorem_10_13
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Theory.GroupTheory.PerfectSmallTwoAction
public import Theory.GroupTheory.PGroup.MutualNormalizerCommutator
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.Representation.SU3.BinaryDegree.ProjectiveOrder

/-!
# The original radical supplies the unitary involution witness

The full movement identity R₂* = [R₂*,Y*] makes the two-group R₂* inner.
In the PSU₃(5) quotient the projected K₂ is perfect with an A₅ quotient.
The group order bounds its two-core by four, so perfectness makes that
core central. Mutual normalization then makes K₂ centralize the inner
implementers of R₂*. Its nontrivial action supplies an involution and an
order-five subgroup of the original projected K₂ centralizing it.

This is the local placement input for the Sylow-center argument in
Aschbacher--Smith, original 4.3.2, printed p.618, using 4.3.11--15.
The independent four-chief-factor bound is consumed by the final index
contradiction; it is not an extra assumption of this placement theorem.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}

omit [Finite G] in
/-- The literal R₂ action is inner in the prime-five unitary branch. -/
theorem unitaryFive_radical_action_inner (s : SecondaryData c n)
    (hunitary : ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 5) :
    SecondaryData.radicalImage s ≤ MulAut.innerSubgroup (s.component ⧸ pCore 2 s.component) := by
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
    ((SecondaryData.radicalImage s).map k.toMonoidHom)
    ((SecondaryData.torusImage s).map k.toMonoidHom)
    ((SecondaryData.radicalImage_two s).1.map k.toMonoidHom)
    (by rw [← map_commutator, SecondaryData.radicalImage_moved s])
  intro a ha
  have ht := hm (mem_map_of_mem k.toMonoidHom ha)
  rw [← MulAut.map_innerSubgroup_congr e] at ht
  obtain ⟨b, hb, he⟩ := ht
  exact k.injective he ▸ hb

omit [Finite G] in
private theorem quotient_center_eq_bot (s : SecondaryData c n)
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
theorem unitaryFive_radical_involution (s : SecondaryData c n)
    (hunitary : ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 5) :
    ∃ x : s.component ⧸ pCore 2 s.component, orderOf x = 2 ∧
      MulAut.conj x ∈ SecondaryData.radicalImage s := by
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
  have hinj : Function.Injective (MulAut.conj : E →* MulAut E) :=
    Theory.GroupTheory.conj_injective_of_center_eq_bot hz
  let A := SecondaryData.radicalImage s
  let : Nontrivial A := A.nontrivial_iff_ne_bot.mpr (SecondaryData.radicalImage_two s).2
  obtain ⟨m, hm, hcard⟩ := (SecondaryData.radicalImage_two s).1.nontrivial_iff_card.mp
    (inferInstance : Nontrivial A)
  have hd : 2 ∣ Nat.card A := by
    rw [hcard]
    exact dvd_pow_self 2 (by omega)
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := A) 2 hd
  obtain ⟨x, hx⟩ := unitaryFive_radical_action_inner s hunitary a.property
  refine ⟨x, ?_, hx.symm ▸ a.property⟩
  rw [← orderOf_injective (MulAut.conj : E →* MulAut E) hinj x, hx,
    Subgroup.orderOf_coe, ha]

omit [Finite G] in
private theorem quotient_card (s : SecondaryData c n)
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

private theorem projection_core_central (s : SecondaryData c 2)
    (hm : ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 5) :
    pCore 2 (SecondaryData.secondaryProjection s).range ≤
      center (SecondaryData.secondaryProjection s).range := by
  let B := (SecondaryData.secondaryProjection s).range
  let := SecondaryData.secondaryProjection_perfect s
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := SecondaryData.secondaryProjection_model s
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
theorem unitaryFive_secondary_centralizes_inner_radical (s : SecondaryData c 2)
    (hm : ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 5)
    (hz : center (s.component ⧸ pCore 2 s.component) = ⊥) :
    (SecondaryData.secondaryProjection s).range ≤
      centralizer ((SecondaryData.radicalImage s).comap MulAut.conj : Set _) := by
  let E := s.component ⧸ pCore 2 s.component
  let f : E →* MulAut E := MulAut.conj
  have hi : Function.Injective f := Theory.GroupTheory.conj_injective_of_center_eq_bot hz
  let A := SecondaryData.radicalImage s
  let B := (SecondaryData.secondaryProjection s).range
  let R := A.comap f
  have hB : B.map f = SecondaryData.secondaryImage s :=
    (SecondaryData.secondary_action_image s).symm
  have hpre : (SecondaryData.secondaryImage s).comap f = B := by
    rw [← hB, comap_map_eq, (MonoidHom.ker_eq_bot_iff f).mpr hi, sup_bot_eq]
  have hn1 : B ≤ normalizer (R : Set E) :=
    ((map_le_iff_le_comap.mp (hB ▸ (SecondaryData.image_normalization s).1))).trans
      (A.le_normalizer_comap f)
  have hn2 : R ≤ normalizer (B : Set E) := by
    rw [← hpre]
    exact (comap_mono (SecondaryData.image_normalization s).2.1).trans
      ((SecondaryData.secondaryImage s).le_normalizer_comap f)
  have hp : IsPGroup 2 R := (SecondaryData.radicalImage_two s).1.comap_of_injective f hi
  let := SecondaryData.secondaryProjection_perfect s
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
theorem unitaryFive_quotient_involution_witness (s : SecondaryData c 2)
    (hm : ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 5) :
    ∃ X : Subgroup (s.component ⧸ pCore 2 s.component), Nat.card X = 5 ∧
      X ≤ (SecondaryData.secondaryProjection s).range ∧
      ∃ t : s.component ⧸ pCore 2 s.component, orderOf t = 2 ∧
        X ≤ centralizer ({t} : Set _) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let B := (SecondaryData.secondaryProjection s).range
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := SecondaryData.secondaryProjection_model s
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
  obtain ⟨t, ht, hta⟩ := unitaryFive_radical_involution s hm
  refine ⟨X, ?_, hXB, t, ht, ?_⟩
  · rw [card_map_of_injective B.subtype_injective, Nat.card_zpowers, hx]
  · intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (unitaryFive_secondary_centralizes_inner_radical s hm (quotient_center_eq_bot s hm)
        (hXB hx) t hta).symm

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
