module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.InitialModels
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Linear
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Lifting.Transport
public import Theory.SpecificGroups.PSL2.PrimeSylowMaximal
public import Theory.SpecificGroups.SL2.OddProjectiveNonsolvable
public import Theory.SpecificGroups.SL2.PrimeFiveEquiv
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Parameter restrictions in the rank-one paragraph of 15.3.37

A proper Sylow-two overgroup whose order is divisible by three forces an
even exponent in PSL₂(2ⁿ): its Borel has order 2ⁿ(2ⁿ − 1).
For PSL₂(p) with p a Fermat or Mersenne prime, the large-parameter Sylow
maximality theorem excludes p > 7; nonsolvability excludes p ≤ 3.
The two surviving primes are transported through the actual exceptional
isomorphisms PSL₂(5) ≃ PSL₂(4) and PSL₂(7) ≃ PSL₃(2).

The arithmetic congruence also treats the unitary exponent. The opposite-sign
linear rank-three restriction and innerness require additional arguments.
Source: Aschbacher--Smith, combined manuscript (1 March 2004), the rank-one
paragraph of 15.3.37, printed p.1135. The imported order-seven comparison
carries its ATLAS source attribution and license in its owning module.
-/

@[expose] public section

open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.RankOneAction

theorem even_iff_two_pow_mod_three (n : ℕ) : Even n ↔ 2 ^ n % 3 = 1 := by
  have h (n : ℕ) : 2 ^ n % 3 = if n % 2 = 0 then 1 else 2 := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rcases (show n % 2 = 0 ∨ n % 2 = 1 by omega) with hn | hn
      · simp [pow_succ, Nat.mul_mod, ih, hn, Nat.add_mod]
      · simp [pow_succ, Nat.mul_mod, ih, hn, Nat.add_mod]
  rw [h, Nat.even_iff]
  split_ifs <;> simp_all

private theorem binary_borel_card (F : Type*) [Field F] [Finite F] [CharP F 2] :
    Nat.card (BenderSuzuki.Converse.PBorel F) = Nat.card F * (Nat.card F - 1) := by
  let := BenderSuzuki.Converse.PUnip_normal_in_PBorel (F := F)
  open BenderSuzuki.Converse in
  rw [← PUnip_sup_PTorus, card_sup_eq_mul_of_normalizes_of_disjoint _ _
    (PTorus_le_PBorel.trans (le_normalizer_of_normal_subgroupOf PUnip_le_PBorel))
    PUnip_disjoint_PTorus, PUnip_card, PTorus_card, Nat.card_units]

private theorem binary_normalizer_card (F : Type*) [Field F] [Finite F]
    [CharP F 2] (P : Sylow 2 PSL(2, F)) :
    Nat.card (normalizer (P : Set PSL(2, F))) = Nat.card F * (Nat.card F - 1) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq PSL(2, F)
    (ChapterF.Source.Linear.projectiveSylow F) P
  have he : (normalizer (ChapterF.Source.Linear.projectiveSylow F : Set PSL(2, F))).map
      (MulAut.conj g).toMonoidHom = normalizer (P : Set PSL(2, F)) := by
    change (normalizer ((ChapterF.Source.Linear.projectiveSylow F :
      Subgroup PSL(2, F)) : Set PSL(2, F))).map (MulAut.conj g).toMonoidHom = _
    rw [Subgroup.map_equiv_normalizer_eq]
    congr 1
    rw [← hg]
    rfl
  rw [← he, ← Nat.card_congr (Subgroup.equivMapOfInjective _ _
    (MulAut.conj g).injective).toEquiv, ChapterF.Source.Linear.projectiveSylow_normalizer,
    binary_borel_card]

variable {H : Type*} [Group H] [Finite H]

theorem binary_exponent_even {n : ℕ} (hn : 0 < n)
    (hm : ClassicalGroup.IsPSL H 2 (2 ^ n))
    (P : Sylow 2 H) (D : Subgroup H) (hPD : (P : Subgroup H) ≤ D)
    (hD : D < ⊤) (h3 : 3 ∣ Nat.card D) : Even n := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hDQ : D.map e.toMonoidHom ≤ normalizer (Q : Set PSL(2, F)) := by
    apply (ChapterF.Source.rankOneSylowFacts_psl2 F n hn hF Q).unique_maximal
    · exact map_mono hPD
    · apply lt_top_iff_ne_top.mpr
      intro he
      apply hD.ne
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      simpa only [Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] using he
  have h3' : 3 ∣ Nat.card (normalizer (Q : Set PSL(2, F))) := by
    apply dvd_trans _ (card_dvd_of_le hDQ)
    rwa [← Nat.card_congr (D.equivMapOfInjective e.toMonoidHom e.injective).toEquiv]
  rw [binary_normalizer_card, hF] at h3'
  have hd : 3 ∣ 2 ^ n - 1 := (Nat.Prime.dvd_mul Nat.prime_three).mp h3' |>.resolve_left
    (fun hh => (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hh))
  apply (even_iff_two_pow_mod_three n).mpr
  have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hr := Nat.mod_eq_zero_of_dvd hd
  omega

private theorem large_fermatMersenne_adjacent_power {p : ℕ}
    (hp : IsFermatOrMersennePrime p) (hbig : 7 < p) :
    ∃ k : ℕ, 4 ≤ k ∧ (p - 1 = 2 ^ k ∨ p + 1 = 2 ^ k) := by
  rcases hp.2 with ⟨a, ha⟩ | ⟨a, ha⟩
  · have ha2 : 2 ≤ a := by
      by_contra! h
      interval_cases a <;> norm_num at ha <;> omega
    refine ⟨2 ^ a, ?_, Or.inl (by omega)⟩
    exact (show 2 ^ 2 ≤ 2 ^ a from Nat.pow_le_pow_right (by omega) ha2)
  · have ha4 : 4 ≤ a := by
      by_contra! h
      interval_cases a <;> norm_num at ha <;> omega
    exact ⟨a, ha4, Or.inr ha⟩

private theorem prime_field_equiv {F : Type*} [Field F] [Finite F]
    {p : ℕ} (hp : p.Prime) (hF : Nat.card F = p) :
    let : Fact p.Prime := ⟨hp⟩
    Nonempty (F ≃+* ZMod p) := by
  let : Fact p.Prime := ⟨hp⟩
  let := Fintype.ofFinite F
  exact ⟨(ZMod.ringEquivOfPrime F hp
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm⟩

theorem fermatMersenne_parameter {p : ℕ} (hp : IsFermatOrMersennePrime p)
    (hm : ClassicalGroup.IsPSL H 2 p) (hns : ¬ Group.IsSolvable H)
    (P : Sylow 2 H) (D : Subgroup H) (hPD : (P : Subgroup H) ≤ D)
    (hD : D < ⊤) (h3 : 3 ∣ Nat.card D) : p = 5 ∨ p = 7 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  have hp2 : p ≠ 2 := by
    rintro rfl
    rcases hp.2 with ⟨a, ha⟩ | ⟨a, ha⟩
    · have hlow : 2 ≤ 2 ^ (2 ^ a) := Nat.le_pow (by norm_num)
      omega
    · have hd : 2 ∣ 2 ^ a := dvd_pow_self _ (by
        rintro rfl
        norm_num at ha)
      omega
  have hgt : 3 < p := hF ▸ Matrix.ProjectiveSpecialLinearGroup.card_gt_three_of_odd_of_not_isSolvable
    (hF ▸ hp.1.odd_of_ne_two hp2) (by
      intro hs
      let := hs
      exact hns (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective))
  have hle : p ≤ 7 := by
    by_contra! hbig
    let : Fact p.Prime := ⟨hp.1⟩
    obtain ⟨f⟩ := prime_field_equiv hp.1 hF
    let E : H ≃* PSL(2, ZMod p) := e.trans (Atlas.fieldEquivPSL 2 f)
    obtain ⟨k, hk, hpk⟩ := large_fermatMersenne_adjacent_power hp hbig
    have hmax : IsCoatom (P : Subgroup H) := by
      apply (OrderIso.isCoatom_iff E.mapSubgroup (P : Subgroup H)).mp
      exact Matrix.ProjectiveSpecialLinearGroup.sylow_two_isCoatom_of_adjacent_power
        hk hpk (P.mapSurjective (f := E.toMonoidHom) E.surjective)
    have he := (hmax.le_iff_eq hD.ne).mp hPD
    have hd : 3 ∣ Nat.card P := he ▸ h3
    obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
    rw [hk] at hd
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
  obtain ⟨a, ha⟩ := hp.1.odd_of_ne_two hp2
  omega

omit [Finite H] in
theorem rankOneModel_of_prime_five (hm : ClassicalGroup.IsPSL H 2 5) : RankOneModel H := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  obtain ⟨f⟩ := prime_field_equiv (by decide : Nat.Prime 5) hF
  obtain ⟨g⟩ := Matrix.ProjectiveSpecialLinearGroup.five_equiv_four
  refine Or.inl ⟨2, by decide, by decide, GaloisField 2 2, inferInstance, inferInstance, ?_,
    ⟨(e.trans (Atlas.fieldEquivPSL 2 f)).trans g⟩⟩
  exact GaloisField.card 2 2 (by decide)

omit [Finite H] in
theorem rankOneModel_of_prime_seven (hm : ClassicalGroup.IsPSL H 2 7) : RankOneModel H := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  obtain ⟨f⟩ := prime_field_equiv (by decide : Nat.Prime 7) hF
  refine Or.inr (Or.inr ⟨ZMod 2, inferInstance, inferInstance, by simp,
    ⟨(e.trans (Atlas.fieldEquivPSL 2 f)).trans
      Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two⟩⟩)

end CFSG.Quasithin.Chapter15.Section03.Candidates.RankOneAction
