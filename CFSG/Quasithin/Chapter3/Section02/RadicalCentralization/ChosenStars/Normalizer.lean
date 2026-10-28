module
public import CFSG.Quasithin.Chapter3.Section02.RadicalCentralization.ChosenStars.Escape
public import CFSG.Quasithin.Chapter3.Section02.RadicalCentralization.ChosenStars.Parameters
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Thompson
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Thompson.Application.Source.Complete
/-!
# Normalizer control with several odd Fitting primes

Solvable Thompson factorization produces a nontrivial characteristic
subgroup C of R = O₂(Ξ_p(L)T) whose normalizer residual contains both
Ξ_p(L) and Ξ_q(L). An escaping ambient normalizer would have a normal
containing component of type (S)L₃(p) and (S)L₃(q), contradicting p ≠ q.
Thus N_G(C) and N_G(R) lie in N_G(L). The single-prime source argument
supplies the other case.

This is the N_G(R) step of the source characteristic-normalizer proof.
Control of every characteristic subgroup remains separate, as in the
Signalizers modules; no universal A.3.12 premise is used.
Source: Aschbacher--Smith, proof of 1.3.8, printed p.513.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter3.RadicalCentralization.ChosenStars
open Chapter1 Chapter1.Section02 Chapter1.RadicalNormalizers Chapter1.RadicalActions
open Chapter1.RadicalNormalizers.Embedding Chapter1.XiEmbedding Chapter1.RadicalExclusions
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Two distinct canonical radicals in the actual characteristic residual
force its full ambient normalizer into N_G(L). -/
theorem characteristic_normalizer_le_of_two_radicals
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : Odd p) (hq : Odd q) (hpq : p ≠ q)
    (hdp : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (hdq : q ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (C : Subgroup (radicalCore p L T)) [C.Characteristic] (hC : C ≠ ⊥)
    (hqC : XiP q L ≤ normalizerResidual L (C.map (radicalCore p L T).subtype)) :
    normalizer (C.map (radicalCore p L T).subtype : Set G) ≤ normalizer (L : Set G) := by
  by_contra he
  let h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun A _ _ => ChapterA.Section02.theoremA_knownSimple (G := A))
    (fun A _ _ => ChapterA.Section02.theoremC_knownSimple (G := A))
  have h38 : ∀ (A : Type u) [Group A] [Finite A],
      IsSQTK KnownSimple.IsKnownSimple A → pCore 2 A = ⊥ → ∀ B : Subgroup A,
      B.IsCComponent → B.Normal ∨ IsQuasisimple B :=
    fun _ _ _ hA hO _ hB => ChapterA.Section03.NoncentralNormality.normal_or_quasisimple hA hO hB
  have hQ := uniqueness_local_quotient_sqtk hG hL.1.2.2
  have hr := residual_normalizer_data_of_source h36 h38 hL hQ hn hp hdp
  obtain ⟨K,hK,hYK,hKn,_⟩ := exists_normal_component_source hG T hL hn hp hdp C hC
  have hLC := residual_le_component L _ K C hK.1 hKn hYK
    (hr.characteristic_local C inferInstance hC).2.2
  have hTN := (t_le_normalizer_radicalCore p L T).trans
    (normalizer_le_normalizer_characteristic_image _ C)
  have hN := characteristic_normalizer_isTwoLocal p L T C hC
  have hm := escaping_component_linearThree hG T hL hn hp hdp hN hTN hK hKn
    (hr.X_le_Y.trans hYK) he
  have hmq := escaping_component_linearThree hG T hL hn hq hdq hN hTN hK hKn
    (hqC.trans hLC) he
  exact hpq (linearThree_prime_eq Fact.out Fact.out
    (XiP_oddQuotient_of_A36 h36 hL.1 hQ hn hp hdp).1
    (XiP_oddQuotient_of_A36 h36 hL.1 hQ hn hq hdq).1 hm hmq)

/-- The genuine Thompson factorization constructs a controlled nontrivial
characteristic subgroup; no embedding-list callback remains. -/
theorem exists_controlled_thompsonChoice
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : Odd p) (hq : Odd q) (hpq : p ≠ q)
    (hdp : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (hdq : q ∣ Nat.card (fittingSubgroup (XiQuotient L))) :
    ∃ C : Subgroup (radicalCore p L T), IsThompsonChoice (radicalCore p L T) C ∧
      C ≠ ⊥ ∧ C.Characteristic ∧
      normalizer (C.map (radicalCore p L T).subtype : Set G) ≤ normalizer (L : Set G) := by
  let h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun A _ _ => ChapterA.Section02.theoremA_knownSimple (G := A))
    (fun A _ _ => ChapterA.Section02.theoremC_knownSimple (G := A))
  have h38 : ∀ (A : Type u) [Group A] [Finite A],
      IsSQTK KnownSimple.IsKnownSimple A → pCore 2 A = ⊥ → ∀ B : Subgroup A,
      B.IsCComponent → B.Normal ∨ IsQuasisimple B :=
    fun _ _ _ hA hO _ hB => ChapterA.Section03.NoncentralNormality.normal_or_quasisimple hA hO hB
  have hQ := uniqueness_local_quotient_sqtk hG hL.1.2.2
  have hr := residual_normalizer_data_of_source h36 h38 hL hQ hn hp hdp
  have hq3 := (XiP_oddQuotient_of_A36 h36 hL.1 hQ hn hq hdq).1
  have hq5 : 5 ≤ q := by obtain ⟨a,ha⟩ := hq; omega
  obtain ⟨C,hC,hne,hchar,_,_,hqC,_,_⟩ :=
    exists_thompsonChoice_fittingPrimes_of_B216 ThompsonSource.source_theoremB216
      p q hp hq hq5 L T hL.1 hr.t_normalizes
      (lemma_1_1_4_6 T (hG.evenCharacteristic T)) hdp hdq hr.X_le_Y
      (hr.actions q Fact.out hq hdq).2 (hr.actions q Fact.out hq hdq).1
  let := hchar
  exact ⟨C,hC,hne,hchar,
    characteristic_normalizer_le_of_two_radicals hG T hL hn hp hq hpq hdp hdq C hne hqC⟩

/-- The full normalizer of the canonical two-core lies in N_G(L), for
arbitrary odd-prime support of the actual Fitting quotient. -/
theorem radicalCore_normalizer_le
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L))) :
    normalizer (radicalCore p L T : Set G) ≤ normalizer (L : Set G) := by
  classical
  by_cases hs : ∀ q : ℕ, q.Prime → Odd q →
      q ∣ Nat.card (fittingSubgroup (XiQuotient L)) → q = p
  · let hA := fun (A : Type u) [Group A] [Finite A] =>
      ChapterA.Section02.theoremA_knownSimple (G := A)
    let hC := fun (A : Type u) [Group A] [Finite A] =>
      ChapterA.Section02.theoremC_knownSimple (G := A)
    let h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC hA hC
    have h38 : ∀ (A : Type u) [Group A] [Finite A],
        IsSQTK KnownSimple.IsKnownSimple A → pCore 2 A = ⊥ → ∀ B : Subgroup A,
        B.IsCComponent → B.Normal ∨ IsQuasisimple B :=
      fun _ _ _ hA hO _ hB => ChapterA.Section03.NoncentralNormality.normal_or_quasisimple hA hO hB
    have h127 : ∀ K ∈ LStar G (T : Subgroup G),
        IsMaximalTwoLocal (normalizer (componentOrbit K (T : Subgroup G) : Set G)) ∧
        ∀ M : Subgroup G, IsMaximalTwoLocal M → K ⊔ (T : Subgroup G) ≤ M →
          M = normalizer (componentOrbit K (T : Subgroup G) : Set G) := by
      intro K hK
      have hh := nonsolvable_uniqueness_of_theoremsAC hA hC hG T hK
      exact ⟨hh.normalizer_maximal,hh.normalizer_unique⟩
    have hc := (radical_singlePrime_normalizers_of_source h36 h38 h127 hL
      (uniqueness_local_quotient_sqtk hG hL.1.2.2) hn hp hd hs).2
    have hh := (characteristicNormalizerClosure_le_iff _ _).mp hc
      ⊤ inferInstance (by
        let : Nontrivial (radicalCore p L T) :=
          (nontrivial_iff_ne_bot _).mpr (radicalCore_ne_bot p hL.1)
        exact top_ne_bot)
    simpa only [←MonoidHom.range_eq_map,range_subtype] using hh
  · push Not at hs
    obtain ⟨q,hq,hqo,hqd,hqp⟩ := hs
    let : Fact q.Prime := ⟨hq⟩
    obtain ⟨C,_,hne,hchar,hcontrol⟩ :=
      exists_controlled_thompsonChoice hG T hL hn hp hqo (Ne.symm hqp) hd hqd
    let := hchar
    exact (normalizer_le_normalizer_characteristic_image _ C).trans hcontrol

end CFSG.Quasithin.Chapter3.RadicalCentralization.ChosenStars
