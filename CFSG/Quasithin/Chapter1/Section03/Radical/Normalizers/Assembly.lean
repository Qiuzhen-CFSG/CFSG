module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Parabolic
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.MultiplePrimeStructure
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Residual
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Thompson
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness

/-!
# Characteristic-normalizer control for the radical family

For R = O₂(Ξ_p(L)T), the single-prime case follows from the coprime omega
normalizer argument with its structural premises discharged. With two odd
Fitting primes, solvable Thompson factorization gives a nontrivial
characteristic subgroup C₀ whose normalizer residual has both primes.
The escaping-normalizer embedding theorem would force that residual to
have only the odd Fitting prime five, so N_G(R) ≤ N_G(C₀) ≤ N_G(L).

For any remaining escaping characteristic normalizer, the actual marked
five-kernel in its containing component K kills the image of R in
KR/O₂(KR). Together with the reverse core bound this gives R = O₂(KR).
Thus K ≤ N_G(R) ≤ N_G(L) ≤ N_G(Ξ_p(L)), contradicting the proved
nonnormality of Ξ_p(L) in K. This proves the source's C(G,R) bound.

Only universal earlier A.3.6, the two used clauses of A.3.8, A.3.12,
B.2.16 and 1.2.7(3) remain parameters. The local characteristic-two,
residual, action, factorization, relative-normality and marked-model
premises are all discharged. The final wrapper uses the source radical
identification to cover every member of Ξ*_rad.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Proposition 1.3.8, printed pp.512–513, claim (*).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers
open Section02 Section02.LocalModels
open CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding
open CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.FiveCase
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The characteristic-normalizer bound in the proof of Proposition 1.3.8.
Only universal earlier source results are parameters. All construction-specific
residual, action, factorization, marked-model and normality premises are proved. -/
theorem characteristicNormalizerClosure_le_of_source
    {𝒦 : GroupClass.{u}} (hG : IsSimpleQTKE 𝒦 G)
    (hA36 : ∀ (A : Type u) [Group A] [Finite A],
      IsSQTK 𝒦 A → pCore 2 A = ⊥ → ∀ B : Subgroup A,
      B.IsCComponent → A36Conclusion B)
    (hA38q : ∀ (A : Type u) [Group A] [Finite A],
      IsSQTK 𝒦 A → pCore 2 A = ⊥ → ∀ B : Subgroup A,
      B.IsCComponent → B.Normal ∨ IsQuasisimple B)
    (hA38 : ∀ (A : Type u) [Group A] [Finite A],
      IsSQTK 𝒦 A → pCore 2 A = ⊥ → ∀ B : Subgroup A, B.IsCComponent →
      B.Normal ∨ (normalizer (B : Set A)).index = 2 ∧ NonnormalCComponentModel B)
    (hA312 : ∀ (A : Type u) [Group A] [Finite A],
      IsSQTK 𝒦 A → pCore 2 A = ⊥ → ∀ (S : Sylow 2 A) (B : Subgroup A),
      B ∈ ChapterA.Section03.localCComponents S → A312Conclusion B)
    (hB216 : ThompsonSource.TheoremB216.{u})
    (T : Sylow 2 G)
    (h127 : ∀ K ∈ LStar G (T : Subgroup G),
      IsMaximalTwoLocal (normalizer (componentOrbit K (T : Subgroup G) : Set G)) ∧
        ∀ M : Subgroup G, IsMaximalTwoLocal M → K ⊔ T ≤ M →
          M = normalizer (componentOrbit K (T : Subgroup G) : Set G))
    {L : Subgroup G} (hL : L ∈ LStar G T)
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L))) :
    characteristicNormalizerClosure (radicalCore p L T) ≤ normalizer (L : Set G) := by
  classical
  have hQall : ∀ K ∈ Chapter1.L G (T : Subgroup G),
      IsSQTK 𝒦 ((K ⊔ T : Subgroup G) ⧸ pCore 2 (K ⊔ T : Subgroup G)) := by
    intro K hK
    exact uniqueness_local_quotient_sqtk hG hK.2.2
  have hQ := hQall L hL.1
  have hTL := radicalLocal_invariant_of_A38 hA38q hL.1 hQ hn
  have hunique := (radical_normalizer_maximal_of_127 h127 hL hTL).2
  by_cases hs : ∀ q : ℕ, q.Prime → Odd q →
      q ∣ Nat.card (fittingSubgroup (XiQuotient L)) → q = p
  · exact (radical_singlePrime_normalizers_of_source hA36 hA38q h127 hL hQ hn hp hd hs).2
  push Not at hs
  obtain ⟨q, hq, hqo, hqd, hqp⟩ := hs
  let _ : Fact q.Prime := ⟨hq⟩
  have hnil := nilpotent_of_two_fitting_primes hA36 hL.1 hQ hn Fact.out hq hqp hd hqd
  have hfive : IsSL (fittingQuotient L) 2 5 := by
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hnil.2.2.1
    exact ⟨F, inferInstance, inferInstance, hF,
      ⟨(QuotientGroup.quotientMulEquivOfEq hnil.1).symm.trans e⟩⟩
  obtain ⟨hp3, hshape⟩ := XiP_oddQuotient_of_A36 hA36 hL.1 hQ hn hp hd
  have hq3 : 3 < q := (XiP_oddQuotient_of_A36 (p := q) hA36 hL.1 hQ hn hqo hqd).1
  have hq5 : 5 ≤ q := by
    obtain ⟨k, hk⟩ := hqo
    omega
  have hX : XiMember T (XiP p L) :=
    lemma_1_3_3 hA36 hA38q hQall ⟨L, hL.1, hn, p, Fact.out, hp, hd, rfl⟩
  have hlocal := lemma_1_1_4_6 T (hG.evenCharacteristic T)
  have hcore := XiP_pCoreIn_ne_bot (Fact.out : p.Prime) hL.1 hTL hshape
    (fun _ hM _ hne hNM hsub => lemma_1_1_3_1 hM hne hNM hsub) hlocal
  have hres := residual_normalizer_data_of_source hA36 hA38q hL hQ hn hp hd
  have hsecond : ∃ q : ℕ, q.Prime ∧ Odd q ∧ q ≠ p ∧
      q ∣ Nat.card (fittingSubgroup (XiQuotient L)) := ⟨q, hq, hqo, hqp, hqd⟩
  have escape (C : Subgroup (radicalCore p L T)) (hchar : C.Characteristic)
      (hne : C ≠ ⊥)
      (he : ¬ normalizer (C.map (radicalCore p L T).subtype : Set G) ≤
        normalizer (L : Set G)) := by
    let _ := hchar
    have hc := hres.characteristic_local C hchar hne
    exact exists_marked_five_component hG hA36 hA312 hA38
      p 5 Fact.out hp3 (by decide) L T hL hTL hunique hX hcore hshape hd hnil hfive
      hsecond hres.Y_cComponent hres.X_le_Y hres.Y_not_quasisimple C hne hc.1 hc.2.2 he
  obtain ⟨C₀, _, hC₀, hchar₀, _, _, _, hpC₀, hqC₀⟩ :=
    exists_thompsonChoice_fittingPrimes_of_B216 hB216 p q hp hqo hq5 L T
      hL.1 hTL hlocal hd hqd hres.X_le_Y (hres.actions q hq hqo hqd).2
      (hres.actions q hq hqo hqd).1
  let _ : C₀.Characteristic := hchar₀
  have hC₀M : normalizer (C₀.map (radicalCore p L T).subtype : Set G) ≤
      normalizer (L : Set G) := by
    by_contra he
    obtain ⟨_, K, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsupport, _⟩ :=
      escape C₀ hchar₀ hC₀ he
    have hp5 := (hsupport p Fact.out hp).mp hpC₀
    have hq5 := (hsupport q hq hqo).mp hqC₀
    exact hqp (hq5.trans hp5.symm)
  have hRM : normalizer (radicalCore p L T : Set G) ≤ normalizer (L : Set G) :=
    (normalizer_le_normalizer_characteristic_image _ C₀).trans hC₀M
  apply (characteristicNormalizerClosure_le_iff _ _).mpr
  intro C hchar hne
  let _ := hchar
  by_contra he
  obtain ⟨hM, K, hK, hYK, _, hKn, hTK, _, hXn, _, _, _, _, _,
      ⟨emodel⟩, _, _, hmarked⟩ := escape C hchar hne he
  let P : Sylow p (XiP p L) := Classical.arbitrary _
  let P₀ := (P : Subgroup (XiP p L)).map (XiP p L).subtype
  have hRcore : radicalCore p L T ≤ (K ⊔ radicalCore p L T).pCoreIn 2 :=
    radical_le_join_core_of_marked_five K (radicalCore p L T) _
      (normalizerResidual L (radicalCore p L T)) P₀ hK hKn
      ((radicalCore p L T).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ C))
      (radicalCore_isTwoGroup p L T) hYK ((map_subtype_le _).trans hres.X_le_Y)
      ((map_subtype_le _).trans (le_sup_left.trans (join_le_normalizer_radicalCore p L T)))
      emodel (hmarked P).1
  have heq : radicalCore p L T = (K ⊔ radicalCore p L T).pCoreIn 2 :=
    le_antisymm hRcore (twoCore_join_le_radicalCore p L K T hTK (hres.X_le_Y.trans hYK))
  have hKR : K ≤ normalizer (radicalCore p L T : Set G) := by
    rw [heq]
    exact le_sup_left.trans ((K ⊔ radicalCore p L T).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  apply hXn
  exact normal_subgroupOf_of_le_normalizer ((hKR.trans hRM).trans
    (normalizer_le_normalizer_XiP p L))

/-- The same control bound for an arbitrary member of Ξ*_rad, with its
actual core O₂(XT). The radical identification and all construction data are
discharged before applying the normalizer theorem. -/
theorem characteristicNormalizerClosure_le_of_XiRadStar
    {𝒦 : GroupClass.{u}} (hG : IsSimpleQTKE 𝒦 G)
    (hA36 : ∀ (A : Type u) [Group A] [Finite A],
      IsSQTK 𝒦 A → pCore 2 A = ⊥ → ∀ B : Subgroup A,
      B.IsCComponent → A36Conclusion B)
    (hA38q : ∀ (A : Type u) [Group A] [Finite A],
      IsSQTK 𝒦 A → pCore 2 A = ⊥ → ∀ B : Subgroup A,
      B.IsCComponent → B.Normal ∨ IsQuasisimple B)
    (hA38 : ∀ (A : Type u) [Group A] [Finite A],
      IsSQTK 𝒦 A → pCore 2 A = ⊥ → ∀ B : Subgroup A, B.IsCComponent →
      B.Normal ∨ (normalizer (B : Set A)).index = 2 ∧ NonnormalCComponentModel B)
    (hA312 : ∀ (A : Type u) [Group A] [Finite A],
      IsSQTK 𝒦 A → pCore 2 A = ⊥ → ∀ (S : Sylow 2 A) (B : Subgroup A),
      B ∈ ChapterA.Section03.localCComponents S → A312Conclusion B)
    (hB216 : ThompsonSource.TheoremB216.{u})
    (T : Sylow 2 G)
    (h127 : ∀ K ∈ LStar G (T : Subgroup G),
      IsMaximalTwoLocal (normalizer (componentOrbit K (T : Subgroup G) : Set G)) ∧
        ∀ M : Subgroup G, IsMaximalTwoLocal M → K ⊔ T ≤ M →
          M = normalizer (componentOrbit K (T : Subgroup G) : Set G))
    {X : Subgroup G} (hX : X ∈ XiRadStar G T) :
    characteristicNormalizerClosure ((X ⊔ T).pCoreIn 2) ≤ normalizer (X : Set G) := by
  have hQall : ∀ K ∈ Chapter1.L G (T : Subgroup G),
      IsSQTK 𝒦 ((K ⊔ T : Subgroup G) ⧸ pCore 2 (K ⊔ T : Subgroup G)) := by
    intro K hK
    exact uniqueness_local_quotient_sqtk hG hK.2.2
  obtain ⟨L, hL, p, hp, ho, _, hn, hd, heq, _⟩ :=
    XiRadStar_identification_of_A36 hA36 hA38q hQall hX
  let _ : Fact p.Prime := ⟨hp⟩
  subst X
  exact (characteristicNormalizerClosure_le_of_source hG hA36 hA38q hA38 hA312 hB216
    T h127 hL hn ho hd).trans (normalizer_le_normalizer_XiP p L)

end CFSG.Quasithin.Chapter1.RadicalNormalizers
