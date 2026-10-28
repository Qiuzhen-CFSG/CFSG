module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalSmallGenerationAssembly
public import CFSG.Quasithin.Chapter3.Section01.CommonNormalKnownSimple
public import Theory.GroupTheory.PCoreQuotientInnerSupplement
public import Theory.GroupTheory.NormalSylowQuotientAction
public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms
public import Theory.FieldTheory.FiniteAutomorphismOrder
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore

/-!
# Evenness of the original rank-one field exponent

If the Cartan normalized T, the original common-normal theorem 3.1.1
would put a nontrivial normal two-subgroup in its join with H. This
contradicts the zero-core hypothesis. If T had trivial field action on
L/O₂(L), the inner-action supplement theorem would give
T = (T ∩ L) O₂(LT), and the local Borel would normalize both factors.
Thus the Cartan would normalize T, the same contradiction.

The nontrivial image of the two-group T in the finite field's automorphism
group has even order. That automorphism group has order n, proving Even n
for the original exponent of L/O₂(L), without restricting n(H).

Source: Aschbacher--Smith, original 5.1.6, printed p.632,
`refs/quasithin.pdf`.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Zero core excludes a Cartan that normalizes the original ambient Sylow. -/
theorem Input.cartan_not_normalizes_sylow {T : Sylow 2 G} {L W H A : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hzero : (A ⊔ H).pCoreIn 2 = ⊥) :
    ¬ A ≤ normalizer (T : Set G) := by
  intro hAN
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hT : (T : Subgroup G) ≠ ⊥ := by
    have hQT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
      simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] using
        pCoreIn_le_sylow H (T.subtype hTH)
    exact fun he => hH.1.1.1 (bot_unique (he ▸ hQT))
  have hnorm : A ⊔ (T : Subgroup G) ≤ normalizer (T : Set G) :=
    sup_le hAN (T : Subgroup G).le_normalizer
  have hcore : (T : Subgroup G) ≤ (A ⊔ (T : Subgroup G)).pCoreIn 2 :=
    le_pCoreIn_of_normalizes T.isPGroup' le_sup_right hnorm
  have hAT : A ⊔ (T : Subgroup G) ∈ Chapter1.HOver G (T : Set G) :=
    ⟨fun he => hT (bot_unique (he ▸ hcore)), fun _ hx => mem_sup_right hx⟩
  have hs : Chapter1.IsSylowIn 2 (T : Subgroup G)
      ((pResidual 2 H).map H.subtype ⊔ (T : Subgroup G)) := by
    rw [residual_sup_sylow T H hTH]
    exact ⟨T.subtype hTH, by
      simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH]⟩
  obtain ⟨N, hNT, hN, hnormal⟩ := Chapter3.source_common_normal_knownSimple
    h.qtke T (A ⊔ (T : Subgroup G)) H (T : Subgroup G) hAT hH.1.1
    (Chapter3.HStar.hasUniqueMaximalOver T h.sylow_normalizes hH) hT le_rfl hs hnorm
  have hNH : N ≤ A ⊔ H := hNT.trans (hTH.trans le_sup_right)
  have hgen : Chapter3.generated (A ⊔ (T : Subgroup G)) H = A ⊔ H := by
    rw [Chapter3.generated_eq_sup, sup_assoc, sup_eq_right.mpr hTH]
  have hnormal' : A ⊔ H ≤ normalizer (N : Set G) := by
    simpa only [hgen] using (Chapter3.normalIn_iff_le_normalizer.mp hnormal).2
  have hNC := le_pCoreIn_of_normalizes (T.isPGroup'.to_le hNT) hNH hnormal'
  exact hN (bot_unique (hzero ▸ hNC))


open scoped MatrixGroups

/-- The literal quotient conjugation action followed by the field projection. -/
noncomputable def cartanFieldAction {T : Sylow 2 G} {L : Subgroup G}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (L ⧸ pCore 2 L) ≃* PSL(2,F)) : T →* (F ≃+* F) :=
  (Theory.PSL2.fieldProjection F).comp
    ((MulAut.congr e).toMonoidHom.comp
      ((pCoreJoinAction 2 hTL).comp (inclusion le_sup_right)))

omit [Finite G] in
private theorem quotient_center_eq_bot {L : Subgroup G}
    {F : Type*} [Field F] [CharP F 2]
    (e : (L ⧸ pCore 2 L) ≃* PSL(2,F)) : center (L ⧸ pCore 2 L) = ⊥ := by
  apply (center _).eq_bot_iff_forall.mpr
  intro x hx
  apply e.injective
  rw [map_one]
  have hx' : e x ∈ center PSL(2,F) := by
    rw [mem_center_iff]
    intro y
    obtain ⟨y, rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (mem_center_iff.mp hx y)
  simpa only [Atlas.RankOneFieldAutomorphisms.psl_center_eq_bot, mem_bot] using hx'

/-- Failure to normalize T forces a nontrivial field-action image. -/
theorem CartanPair.fieldAction_ne_bot {T : Sylow 2 G} {L H A B : Subgroup G}
    (c : CartanPair T L H A B)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (L ⧸ pCore 2 L) ≃* PSL(2,F))
    (hnot : ¬ A ≤ normalizer (T : Set G)) :
    (cartanFieldAction hTL e).range ≠ ⊥ := by
  intro hzero
  have hi (t : T) : pCoreJoinAction 2 hTL (inclusion le_sup_right t) ∈
      MulAut.innerSubgroup (L ⧸ pCore 2 L) := by
    have ht : cartanFieldAction hTL e t = 1 := by
      have ht : cartanFieldAction hTL e t ∈ (cartanFieldAction hTL e).range := ⟨t, rfl⟩
      simpa only [hzero, mem_bot] using ht
    have ht' : MulAut.congr e (pCoreJoinAction 2 hTL (inclusion le_sup_right t)) ∈
        Theory.PSL2.inner F := by
      rw [← Theory.PSL2.fieldProjection_ker]
      exact ht
    change MulAut.congr e (pCoreJoinAction 2 hTL (inclusion le_sup_right t)) ∈
      MulAut.innerSubgroup PSL(2,F) at ht'
    rw [← MulAut.map_innerSubgroup_congr e] at ht'
    obtain ⟨a, ha, he⟩ := ht'
    exact (MulAut.congr e).injective he ▸ ha
  obtain ⟨P, hP⟩ := NormalSylowQuotientAction.intersection_sylow T L hTL
  have hPT : (P : Subgroup L).map L.subtype = (T : Subgroup G) ⊓ L := by
    rw [hP, subgroupOf_map_subtype]
  have hfactor := sup_core_factor_of_inner_action L (T : Subgroup G) hTL T.isPGroup'
    (quotient_center_eq_bot e) P (hPT.le.trans inf_le_left) hi
  have hB1 : localBorel T L ≤ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) :=
    inf_le_right
  let X := L ⊔ (T : Subgroup G)
  have hB2 : localBorel T L ≤ normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) :=
    (inf_le_left.trans le_sup_left).trans
      (X.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image X (pCore 2 X)))
  apply hnot
  change A ≤ normalizer ((T : Subgroup G) : Set G)
  have hnorm := (le_inf hB1 hB2).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  rw [hPT] at hfactor
  simpa only [← hfactor] using c.left_le.trans hnorm

omit [Finite G] in
/-- A nontrivial two-group of field automorphisms forces an even field degree. -/
theorem even_of_cartanFieldAction_ne_bot {T : Sylow 2 G} {L : Subgroup G} {n : ℕ}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (L ⧸ pCore 2 L) ≃* PSL(2,F))
    (hF : Nat.card F = 2 ^ n) (hne : (cartanFieldAction hTL e).range ≠ ⊥) : Even n := by
  have hp : IsPGroup 2 (cartanFieldAction hTL e).range :=
    T.isPGroup'.of_surjective _ (cartanFieldAction hTL e).rangeRestrict_surjective
  have hd : 2 ∣ Nat.card (cartanFieldAction hTL e).range := by
    rcases hp.card_eq_or_dvd with hc | hc
    · exact (hne ((cartanFieldAction hTL e).range.eq_bot_of_card_eq hc)).elim
    · exact hc
  apply even_iff_two_dvd.mpr
  have hn := hd.trans (card_subgroup_dvd_card (cartanFieldAction hTL e).range)
  rwa [FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two hF] at hn


/-- The parity clause of source 5.1.6, for the original field exponent. -/
theorem Input.cartan_even_of_zero_core {T : Sylow 2 G} {L W H A B : Subgroup G}
    {n : ℕ} (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hzero : (A ⊔ H).pCoreIn 2 = ⊥) : Even n := by
  have hnot := h.cartan_not_normalizes_sylow hH hzero
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h.linear
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  exact even_of_cartanFieldAction_ne_bot h.sylow_normalizes e hF
    (c.fieldAction_ne_bot h.sylow_normalizes e hnot)

/-- Discharge the original parity contract without any module-classification
or higher-field premise. -/
theorem sourceCartanEvenExponent_knownSimple :
    SourceCartanEvenExponent KnownSimple.IsKnownSimple G := by
  intro T L W n h H hH _hgen A B c hzero
  exact h.cartan_even_of_zero_core hH c hzero

/-- The odd-exponent branch of the actual local-to-global normalization
implication: the whole Cartan join has nontrivial core. -/
theorem Input.cartan_normalizes_of_odd {T : Sylow 2 G} {L W H A B : Subgroup G}
    {n : ℕ} (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hc : CartanLocalControl A H) (hn : Odd n) :
    A ≤ normalizer (residual H : Set G) := by
  apply hc A le_rfl
  intro hzero
  exact (Nat.not_even_iff_odd.mpr hn) (h.cartan_even_of_zero_core hH c hzero)

/-- The small-Cartan assembly now needs only the higher-degree branch of
5.1.6. Its parity input is proved above on the original generic setup. -/
theorem sourceCartanSmallGeneration_of_higher_knownSimple
    (hhigher : SourceCartanHigherFieldReduction KnownSimple.IsKnownSimple G) :
    SourceCartanSmallGeneration KnownSimple.IsKnownSimple G :=
  sourceCartanSmallGeneration_of_even_and_higher sourceCartanEvenExponent_knownSimple hhigher

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
