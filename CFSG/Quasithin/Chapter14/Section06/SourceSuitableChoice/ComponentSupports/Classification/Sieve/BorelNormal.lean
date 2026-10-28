module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.Sieve.EvenG2
public import Theory.GroupTheory.CComponent.OverlapRank
public import Theory.SpecificGroups.SL2.EvenBorelResidual

/-!
# Cubic Borel rank and the exchanged component catalogue

Pass to the literal H/O₂(H). The image of M intersect H has three-rank at
most one. A positive-rank component overlap therefore makes this image,
and hence T, normalize the component. The source orbit theorem upgrades
this to relative normality in H. Thus every exchanged component overlap,
and its placed Borel, has order prime to three.

For PSL₂ in even defining degree the Borel torus contains a cubic subgroup.
This excludes that exchanged row. The final consumer combines the surviving
odd-degree exchanged catalogue with the previously proved normal catalogue
at the unchanged terminal H=Mc. The odd-degree exchanged exclusions,
remaining normal rows, and support assembly remain with
qt-e-suitable-component-supports. Original 14.6.18 is the only earlier
source input retained here, owned by qt-e-14625-source.

Source: Aschbacher--Smith 14.6.20, printed p.1037, using 14.2.2(4).
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter13.Section08.Components.Models
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
include hG hempty hM hunique hmany hcard e hab hsolv

/-- Positive cubic rank in the literal overlap forces relative normality. -/
theorem source_component_normal_of_overlap_threeRank
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hpos : 0 < primeRank 3 (M.subgroupOf K)) : (K.subgroupOf H).Normal := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
  let D := (K.subgroupOf H).map q
  let I := (M.subgroupOf H).map q
  let ec := (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKH)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKH))).symm.trans (cComponentTwoCoreQuotientEquiv hK)
  let qK := ec.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let B := (M.subgroupOf K).map qK
  let J := B.map D.subtype
  have hker : qK.ker = pCore 2 K := by
    rw [MonoidHom.ker_comp_of_injective _ _ ec.injective,QuotientGroup.ker_mk']
  have hpB : 0 < primeRank 3 B := by
    rw [ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide : Odd 3)
      qK (hker.symm ▸ pCore_isPGroup)]
    exact hpos
  have hpJ : 0 < primeRank 3 J := by
    rwa [←primeRank_equiv 3 (B.equivMapOfInjective D.subtype D.subtype_injective)]
  have hJI : J ≤ I := by
    rintro x ⟨b,hb,rfl⟩
    obtain ⟨k,hk,rfl⟩ := hb
    exact ⟨⟨k,hKH k.property⟩,hk,rfl⟩
  have hR : solvableRadical (H ⧸ pCore 2 H) = ⊥ := by
    have hh := map_solvableRadical_equiv (QuotientGroup.quotientMulEquivOfEq
      (source_radical_eq_core hG T hempty hM hunique hmany hcard e hab hsolv H hH))
    rw [solvableRadical_quotient_solvableRadical,Subgroup.map_bot] at hh
    exact hh.symm
  have hIr : primeRank 3 I ≤ 1 :=
    source_component_overlap_image_threeRank_le_one hG T hempty hM hunique hmany hcard e
      H hH H le_rfl q (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
  have hIN := (hK.map_quotient (pCore 2 H)).le_normalizer_of_overlap_primeRank hR hIr
    (map_subtype_le B) hJI hpJ
  have hTN : (T : Subgroup G) ≤ normalizer (K : Set G) := by
    have hTI : ((T : Subgroup G).subgroupOf H).map q ≤ I :=
      map_mono (subgroupOf_mono H hM.1.2)
    have ht := map_le_iff_le_comap.mp (hTI.trans hIN)
    rw [normalizer_cComponent_quotient hK (pCore 2 H)] at ht
    intro t htt
    have hh := ht (show (⟨t,hH.1.2 htt⟩ : H) ∈ (T : Subgroup G).subgroupOf H from htt)
    rwa [←subgroupOf_normalizer_eq hKH] at hh
  have he : conjugateSpanBy K (T : Subgroup G) = K :=
    le_antisymm (conjugateSpanBy_le le_rfl hTN) (le_conjugateSpanBy K _)
  apply (normal_subgroupOf_iff_le_normalizer hKH).mpr
  rw [←he]
  exact source_component_orbit_normal hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK

/-- An exchanged component has no cubic subgroup in its original M-overlap. -/
theorem source_nonnormal_component_overlap_threeRank_eq_zero
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : ¬ (K.subgroupOf H).Normal) : primeRank 3 (M.subgroupOf K) = 0 := by
  by_contra hz
  exact hn (source_component_normal_of_overlap_threeRank hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K hKH hK (Nat.pos_of_ne_zero hz))

/-- Every marked Borel of an exchanged component has order prime to three. -/
theorem source_nonnormal_component_borel_threePrime
    {E : Type*} [Group E] [Finite E]
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : ¬ (K.subgroupOf H).Normal) (eK : (K ⧸ pCore 2 K) ≃* E)
    (P : Sylow 2 K) (hP : (P : Subgroup K) = (T : Subgroup G).subgroupOf K) :
    ¬ 3 ∣ Nat.card (normalizer (((P : Subgroup K).map
      (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))) : Set E)) := by
  apply PrimeRank.eq_zero_iff_not_dvd_card.mp
  apply Nat.eq_zero_of_le_zero
  have hp := source_component_sylow_normalizer_le_image T M hsolv H hH.1 K hKH hK eK P hP
  apply (primeRank_mono 3 hp).trans
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hk : q.ker = pCore 2 K := by
    rw [MonoidHom.ker_comp_of_injective _ _ eK.injective,QuotientGroup.ker_mk']
  change primeRank 3 ((M.subgroupOf K).map q) ≤ 0
  rw [ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide : Odd 3) q
    (hk.symm ▸ pCore_isPGroup),
    source_nonnormal_component_overlap_threeRank_eq_zero hG T hempty hM hunique hmany hcard e hab hsolv
      H hH K hKH hK hn]

/-- The Borel torus excludes every even defining degree in an exchanged
PSL₂ component. The original component quotient and its Sylow are retained. -/
theorem source_nonnormal_component_not_even_psl_two
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : ¬ (K.subgroupOf H).Normal) {f : ℕ} (he : Even f) :
    ¬ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f) := by
  rintro ⟨F,_,_,hF,⟨eK⟩⟩
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  obtain ⟨P,hP⟩ := source_component_sylow T H K hH.1.2 hKH hK
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let Pq := P.mapSurjective (f := q) (eK.surjective.comp (QuotientGroup.mk'_surjective _))
  have hu := source_nonnormal_component_borel_threePrime hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K hKH hK hn eK P hP
  change ¬ 3 ∣ Nat.card (normalizer (Pq : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))) at hu
  rw [Nat.card_congr (Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.sylowNormalizerEquiv F Pq).toEquiv,
    Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.card_borel,hF] at hu
  exact hu (dvd_mul_of_dvd_right ((Nat.BinaryTorusParity.three_dvd_sub_one_iff f).mpr he) _)

/-- A PSL₂ component in even field degree must be relatively normal. -/
theorem source_component_even_psl_two_normal
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    {f : ℕ} (he : Even f) (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f)) :
    (K.subgroupOf H).Normal := by
  by_contra hn
  exact source_nonnormal_component_not_even_psl_two hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K hKH hK hn he hm

/-- The remaining exchanged rows have odd nonbinary degree, or binary PSL₃.
The odd-degree Borel fixed-space exclusion is still a separate local step. -/
@[expose] def NonnormalOddQuotientModels (D : Type*) [Group D] : Prop :=
  (∃ f : ℕ, 3 ≤ f ∧ Odd f ∧ ClassicalGroup.IsPSL D 2 (2 ^ f)) ∨
  (∃ m : ℕ, 0 < m ∧ Nonempty (D ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) ∨
  ClassicalGroup.IsPSL D 3 2

/-- Apply the cubic-overlap exclusion to the actual exchanged F.9.18 list. -/
theorem source_nonnormal_component_odd_models
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : ¬ (K.subgroupOf H).Normal) : NonnormalOddQuotientModels (K ⧸ pCore 2 K) := by
  have hm := source_nonnormal_component_f918_models hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K hKH hK hn
  rcases hm with ⟨f,hf,hm⟩ | hs | hl
  · have ho : Odd f := (Nat.even_or_odd f).resolve_left fun he =>
      source_nonnormal_component_not_even_psl_two hG T hempty hM hunique hmany hcard e hab hsolv
        H hH K hKH hK hn he hm
    exact Or.inl ⟨f,by obtain ⟨k,hk⟩ := ho; omega,ho,hm⟩
  · exact Or.inr (Or.inl hs)
  · exact Or.inr (Or.inr hl)

/-- The normal and exchanged catalogue refinements both apply at the original
terminal H=Mc, with no change of ambient span or component quotient. -/
theorem terminal_component_normal_or_odd_models
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent) :
    ((K.subgroupOf Mc).Normal ∧ NormalRemainingQuotientModels (K ⧸ pCore 2 K)) ∨
    (¬ (K.subgroupOf Mc).Normal ∧ NonnormalOddQuotientModels (K ⧸ pCore 2 K)) := by
  by_cases hn : (K.subgroupOf Mc).Normal
  · exact Or.inl ⟨hn,terminal_normal_component_remaining_models
      hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hn⟩
  · exact Or.inr ⟨hn,source_nonnormal_component_odd_models
      hG T hempty hM hunique hmany hcard e hab hsolv Mc
        (terminal_outside hG T hempty hM hunique hmany hcard e) K hKM hK hn⟩

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve
