module
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.BlockKernel
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.AlternatingSixMS
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.MSPreparation
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.AlternatingPlacement
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.LinearThree.Descent
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.SourceClassifications
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.SpecificGroups.SymmetricSix.Parabolics.ThreeRank
public import Theory.Alternating.OddCentralCovers

/-!
# Excluding the original A₆ star image

The original partner intersection contains a Sylow two-subgroup of X and
has three-rank at least two, by placement of the original K. Thus its full
core quotient cannot be A₆: every proper Sylow-two overgroup in A₆ has
three-rank at most one. This preserves the possible central kernel of
the star projection; an A₆ star image would force that kernel to have
order three.

The same X and R form a genuine small MS pair. The earlier C.1.32 input
then gives either a block or a full SL₃ quotient. A block makes the literal
core-to-star map injective, contradicting the preceding obstruction.
The SL₃ alternative has the wrong order. This excludes both B.5.1 actions
whose marked component is A₆, without assuming placement of the entire KS.
The earlier small MS classification retains its original producer.

Source: Aschbacher--Smith C.1.31--32, pp.135--136; C.2.7, pp.145--147;
original 15.2.23, pp.1116--1117; refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
open Section01 PlaneUniquenessPreceding PlaneUniquenessPreceding.LinearThree TerminalLinear
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source
open Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)

include d in
private theorem component_sylow_in_partner
    (hI : PlaneEscapes Mc ZS I) (hX : X ∈ Chapter1.cComponentsIn I) :
    ∃ P : Sylow 2 X, (P : Subgroup X) ≤ Mc.subgroupOf X := by
  obtain ⟨R,hR⟩ := d.sylow_in_escape hI
  obtain ⟨Q,hQ⟩ := R.exists_subgroupOf_eq_of_subnormal (X.subgroupOf I) hX.2.subnormal
  let e := subgroupOfEquivOfLe hX.1
  refine ⟨Q.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  rintro x ⟨y,hy,rfl⟩
  have hyR : (y : I) ∈ R := by
    change y ∈ (R : Subgroup I).subgroupOf (X.subgroupOf I)
    rwa [← hQ]
  have hyS : ((y : I) : G) ∈ planeSylow T ZS := hR ▸ mem_map_of_mem I.subtype hyR
  exact ((le_sup_right.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_left) hyS

include d in
/-- The original partner geometry rules out the full A₆ core quotient. -/
theorem normalized_alternatingSix_no_ordinary_core
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (s : Normalized H M I X)
    (e : starImage X ((M ⊓ I).pCoreIn 2) X ≃* alternatingGroup (Fin 6))
    (a : (X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 6)) : False := by
  let K := (pResidual 2 H).map H.subtype
  have hK : K ≤ M1 X ZS := alternating_star_residual_le_M1 d hI hcore s (Or.inl rfl) e
  have hKX : K ≤ X := hK.trans inf_le_left
  have hKM : K ≤ Mc := hK.trans ((M1_le_partner_intersection d hI s.component.1).trans inf_le_left)
  have hproper : Mc.subgroupOf X ≠ ⊤ := by
    intro he
    exact alternating_star_not_le_partner d horbit hI hcore s (Or.inl rfl) e
      (subgroupOf_eq_top.mp he)
  obtain ⟨P,hP⟩ := component_sylow_in_partner d hI s.component
  have hu := Theory.SpecificGroups.SymmetricSix.twoCoreQuotient_sylow_overgroup_three_rank_le_one
    a P (Mc.subgroupOf X) hP hproper
  have hl : 2 ≤ primeRank 3 (Mc.subgroupOf X) := by
    have hh := primeRank_mono 3 (show K.subgroupOf X ≤ Mc.subgroupOf X from fun _ hx => hKM hx)
    rw [primeRank_congr 3 (subgroupOfEquivOfLe hKX), residual_rank_two d] at hh
    exact hh
  omega

include d in
/-- An A₆ star image forces a cubic center in the full core quotient. -/
theorem normalized_alternatingSix_core_center_three
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (s : Normalized H M I X)
    (e : starImage X ((M ⊓ I).pCoreIn 2) X ≃* alternatingGroup (Fin 6)) :
    Nat.card (center (X ⧸ pCore 2 X)) = 3 := by
  let h := normalized_component_input (hsource := hsource) hI hcore s
  rcases coreQuotient_center_card_from_source h with hc | hc
  · exact (normalized_alternatingSix_no_ordinary_core d horbit hI hcore s e
      (GLS3.Chapter5.OddCentralCovers.alternatingEquivOfCenterCardOne 6
        (alternatingStarCoreCenterEquiv h (by decide) e) hc)).elim
  · exact hc

include d in
/-- All small MS-pair hypotheses hold on the original X and R. -/
theorem normalized_alternatingSix_smallMSPair
    (hI : PlaneEscapes Mc ZS I) (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (s : Normalized H M I X)
    (e : starImage X ((M ⊓ I).pCoreIn 2) X ≃* alternatingGroup (Fin 6)) :
    SmallMSPair KnownSimple.IsKnownSimple X ((M ⊓ I).pCoreIn 2) := by
  let R := (M ⊓ I).pCoreIn 2
  let D := X ⊔ R
  let L := X.subgroupOf D
  let h := normalized_component_input (hsource := hsource) hI hcore s
  let : L.Normal := normal_subgroupOf_of_le_normalizer (sup_le X.le_normalizer s.radical_normalizes)
  refine ⟨inferInstance,(source_join_input h).setup.sqtk,source_join_fitting h,?_,
    (source_join_input h).component.2,?_,normalized_component_ms_oddIndex d hI hcore s,
    source_ms_characteristic h⟩
  · intro g hg
    have hm : (⟨g,hg⟩ : D) ∈ L ⊔ R.subgroupOf D := by
      rw [←subgroupOf_sup (show X ≤ D from le_sup_left) (show R ≤ D from le_sup_right),subgroupOf_self]
      trivial
    obtain ⟨x,hx,r,hr,he⟩ := mem_sup_of_normal_left.mp hm
    exact ⟨x,hx,r,hr,congrArg Subtype.val he⟩
  · exact Or.inr (Or.inl ⟨(source_a6_coreCenterQuotientEquiv h e).trans
      (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix
        (F := ZMod 2) (by simp)).symm⟩)

private theorem linearThree_card_ne_1080
    (n : ℕ) (F : Type*) [Field F] [Finite F] (hn : 1 ≤ n) (hF : Nat.card F = 2^n) :
    Nat.card SL(3,F) ≠ 1080 := by
  have hc : Nat.card SL(3,F) =
      Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center SL(3,F)),
      Atlas.ExceptionalSupport.card_sl_center]
    exact Matrix.PSL3.LinearThree.card_projective_mul_scalar F
  intro he
  by_cases h1 : n = 1
  · rw [h1,pow_one] at hF
    rw [hc,hF] at he
    norm_num at he
  · have hq : 4 ≤ Nat.card F := by
      rw [hF]
      exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ n)
    have hh := Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.pow_le_pow_left hq 3)
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 3) 1))
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
    rw [←hc,he] at hh
    norm_num at hh

include d in
/-- The C.1.32 conclusion only for this original pair suffices for the A₆
exclusion. No universal linear-three module classification is used. -/
theorem normalized_alternatingSix_false_of_rankTwo
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (s : Normalized H M I X)
    (e : starImage X ((M ⊓ I).pCoreIn 2) X ≃* alternatingGroup (Fin 6))
    (hm : RankTwoAlternatives X ((M ⊓ I).pCoreIn 2)) : False := by
  have noBlock (hb : ChapterC.IsBlock (X.subgroupOf (X ⊔ (M ⊓ I).pCoreIn 2))) : False := by
    let a := MulEquiv.ofBijective (coreToStar s.radical_normalizes)
      ⟨coreToStar_injective_of_block s.radical_normalizes hb,
        coreToStar_surjective s.radical_normalizes⟩
    exact normalized_alternatingSix_no_ordinary_core d horbit hI hcore s e (a.trans e)
  rcases hm with ⟨hb,_⟩ | ⟨hb,_⟩ | ⟨hb,_⟩ | ⟨hb,_⟩ | ⟨n,hn,F,_,_,hF,⟨a⟩⟩
  · exact noBlock hb
  · exact noBlock hb
  · exact noBlock hb
  · exact noBlock hb
  · apply linearThree_card_ne_1080 n F hn hF
    rw [← Nat.card_congr a.toEquiv]
    let h := normalized_component_input (hsource := hsource) hI hcore s
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center (X ⧸ pCore 2 X)),
      Nat.card_congr (alternatingStarCoreCenterEquiv h (by decide) e).toEquiv,
      nat_card_alternatingGroup,normalized_alternatingSix_core_center_three d horbit hI hcore s e]
    norm_num [Nat.factorial]

include d in
/-- Legacy conditional adapter. Source assembly must supply only the actual
pair's rank-two conclusion, without constructing the universal record. -/
theorem normalized_alternatingSix_false
    (hC : EarlierMSClassifications.{u} KnownSimple.IsKnownSimple)
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (s : Normalized H M I X)
    (e : starImage X ((M ⊓ I).pCoreIn 2) X ≃* alternatingGroup (Fin 6)) : False :=
  normalized_alternatingSix_false_of_rankTwo d horbit hI hcore s e
    (hC.rankTwo G X ((M ⊓ I).pCoreIn 2)
      (normalized_alternatingSix_smallMSPair d hI hcore s e))



end CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
