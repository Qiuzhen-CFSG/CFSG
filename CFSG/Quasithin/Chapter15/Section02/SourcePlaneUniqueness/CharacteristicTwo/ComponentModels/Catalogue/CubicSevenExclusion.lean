module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.OriginalSevenExclusion
public import Theory.GroupTheory.PCoreCentralizingSupplement
public import Theory.GroupTheory.PCoreInRestriction
public import Theory.Alternating.SevenQuasisimpleExtension
public import Theory.GroupTheory.PCoreNormalizerAction.CubicCenter

/-!
# Excluding the cubic seven-letter component on the original QI

The original K has three-rank two, so its image in X/O₂(X) contains the
cubic center. Since K normalizes QI, displacement modulo O₂(X) shows
that QI fixes this center. Every outer automorphism of 3.A₇ inverts it;
therefore QI acts by even permutations on the whole original U.

B.3.2(4) places J(QI) in the literal U-action kernel. Equivariance through
the perfect core-to-star cover shows that this kernel centralizes X
modulo O₂(X). A normal-kernel argument puts its two-subgroups in O₂(XQI),
even though the kernel can have odd order. The original Thompson
normalizer control now gives the contradiction.

Together with the centerless exclusion, this removes the entire
seven-letter row. The source consumer retains the same selected component,
full B.5.1 moved section and all six source clauses. Its sole remaining row
has the actual marked binary symplectic action and cubic core center.
The cubic A₆ exclusion, full original KS placement and final 15.2.23
assembly remain with this owner; no universal MS input is used here.

Source: Aschbacher--Smith 15.2.23, pp.1115--1117, B.3.2(4), p.83,
and C.2.7, pp.145--147; refs/quasithin.pdf. The center-inversion input
is GLS3 5.2.3 and 5.2.7, transported through the actual perfect cover.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
open Section01 PlaneUniquenessPreceding PlaneUniquenessPreceding.LinearThree TerminalLinear
open ChapterD ChapterD.UniqueFactor
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
variable {X E : Subgroup G}

omit [Finite G] in
private theorem seven_cover_equivariant
    (hXE : X ≤ E) (hEX : E ≤ normalizer (X : Set G))
    (q : PerfectCentralCovering.Cover (X ⧸ pCore 2 X) (alternatingGroup (Fin 7)))
    (f : E →* Equiv.Perm (Fin 7))
    (hf : ∀ x : X, f (inclusion hXE x) = (q.toMonoidHom (QuotientGroup.mk' (pCore 2 X) x)).val)
    (g : E) (z : X ⧸ pCore 2 X) :
    q.toMonoidHom (pCoreNormalizerAction 2 X (inclusion hEX g) z) =
      MulAut.conjNormal (f g) (q.toMonoidHom z) := by
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 X) z
  apply Subtype.ext
  rw [pCoreNormalizerAction_mk,←hf]
  change f (inclusion hXE (X.normalizerMonoidHom (inclusion hEX g) x)) =
    f g * (q.toMonoidHom (QuotientGroup.mk' (pCore 2 X) x)).val * (f g)⁻¹
  rw [←hf]
  rw [←map_inv,←map_mul,←map_mul]
  congr 1

private theorem seven_cover_even_of_fixed_center
    (hXE : X ≤ E) (hEX : E ≤ normalizer (X : Set G))
    (q : PerfectCentralCovering.Cover (X ⧸ pCore 2 X) (alternatingGroup (Fin 7)))
    (e : (X ⧸ pCore 2 X) ≃* GLS3.Chapter5.OddCentralCovers.TripleSeven)
    (f : E →* Equiv.Perm (Fin 7))
    (hf : ∀ x : X, f (inclusion hXE x) = (q.toMonoidHom (QuotientGroup.mk' (pCore 2 X) x)).val)
    (g : E)
    (hfix : ∀ z ∈ center (X ⧸ pCore 2 X), pCoreNormalizerAction 2 X (inclusion hEX g) z = z) :
    f g ∈ alternatingGroup (Fin 7) := by
  let a := pCoreNormalizerAction 2 X (inclusion hEX g)
  have hi : a ∈ MulAut.innerSubgroup (X ⧸ pCore 2 X) := by
    by_contra hn
    have hout : ∀ k, a ≠ MulAut.conj k := fun k he => hn ⟨k,he.symm⟩
    have hc : Nat.card (center (X ⧸ pCore 2 X)) = 3 :=
      (Nat.card_congr (centerCongr e).toEquiv).trans
        GLS3.Chapter5.OddCentralCovers.tripleSeven_center_card
    obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := center (X ⧸ pCore 2 X)) 3
      (by rw [hc])
    have hinv := Theory.AlternatingSevenExtension.center_inverted_of_tripleSeven_model
      e a hout z z.property
    have he : (z : X ⧸ pCore 2 X) = (z : X ⧸ pCore 2 X)⁻¹ :=
      (hfix z z.property).symm.trans hinv
    have hp : (z : X ⧸ pCore 2 X)^2 = 1 := by
      exact (pow_two _).trans ((congrArg (fun t => t * (z : X ⧸ pCore 2 X)) he).trans (inv_mul_cancel _))
    have hd := orderOf_dvd_of_pow_eq_one hp
    rw [Subgroup.orderOf_coe,hz] at hd
    norm_num at hd
  have hb := (q.equivariant_inner_iff a (MulAut.conjNormal (f g))
    (seven_cover_equivariant hXE hEX q f hf g)).mp hi
  obtain ⟨k,hk⟩ := hb
  have he : f g = (k : Equiv.Perm (Fin 7)) := by
    apply (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
      (by decide) (by decide)).1
    exact hk.symm
  exact he ▸ k.property

omit [Finite G] in
private theorem seven_cover_kernel_commutator
    (hXE : X ≤ E) (hEX : E ≤ normalizer (X : Set G))
    (q : PerfectCentralCovering.Cover (X ⧸ pCore 2 X) (alternatingGroup (Fin 7)))
    (f : E →* Equiv.Perm (Fin 7))
    (hf : ∀ x : X, f (inclusion hXE x) = (q.toMonoidHom (QuotientGroup.mk' (pCore 2 X) x)).val) :
    ⁅f.ker,X.subgroupOf E⁆ ≤ (X.subgroupOf E).pCoreIn 2 := by
  rw [pCoreIn_subgroupOf 2 X E hXE]
  apply commutator_le.mpr
  intro c hc x hx
  have ha : pCoreNormalizerAction 2 X (inclusion hEX c) = 1 :=
    (q.equivariant_eq_one_iff _ (MulAut.conjNormal (f c))
      (seven_cover_equivariant hXE hEX q f hf c)).mpr (by rw [show f c = 1 from hc,map_one])
  have hh := (pCoreNormalizerAction_eq_one_iff 2 X (inclusion hEX c)).mp ha ⟨x,hx⟩
  change (c : G) * (x : G) * (c : G)⁻¹ * (x : G)⁻¹ ∈ X.pCoreIn 2
  have hm := mem_map_of_mem X.subtype hh
  rw [map_div,div_eq_mul_inv] at hm
  change (X.normalizerMonoidHom (inclusion hEX c) ⟨x,hx⟩ : G) * (x : G)⁻¹ ∈ X.pCoreIn 2 at hm
  rw [normalizerMonoidHom_apply_apply_coe] at hm
  exact hm

variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The original QI excludes the cubic seven-letter cover on the whole U. -/
theorem originalSeven_false_of_cubic_center
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G)) (hout : ¬ X ≤ Mc)
    (hKX : (pResidual 2 H).map H.subtype ≤ X)
    (hc : OriginalSevenCoordinates X ((M ⊓ I).pCoreIn 2) ZS)
    (h : Input KnownSimple.IsKnownSimple I ((M ⊓ I).pCoreIn 2) (M ⊓ I) X)
    (hz : Nat.card (center (X ⧸ pCore 2 X)) = 3) : False := by
  obtain ⟨e,A,hmark,hnU,hA⟩ := hc
  let R := (M ⊓ I).pCoreIn 2
  let Q := QI H T ZS
  let E := X ⊔ Q
  let W := (U X ZS).subgroupOf E
  let Q' := Q.subgroupOf E
  let K := (pResidual 2 H).map H.subtype
  have hQI : Q ≤ I := (pCoreIn_le 2 _).trans
    ((d.residual_sup_planeSylow_le hI).trans inf_le_right)
  have hEI : E ≤ I := sup_le hXI hQI
  have hUX : U X ZS ≤ X := by
    apply le_normalizer_iff_commutator_le_right.mp
    exact ((d.plane_span_le_planeParabolicCore hI hfit hXI).trans hQI).trans hn
  have hUE : U X ZS ≤ E := hUX.trans le_sup_left
  have hEU : E ≤ normalizer (U X ZS : Set G) := U_normalized d hI hn
  have hEX : E ≤ normalizer (X : Set G) := hEI.trans hn
  let eA : starImage X R X ≃* alternatingGroup (Fin 7) :=
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr hmark)
  let q : X →* alternatingGroup (Fin 7) := eA.toMonoidHom.comp (toStarImage X R)
  have hq : Function.Surjective q := eA.surjective.comp (toStarImage_surjective X R)
  let c : BinaryConjugationSection X (U X ZS) ⊥
      ((BinaryPermutation.alternatingNaturalRepresentation (Fin 7)).comp q) := {
    section_le := hUX
    kernel_le := bot_le
    normalized := le_sup_left.trans hnU
    coordinates := A.toMonoidHom
    onto := A.surjective
    kernel_eq := by rw [A.toMonoidHom.ker_eq_bot_iff.mpr A.injective,bot_subgroupOf]
    equivariant := fun x u => hA ⟨x,mem_sup_left x.property⟩ u _ rfl }
  obtain ⟨f,hf,hfx⟩ := BinaryConjugationSection.exists_seven_normalizer_action
    X (U X ZS) E le_sup_left hEU hEX q hq c
  have hker : f.ker = (centralizer (U X ZS : Set G)).subgroupOf E :=
    BinaryConjugationCoordinates.model_kernel E (U X ZS) hEU
      (BinaryPermutation.naturalRepresentation (Fin 7))
      (BinaryPermutation.naturalRepresentation_injective (Fin 7) (by decide)) f A hf
  let cover : PerfectCentralCovering.Cover (X ⧸ pCore 2 X) (alternatingGroup (Fin 7)) := {
    toMonoidHom := eA.toMonoidHom.comp (coreToStar h.normalizes)
    surjective := eA.surjective.comp (coreToStar_surjective h.normalizes)
    isPerfect := h.quasisimple.toIsPerfect
    ker_le_center := by
      rw [MonoidHom.ker_comp_of_injective _ _ eA.injective]
      exact coreToStar_ker_central_from_source h }
  have hfmark (x : X) : f (inclusion (show X ≤ E from le_sup_left) x) =
      (cover.toMonoidHom (QuotientGroup.mk' (pCore 2 X) x)).val := by
    rw [hfx]
    rfl
  let qX := QuotientGroup.mk' (pCore 2 X)
  have hKrank : primeRank 3 ((K.subgroupOf X).map qX) = 2 := by
    rw [ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide) qX
      (by rw [show qX.ker = pCore 2 X from QuotientGroup.ker_mk' _]; exact pCore_isPGroup),
      primeRank_congr 3 (subgroupOfEquivOfLe hKX),residual_rank_two d]
  have hXrank : primeRank 3 (X ⧸ pCore 2 X) ≤ 2 := by
    rw [primeRank_quotient_eq_of_isTwoGroup 3 (by decide) _ pCore_isPGroup]
    exact (primeRank_mono 3 hXI).trans
      ((Chapter1.RadicalExclusions.sqtk_of_mem_H hsource.ambient hI.1).stronglyQuasithin
        3 Nat.prime_three (by decide))
  have hcenter := cubic_center_le_of_three_rank_two ((K.subgroupOf X).map qX)
    hKrank.ge hXrank hz
  let : IsQuasisimple (X ⧸ pCore 2 X) := h.quasisimple
  obtain ⟨eCore⟩ := GLS3.Chapter5.OddCentralCovers.triple_seven_equiv
    (alternatingStarCoreCenterEquiv h (by decide) eA) hz
  have heven : Q'.map f ≤ alternatingGroup (Fin 7) := by
    rintro _ ⟨g,hg,rfl⟩
    apply seven_cover_even_of_fixed_center le_sup_left hEX cover eCore f hfmark g
    intro z hz'
    exact pCoreNormalizerAction_fixes_center_of_image X K Q
      (fun k hk => d.planeParabolicCore_normalized hI (map_subtype_le _ hk))
      (isPGroup_pCoreIn 2 _) hz hcenter (inclusion hEX g) hg z hz'
  let : W.Normal := normal_subgroupOf_of_le_normalizer hEU
  let := U_elementary d hI hfit hXI
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hUE
  let j : W ≃* U X ZS := subgroupOfEquivOfLe hUE
  let t := BinaryPermutation.coreEquivNatural (Fin 7) (by decide)
  let F : W ≃* Multiplicative (BinaryPermutation.core (Fin 7)) :=
    j.trans (A.trans t.symm.toAddEquiv.toMultiplicative)
  have hF (a : E) (w : W) : (F (MulAut.conjNormal a w)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 7) (f a) (F w).toAdd := by
    apply t.injective
    change t (t.symm (A (j (MulAut.conjNormal a w))).toAdd) =
      t (BinaryPermutation.coreRepresentation (Fin 7) (f a)
        (t.symm (A (j w)).toAdd))
    rw [t.apply_symm_apply, BinaryPermutation.coreEquivNatural_equivariant,
      t.apply_symm_apply]
    exact hf a (j w)
  have hkW : f.ker = centralizer (W : Set E) := by
    rw [hker]
    ext a
    constructor
    · intro ha w hw
      exact Subtype.ext (ha w hw)
    · intro ha u hu
      exact congrArg E.subtype (ha ⟨u,hUE hu⟩ hu)
  have hJ := ChapterB.Offenders.thompson_le_kernel_of_even_core_action (Or.inr rfl)
    W Q' (fun _ hw => U_le_QI d hI hfit hXI hw) f hkW F hF heven
  let L := X.subgroupOf E
  let : L.Normal := normal_subgroupOf_of_le_normalizer hEX
  have hgen : L ⊔ Q' = ⊤ := by
    rw [←subgroupOf_sup (show X ≤ E from le_sup_left)
      (show Q ≤ E from le_sup_right),subgroupOf_self]
  have hquot : IsPGroup 2 (E ⧸ L) := isPGroup_quotient_of_sup_eq_top L Q'
    ((isPGroup_pCoreIn 2 _).comap_subtype) hgen
  have hJcore' := twoGroup_le_pCore_of_normal_core_commutator L f.ker
    (elementaryAbelianMaxJ Q') hquot
    (seven_cover_kernel_commutator le_sup_left hEX cover f hfmark)
    (((isPGroup_pCoreIn 2 _).comap_subtype).to_le (sSup_le fun _ hA => hA.1)) hJ
  have hJcore : elementaryAbelianMaxJ Q ≤ E.pCoreIn 2 := by
    have hh := map_mono (f := E.subtype) hJcore'
    rw [←elementaryAbelianMaxJ_map_injective E.subtype E.subtype_injective,
      map_subgroupOf_eq_of_le (show Q ≤ E from le_sup_right)] at hh
    exact hh
  exact d.planeParabolicCore_thompson_not_le_core hI hout
    ((extension_core_le_seed_kernel d hI hXI hn hKX).trans inf_le_left) hJcore


/-- Both central covers of the original seven-letter row are excluded. -/
theorem normalized_originalSeven_false
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (s : Normalized H M I X)
    (hc : OriginalSevenCoordinates X ((M ⊓ I).pCoreIn 2) ZS) : False := by
  have hz := normalized_originalSeven_center_three d horbit hI hfit hcore s hc
  let h := normalized_component_input (hsource := hsource) hI hcore s
  obtain ⟨e,A,hm,hnU,hA⟩ := hc
  let eA : starImage X ((M ⊓ I).pCoreIn 2) X ≃* alternatingGroup (Fin 7) :=
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr hm)
  have hn := alternating_component_normalized (hsource := hsource) hI s.toSelected
    (by omega) (Or.inr rfl) (alternatingStarCoreCenterEquiv h (by decide) eA)
  have hout := alternating_star_not_le_partner d horbit hI hcore s (Or.inr rfl) eA
  have hK := alternating_star_residual_le_M1 d hI hcore s (Or.inr rfl) eA
  exact originalSeven_false_of_cubic_center d hI hfit s.component.1 hn hout
    (hK.trans inf_le_left) ⟨e,A,hm,hnU,hA⟩ h hz

/-- The same selected source component and full moved section now have only
an A₆ star image with cubic core center and binary symplectic ratio. -/
theorem exists_source_cubicSymplectic_component
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃* ChosenGeometry.Wreath))
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hno : ∀ Y : Subgroup I, ¬ ChapterC.IsChiBlockIn Y)
    (hNI : ¬ M ⊓ I ≤ Mc ⊓ I)
    (ha : letI := hsource.prepared.elementary;
      Nonempty (internalActionImage M V hsource.prepared.normalized ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∨
      SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized))
    (hi : OmegaAction.PlaneInverter hsource ZS) :
    ∃ X : Subgroup G, Normalized H M I X ∧
      let R := (M ⊓ I).pCoreIn 2
      let ρ := starRepresentation X R
      let J := offenderSubgroup ρ
      starImage X R X ≤ J ∧
        ∃ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
            (ρ.comp J.subtype) ((starImage X R X).subgroupOf J),
          Nonempty (starImage X R X ≃* alternatingGroup (Fin 6)) ∧
          Nat.card (center (X ⧸ pCore 2 X)) = 3 ∧
          quadraticRatio c.sectionData.action = 2 / 3 := by
  obtain ⟨X,selection,hCJ,c,hz,hc⟩ := exists_source_cubic_center_component
    d hquotient horbit hI hfit hno hNI ha hi
  refine ⟨X,selection,hCJ,c,?_⟩
  rcases hc with ⟨_,_,hU,_⟩ | hs
  · let := hsource.prepared.elementary
    have ho := OmegaAction.omega_of_restricted_actions d hI ha hNI
    obtain ⟨eNI⟩ := OmegaAction.intersection_image_equiv_of_omega d hI hNI ho hi
    obtain ⟨f,hf,hker⟩ := OmegaAction.exists_symmetricThree_action_of_image_equiv eNI
    have hcore := d.intersection_core_eq_of_centralizes hI
      (intersection_core_centralizes_of_symmetricThree f hf hker)
    exact (normalized_originalSeven_false d horbit hI hfit hcore selection hU).elim
  · exact hs

/-- The remaining action is the literal marked binary symplectic action;
the original full moved section and all its source clauses are unchanged. -/
theorem normalized_component_cubicSymplectic_action
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (selection : Normalized H M I X)
    (hno : ∀ Y : Subgroup I, ¬ ChapterC.IsChiBlockIn Y)
    (hCJ : starImage X ((M ⊓ I).pCoreIn 2) X ≤
      offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      ((starRepresentation X ((M ⊓ I).pCoreIn 2)).comp
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))).subtype)
      ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))))
    (hc : RemainingExceptionalActionCase
      ((starRepresentation X ((M ⊓ I).pCoreIn 2)).comp
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))).subtype)
      ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))) c.sectionData) :
    Nonempty (MarkedActionEquiv c.sectionData.action
      (offenderSubgroup c.sectionData.action)
      ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))))
      (symplecticNatural (k := ZMod 2) 2)
      (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)))) ∧
      Nat.card (center (X ⧸ pCore 2 X)) = 3 ∧
      quadraticRatio c.sectionData.action = 2 / 3 := by
  rcases normalized_component_natural_or_cubicSymplectic
    d horbit hI hfit hcore selection hCJ c hc with hn | hs
  · have hU := normalized_natural_originalSeven_coordinates
      d horbit hI hfit hcore selection hno hCJ c.sectionData hn
    exact (normalized_originalSeven_false d horbit hI hfit hcore selection hU).elim
  · have hne : (2 / 3 : ENNReal) ≠ 1 := by
      intro h
      have hh := (ENNReal.div_eq_one_iff (a := 2) (b := 3)
        (by norm_num) (by norm_num)).mp h
      norm_num at hh
    refine ⟨?_,hs.2⟩
    cases hc with
    | irreducible hp hf hi hr he =>
      cases hr with
      | symplecticTwo a hr => exact ⟨a⟩
      | g2 F hn hg a ho hr => exact (hne (hs.2.2.symm.trans hr)).elim
      | g2Two a ho hr => exact (hne (hs.2.2.symm.trans hr)).elim
      | symmetric n hn a ho hr => exact (hne (hs.2.2.symm.trans hr)).elim
      | alternatingSix hg a ho hr => exact (hne (hs.2.2.symm.trans hr)).elim
      | alternatingSeven hg ht a hd ho hr => exact (hne (hs.2.2.symm.trans hr)).elim
      | tripleSix hg a hr => exact (hne (hs.2.2.symm.trans hr)).elim

/-- The original source produces a marked binary symplectic action on the
same component's full moved section, with its cubic central cover retained. -/
theorem exists_source_marked_cubicSymplectic_component
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃* ChosenGeometry.Wreath))
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hno : ∀ Y : Subgroup I, ¬ ChapterC.IsChiBlockIn Y)
    (hNI : ¬ M ⊓ I ≤ Mc ⊓ I)
    (ha : letI := hsource.prepared.elementary;
      Nonempty (internalActionImage M V hsource.prepared.normalized ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∨
      SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized))
    (hi : OmegaAction.PlaneInverter hsource ZS) :
    ∃ X : Subgroup G, Normalized H M I X ∧
      let R := (M ⊓ I).pCoreIn 2
      let ρ := starRepresentation X R
      let J := offenderSubgroup ρ
      starImage X R X ≤ J ∧
        ∃ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
            (ρ.comp J.subtype) ((starImage X R X).subgroupOf J),
          RemainingExceptionalActionCase (ρ.comp J.subtype)
            ((starImage X R X).subgroupOf J) c.sectionData ∧
          Nonempty (MarkedActionEquiv c.sectionData.action
            (offenderSubgroup c.sectionData.action) ((starImage X R X).subgroupOf J)
            (symplecticNatural (k := ZMod 2) 2)
            (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)))) ∧
          Nat.card (center (X ⧸ pCore 2 X)) = 3 ∧
          quadraticRatio c.sectionData.action = 2 / 3 := by
  obtain ⟨X,selection,hCJ,c,hc,_⟩ := exists_source_component_frontier
    d hquotient horbit hI hfit hno hNI ha hi
  let := hsource.prepared.elementary
  have ho := OmegaAction.omega_of_restricted_actions d hI ha hNI
  obtain ⟨eNI⟩ := OmegaAction.intersection_image_equiv_of_omega d hI hNI ho hi
  obtain ⟨f,hf,hker⟩ := OmegaAction.exists_symmetricThree_action_of_image_equiv eNI
  have hcore := d.intersection_core_eq_of_centralizes hI
    (intersection_core_centralizes_of_symmetricThree f hf hker)
  exact ⟨X,selection,hCJ,c,hc,
    normalized_component_cubicSymplectic_action d horbit hI hfit hcore selection hno hCJ c hc⟩

end CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
