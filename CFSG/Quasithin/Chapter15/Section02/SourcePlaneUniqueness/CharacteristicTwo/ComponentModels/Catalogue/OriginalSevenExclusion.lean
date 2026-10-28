module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.OriginalSeven
public import Theory.Representation.BinaryConjugationSection.SevenNormalizer
public import Theory.Representation.BinaryConjugationCoordinates
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingSevenNormalAction
public import CFSG.Quasithin.ChapterB.Section03.Offenders.OddConjugation

/-!
# The original seven-letter action forces a cubic central cover

Extend the natural coordinates on the whole original U from XR to XQI,
where QI = O₂(KS). If C_X(U) is contained in O₂(X), the original rank-two
residual K has rank-two image on U. Since K normalizes QI, the odd
normalizer bound in S₇ forces QI to act by even permutations.

B.3.2(4) then puts the Thompson subgroup J(QI) in the literal action
kernel. The normal-supplement kernel theorem and the original Sylow
geometry put this kernel, and hence J(QI), in O₂(XQI) ≤ QI. This
contradicts the original Thompson normalizer control.

When the center of X/O₂(X) is trivial, the original core-to-star map is
injective and supplies the required kernel bound. Thus the source consumer
retains the same selected component, full moved section and original
markings, but both surviving alternatives now have cubic core centers.
The cubic seven-letter and cubic symplectic exclusions, full KS placement
and final 15.2.23 assembly remain open.

Source: Aschbacher--Smith original 15.2.23, printed pp.1115--1117,
and B.3.2(4), printed p.83; refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
open Section01 PlaneUniquenessPreceding PlaneUniquenessPreceding.LinearThree TerminalLinear
open ChapterD ChapterD.UniqueFactor
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The original seven-letter action with two-core kernel contradicts the
Thompson normalizer control on the actual QI = O₂(KS). -/
theorem originalSeven_false_of_faithful
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G)) (hout : ¬ X ≤ Mc)
    (hKX : (pResidual 2 H).map H.subtype ≤ X)
    (hc : OriginalSevenCoordinates X ((M ⊓ I).pCoreIn 2) ZS)
    (hfaith : X ⊓ centralizer (U X ZS : Set G) ≤ X.pCoreIn 2) : False := by
  obtain ⟨e,A,hmark,hnU,hA⟩ := hc
  let R := (M ⊓ I).pCoreIn 2
  let Q := QI H T ZS
  let E := X ⊔ Q
  let W := (U X ZS).subgroupOf E
  let Q' := Q.subgroupOf E
  let K := (pResidual 2 H).map H.subtype
  let K' := K.subgroupOf E
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
  have hKker : IsPGroup 2 (f.comp K'.subtype).ker := by
    let j : (f.comp K'.subtype).ker →* X.pCoreIn 2 :=
      ((E.subtype.comp K'.subtype).comp (f.comp K'.subtype).ker.subtype).codRestrict _ (by
        intro k
        apply hfaith
        refine ⟨hKX k.val.property,?_⟩
        exact hker.le (show (k.val.val : E) ∈ f.ker from k.property))
    exact (isPGroup_pCoreIn 2 X).of_injective j (by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : X.pCoreIn 2 => (z : G)) hab)
  have hKQ : K' ≤ normalizer (Q' : Set E) := by
    rw [←subgroupOf_normalizer_eq (show Q ≤ E from le_sup_right)]
    intro k hk
    exact d.planeParabolicCore_normalized hI (map_subtype_le _ hk)
  have heven : Q'.map f ≤ alternatingGroup (Fin 7) := by
    let g := f.subgroupMap K'
    have hg : IsPGroup 2 g.ker := by
      have he : g.ker = (f.comp K'.subtype).ker := by ext k; exact Subtype.ext_iff
      rw [he]
      exact hKker
    have hcop : Nat.Coprime 3 (Nat.card g.ker) := by
      obtain ⟨n,hn⟩ := hg.exists_card_eq
      rw [hn]
      exact (by decide : Nat.Coprime 3 2).pow_right n
    have hr : primeRank 3 K' = 2 := by
      rw [primeRank_congr 3 (subgroupOfEquivOfLe (hKX.trans le_sup_left)),residual_rank_two d]
    have hl : 2 ≤ primeRank 3 (K'.map f) :=
      hr ▸ primeRank_le_of_coprime_ker 3 g hcop
    have hnorm : K'.map f ≤ normalizer (Q'.map f : Set (Equiv.Perm (Fin 7))) :=
      (map_mono hKQ).trans (le_normalizer_map f)
    by_contra hh
    have hb := Theory.SpecificGroups.SymmetricSeven.OddNormalizers.normalizer_rank
      (Q'.map f) (((isPGroup_pCoreIn 2 _).comap_subtype).map f) hh
    have hb' := hl.trans ((primeRank_mono 3 hnorm).trans hb)
    omega
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
  have hC : E ⊓ centralizer (U X ZS : Set G) ≤ E.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (extension_kernel_isTwoGroup d hI hXI hn hfaith) inf_le_left
      ((le_inf E.le_normalizer
        (hEU.trans (normalizer_le_normalizer_centralizer _))).trans
        inf_normalizer_le_normalizer_inf)
  have hJcore : elementaryAbelianMaxJ Q ≤ E.pCoreIn 2 := by
    have hh := map_mono (f := E.subtype) hJ
    rw [←elementaryAbelianMaxJ_map_injective E.subtype E.subtype_injective,
      map_subgroupOf_eq_of_le (show Q ≤ E from le_sup_right),hker,
      subgroupOf_map_subtype] at hh
    exact hh.trans (by simpa only [inf_comm] using hC)
  exact d.planeParabolicCore_thompson_not_le_core hI hout
    ((extension_core_le_seed_kernel d hI hXI hn hKX).trans inf_le_left) hJcore

/-- A seven-letter component with centerless original core quotient is
excluded on the original U and QI, without reconstructing a block. -/
theorem normalized_originalSeven_false_of_center_one
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (s : Normalized H M I X)
    (hc : OriginalSevenCoordinates X ((M ⊓ I).pCoreIn 2) ZS)
    (hz : Nat.card (center (X ⧸ pCore 2 X)) = 1) : False := by
  let R := (M ⊓ I).pCoreIn 2
  let h := normalized_component_input (hsource := hsource) hI hcore s
  obtain ⟨e,A,hm,hnU,hA⟩ := hc
  let eA : starImage X R X ≃* alternatingGroup (Fin 7) :=
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr hm)
  have hn := alternating_component_normalized (hsource := hsource) hI s.toSelected
    (by omega) (Or.inr rfl) (alternatingStarCoreCenterEquiv h (by decide) eA)
  have hout := alternating_star_not_le_partner d horbit hI hcore s (Or.inr rfl) eA
  have hK := alternating_star_residual_le_M1 d hI hcore s (Or.inr rfl) eA
  have hi : Function.Injective (coreToStar s.radical_normalizes) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    exact bot_unique ((coreToStar_ker_central_from_source h).trans_eq
      ((eq_bot_iff_card _).mpr hz))
  have hf : X ⊓ centralizer (U X ZS : Set G) ≤ X.pCoreIn 2 := by
    intro x hx
    have hk : (⟨x,mem_sup_left hx.1⟩ : (X ⊔ R : Subgroup G)) ∈ starKernel X R :=
      (show OriginalSevenCoordinates X R ZS from ⟨e,A,hm,hnU,hA⟩).centralizer_eq_starKernel ▸ hx.2
    have hq : QuotientGroup.mk' (pCore 2 X) ⟨x,hx.1⟩ = 1 := by
      apply hi
      rw [map_one,coreToStar_mk]
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff _).mpr hk
    exact mem_map_of_mem X.subtype ((QuotientGroup.eq_one_iff _).mp hq)
  exact originalSeven_false_of_faithful d hI hfit s.component.1 hn hout
    (hK.trans inf_le_left) ⟨e,A,hm,hnU,hA⟩ hf

/-- Any surviving original seven-letter row has a cubic central kernel;
the centerless alternative has been excluded by the QI offender argument. -/
theorem normalized_originalSeven_center_three
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (s : Normalized H M I X)
    (hc : OriginalSevenCoordinates X ((M ⊓ I).pCoreIn 2) ZS) :
    Nat.card (center (X ⧸ pCore 2 X)) = 3 := by
  rcases coreQuotient_center_card_from_source
      (normalized_component_input (hsource := hsource) hI hcore s) with hh | hh
  · exact (normalized_originalSeven_false_of_center_one d horbit hI hfit hcore s hc hh).elim
  · exact hh

/-- The original source now leaves only cubic central covers, with the same
selected component, full moved section, quotient maps and surviving actions. -/
theorem exists_source_cubic_center_component
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
          Nat.card (center (X ⧸ pCore 2 X)) = 3 ∧
          ((RemainingNaturalActionCase (ρ.comp J.subtype) ((starImage X R X).subgroupOf J) c.sectionData ∧
            FullSevenPermutationCoordinates c.sectionData ∧ OriginalSevenCoordinates X R ZS ∧
            (centralizer (U X ZS : Set G)).subgroupOf (X ⊔ R) = starKernel X R) ∨
            (Nonempty (starImage X R X ≃* alternatingGroup (Fin 6)) ∧
              Nat.card (center (X ⧸ pCore 2 X)) = 3 ∧
              quadraticRatio c.sectionData.action = 2 / 3)) := by
  obtain ⟨X,selection,hCJ,c,hc⟩ := exists_source_originalSeven_or_cubicSymplectic_component
    d hquotient horbit hI hfit hno hNI ha hi
  let := hsource.prepared.elementary
  have ho := OmegaAction.omega_of_restricted_actions d hI ha hNI
  obtain ⟨eNI⟩ := OmegaAction.intersection_image_equiv_of_omega d hI hNI ho hi
  obtain ⟨f,hf,hker⟩ := OmegaAction.exists_symmetricThree_action_of_image_equiv eNI
  have hcore := d.intersection_core_eq_of_centralizes hI
    (intersection_core_centralizes_of_symmetricThree f hf hker)
  refine ⟨X,selection,hCJ,c,?_,hc⟩
  rcases hc with ⟨hn,hcoords,hU,hkerU⟩ | hs
  · exact normalized_originalSeven_center_three d horbit hI hfit hcore selection hU
  · exact hs.2.1

end CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
