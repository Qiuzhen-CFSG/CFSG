module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EqualityRow.SevenCoordinates
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EqualityRow.LinearOrthogonal
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.OriginalSevenExclusion

/-!
# Excluding the original symmetric-five/seven moved action

For centerless core quotient, full natural coordinates extend the actual
U action from XR to XQI.  The rank-two residual and odd-normalizer bound
force QI to act by even permutations; B.3.2 then puts its Thompson subgroup
in the two-core of XQI, contradicting the original normalizer control.
For cubic core center, C.2.6 places the central preimage in M and the
rank-two residual contradiction closes the row.  The terminal theorem
takes the literal symmetric B.5 action, without residual-identity inputs.

Source: Aschbacher--Smith, proof of 15.2.23, printed pp.1116--1117,
refs/quasithin.pdf. The original U, QI and star markings are retained.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Section01 ComponentCatalogue PlaneUniquenessPreceding PlaneUniquenessPreceding.LinearThree TerminalLinear
open ChapterD ChapterD.UniqueFactor
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}

/-- The original faithful seven-letter action contradicts QI Thompson control. -/
theorem ResidualInput.originalSeven_false_of_faithful
    (r : ResidualInput hsource H B)
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G)) (hout : ¬ X ≤ Mc)
    (hKX : (pResidual 2 H).map H.subtype ≤ X)
    (hc : OriginalSevenCoordinates X ((M ⊓ I).pCoreIn 2) ⁅V,B⁆)
    (hfaith : X ⊓ centralizer (U X ⁅V,B⁆ : Set G) ≤ X.pCoreIn 2) : False := by
  obtain ⟨e,A,hmark,hnU,hA⟩ := hc
  let R := (M ⊓ I).pCoreIn 2
  let Q := QI H T ⁅V,B⁆
  let E := X ⊔ Q
  let W := (U X ⁅V,B⁆).subgroupOf E
  let Q' := Q.subgroupOf E
  let K := residual H
  let K' := K.subgroupOf E
  have hQI : Q ≤ I := (pCoreIn_le 2 _).trans
    ((r.residual_sup_planeCentralizer_le hI).trans inf_le_right)
  have hEI : E ≤ I := sup_le hXI hQI
  have hUX : U X ⁅V,B⁆ ≤ X := by
    apply le_normalizer_iff_commutator_le_right.mp
    exact ((r.plane_span_le_planeParabolicCore hI hfit hXI).trans hQI).trans hn
  have hUE : U X ⁅V,B⁆ ≤ E := hUX.trans le_sup_left
  have hEU : E ≤ normalizer (U X ⁅V,B⁆ : Set G) := EqualityRow.Linear.U_normalized r hI hn
  have hEX : E ≤ normalizer (X : Set G) := hEI.trans hn
  let eA : starImage X R X ≃* alternatingGroup (Fin 7) :=
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr hmark)
  let q : X →* alternatingGroup (Fin 7) := eA.toMonoidHom.comp (toStarImage X R)
  have hq : Function.Surjective q := eA.surjective.comp (toStarImage_surjective X R)
  let c : BinaryConjugationSection X (U X ⁅V,B⁆) ⊥
      ((BinaryPermutation.alternatingNaturalRepresentation (Fin 7)).comp q) := {
    section_le := hUX
    kernel_le := bot_le
    normalized := le_sup_left.trans hnU
    coordinates := A.toMonoidHom
    onto := A.surjective
    kernel_eq := by rw [A.toMonoidHom.ker_eq_bot_iff.mpr A.injective,bot_subgroupOf]
    equivariant := fun x u => hA ⟨x,mem_sup_left x.property⟩ u _ rfl }
  obtain ⟨f,hf,hfx⟩ := BinaryConjugationSection.exists_seven_normalizer_action
    X (U X ⁅V,B⁆) E le_sup_left hEU hEX q hq c
  have hker : f.ker = (centralizer (U X ⁅V,B⁆ : Set G)).subgroupOf E :=
    BinaryConjugationCoordinates.model_kernel E (U X ⁅V,B⁆) hEU
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
    exact r.planeParabolicCore_normalized hI (map_subtype_le _ hk)
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
      exact (primeRank_congr 3 (subgroupOfEquivOfLe
        (show K ≤ E from hKX.trans le_sup_left))).trans r.residual_rank_two
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
  let := EqualityRow.Linear.U_elementary r hI hfit hXI
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hUE
  let j : W ≃* U X ⁅V,B⁆ := subgroupOfEquivOfLe hUE
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
    W Q' (fun _ hw => EqualityRow.Linear.U_le_QI r hI hfit hXI hw) f hkW F hF heven
  have hC : E ⊓ centralizer (U X ⁅V,B⁆ : Set G) ≤ E.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (EqualityRow.Linear.extension_kernel_isTwoGroup r hI hXI hn hfaith) inf_le_left
      ((le_inf E.le_normalizer
        (hEU.trans (normalizer_le_normalizer_centralizer _))).trans
        inf_normalizer_le_normalizer_inf)
  have hJcore : elementaryAbelianMaxJ Q ≤ E.pCoreIn 2 := by
    have hh := map_mono (f := E.subtype) hJ
    rw [←elementaryAbelianMaxJ_map_injective E.subtype E.subtype_injective,
      map_subgroupOf_eq_of_le (show Q ≤ E from le_sup_right),hker,
      subgroupOf_map_subtype] at hh
    exact hh.trans (by simpa only [inf_comm] using hC)
  exact r.planeParabolicCore_thompson_not_le_core hI hout
    ((EqualityRow.Linear.extension_core_le_seed_kernel r hI hXI hn hKX).trans inf_le_left) hJcore

/-- Centerless original A₇ core quotient is excluded on the same U and QI. -/
theorem ResidualInput.normalized_originalSeven_false_of_center_one_of_eq
    (r : ResidualInput hsource H B)
    (heq : partnerSpan H Mc = residual H)
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (s : Normalized H M I X)
    (hc : OriginalSevenCoordinates X ((M ⊓ I).pCoreIn 2) ⁅V,B⁆)
    (hz : Nat.card (center (X ⧸ pCore 2 X)) = 1) : False := by
  let R := (M ⊓ I).pCoreIn 2
  let h := normalized_component_input (hsource := hsource) hI hcore s
  obtain ⟨e,A,hm,hnU,hA⟩ := hc
  let eA : starImage X R X ≃* alternatingGroup (Fin 7) :=
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr hm)
  have hn := alternating_component_normalized (hsource := hsource) hI s.toSelected
    (by omega) (Or.inr rfl) (alternatingStarCoreCenterEquiv h (by decide) eA)
  have hout := r.alternating_component_not_le_partner_of_eq heq hI hcore s (Or.inr rfl)
    (alternatingStarCoreCenterEquiv h (by decide) eA)
  have hK := r.alternating_star_residual_le_M1 hI hcore s (Or.inr rfl) eA
  have hi : Function.Injective (coreToStar s.radical_normalizes) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    exact bot_unique ((coreToStar_ker_central_from_source h).trans_eq
      ((eq_bot_iff_card _).mpr hz))
  have hf : X ⊓ centralizer (U X ⁅V,B⁆ : Set G) ≤ X.pCoreIn 2 := by
    intro x hx
    have hk : (⟨x,mem_sup_left hx.1⟩ : (X ⊔ R : Subgroup G)) ∈ starKernel X R :=
      (show OriginalSevenCoordinates X R ⁅V,B⁆ from ⟨e,A,hm,hnU,hA⟩).centralizer_eq_starKernel ▸ hx.2
    have hq : QuotientGroup.mk' (pCore 2 X) ⟨x,hx.1⟩ = 1 := by
      apply hi
      rw [map_one,coreToStar_mk]
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff _).mpr hk
    exact mem_map_of_mem X.subtype ((QuotientGroup.eq_one_iff _).mp hq)
  exact r.originalSeven_false_of_faithful hI hfit s.component.1 hn hout
    (hK.trans inf_le_left) ⟨e,A,hm,hnU,hA⟩ hf

/-- Both possible core centers are excluded for the original seven-letter coordinates. -/
theorem ResidualInput.normalized_originalSeven_false_of_eq
    (r : ResidualInput hsource H B) (heq : partnerSpan H Mc = residual H)
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (hno : ∀ Y : Subgroup I, ¬ ChapterC.IsChiBlockIn Y)
    (s : Normalized H M I X)
    (hc : OriginalSevenCoordinates X ((M ⊓ I).pCoreIn 2) ⁅V,B⁆) : False := by
  let h := normalized_component_input (hsource := hsource) hI hcore s
  rcases coreQuotient_center_card_from_source h with hz | hz
  · exact r.normalized_originalSeven_false_of_center_one_of_eq heq hI hfit hcore s hc hz
  obtain ⟨e,A,hm,hnU,hA⟩ := hc
  let eA : starImage X ((M ⊓ I).pCoreIn 2) X ≃* alternatingGroup (Fin 7) :=
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr hm)
  have hn := alternating_component_normalized (hsource := hsource) hI s.toSelected
    (by omega) (Or.inr rfl) (alternatingStarCoreCenterEquiv h (by decide) eA)
  exact r.normal_component_false_of_cubic_core_center hI hfit hcore hno s.component.1 hn
    ((r.alternating_star_residual_le_M1 hI hcore s (Or.inr rfl) eA).trans inf_le_left) hz

/-- The literal B.5 symmetric-five/seven action is impossible on the original moved section. -/
theorem ResidualInput.normalized_symmetric_false_of_eq
    (r : ResidualInput hsource H B)
    (heq : partnerSpan H Mc = residual H)
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (selection : Normalized H M I X)
    (hno : ∀ Y : Subgroup I, ¬ ChapterC.IsChiBlockIn Y)
    (hCJ : starImage X ((M ⊓ I).pCoreIn 2) X ≤
  offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))
    (s : MovedSection ((starRepresentation X ((M ⊓ I).pCoreIn 2)).comp
  (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))).subtype)
  ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
    (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))))
    (hi : IsIrrPlus
  ((starRepresentation X ((M ⊓ I).pCoreIn 2)).comp
    (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))).subtype)
  ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
    (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))) s.space.toSubmodule)
    {n : ℕ} (hn : n = 5 ∨ n = 7)
    (a : MarkedActionEquiv s.action (offenderSubgroup s.action)
  ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
    (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))))
  (BinaryPermutation.naturalRepresentation (Fin n)) (alternatingGroup (Fin n)))
    (hr : quadraticRatio s.action = 1) : False := by
  have hc : OriginalSevenCoordinates X ((M ⊓ I).pCoreIn 2) ⁅V,B⁆ :=
    r.normalized_symmetric_originalSeven_coordinates_of_eq heq hI hfit hcore
      selection hno hCJ s hi hn a hr
  exact r.normalized_originalSeven_false_of_eq heq hI hfit hcore hno selection hc


end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
