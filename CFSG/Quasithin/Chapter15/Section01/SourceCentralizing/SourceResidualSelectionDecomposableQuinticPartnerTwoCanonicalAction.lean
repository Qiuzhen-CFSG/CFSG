module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticMaximalSectionOffender
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoIrreducible
public import Theory.Representation.BinaryConjugationSection.ConjugateSpan
public import Theory.Representation.BinaryConjugationSection.CommutatorImage
public import Theory.Representation.BinaryConjugationSection.ImageDimensions
public import Theory.Representation.BinaryConjugationSection.DualOffenderIndex
public import Theory.Representation.BinaryOffender.FaithfulRankOne
public import Theory.Representation.BinaryOffender.NormalizerImage

/-!
# The canonical irreducible original quintic action

The original moving normal span is all of F. The already constructed
maximal centralizing section therefore has the literal numerator F and
canonical denominator D. Its faithful image is irreducible, and the
original V-image is a quadratic offender whose moved space is exactly
the image of E. When the partner module has order two, that image has
binary dimension at most three.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

/-- The actual canonical F/D action, with the original V-image and its
literal kernel, is irreducible and has a moved subspace of dimension at most three. -/
theorem PreparedChosenModule.decomposable_five_partner_two_core_or_canonical_action
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      Nat.card (localModule T Mc) = 2 →
      let E := thompsonFixed T V
      let C := centralizer (localModule T Mc : Set G)
      let F := conjugateSpanBy E C
      let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
      V ≤ Mc.pCoreIn 2 ∨
        (D < F ∧ localModule T Mc ≤ D ∧ D ≤ centralizer (V : Set G) ∧
          Mc ≤ normalizer (D : Set G) ∧
          ∃ he : IsElementaryAbelian 2 F,
            letI := he
            ∃ ρ : Representation (ZMod 2) Mc (Additive (F ⧸ D.subgroupOf F)),
            ∃ dF : BinaryConjugationSection Mc F D ρ,
              Function.Injective (Representation.BinaryOffender.imageRepresentation ρ) ∧
              (Representation.BinaryOffender.actionHom ρ).ker.map Mc.subtype =
                commutatorPreimage Mc F D ∧
              Nat.card (actionSubgroup ρ (V.subgroupOf Mc)) =
                (commutatorPreimage Mc F D).relIndex V ∧
              pCore 2 (Representation.BinaryOffender.actionImage ρ) = ⊥ ∧
              IsOffender (Representation.BinaryOffender.imageRepresentation ρ)
                (actionSubgroup ρ (V.subgroupOf Mc)) ∧
              IsIrreducible ρ ∧
              IsIrreducible (Representation.BinaryOffender.imageRepresentation ρ) ∧
              IsQuadratic (Representation.BinaryOffender.imageRepresentation ρ)
                (actionSubgroup ρ (V.subgroupOf Mc)) ∧
              dF.imageSpace E = subspaceCommutator
                (Representation.BinaryOffender.imageRepresentation ρ) ⊤
                (actionSubgroup ρ (V.subgroupOf Mc)) ∧
              Module.finrank (ZMod 2) (dF.imageSpace E) ≤ 3) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  let E := thompsonFixed T V
  let Uc := localModule T Mc
  let C := centralizer (Uc : Set G)
  let F := conjugateSpanBy E C
  let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
  let W := F ⊓ commutatorPreimage (T : Subgroup G) (T : Subgroup G) D
  let H := conjugateSpanBy W Mc
  rcases h.decomposable_five_core_or_maximal_reduced_section
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive with
    hcore | ⟨_, _, _, _, _, hHF, hnH, _, hmove, _⟩
  · exact Or.inl hcore
  obtain ⟨hVH, hHeq⟩ := h.decomposable_five_moving_normal_span
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive H hHF hnH hmove
  have hVF : ⁅V,F⁆ = E := by simpa only [hHeq] using hVH
  have hpacket := h.decomposable_five_core_or_maximal_section_offender
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  rcases hpacket with hcore | hpacket
  · exact Or.inl hcore
  change D<W ∧ D<F ∧ D≤centralizer (V:Set G) ∧ Mc≤normalizer (D:Set G) ∧
    D≤H ∧ H≤F ∧ Mc≤normalizer (H:Set G) ∧
      (∃ he : IsElementaryAbelian 2 H, letI := he
        ∃ ρ : Representation (ZMod 2) Mc (Additive (H ⧸ D.subgroupOf H)),
          Nonempty (BinaryConjugationSection Mc H D ρ) ∧
          Function.Injective (Representation.BinaryOffender.imageRepresentation ρ) ∧
          (Representation.BinaryOffender.actionHom ρ).ker.map Mc.subtype =
            commutatorPreimage Mc H D ∧
          Nat.card (actionSubgroup ρ (V.subgroupOf Mc)) =
            (commutatorPreimage Mc H D).relIndex V ∧
          pCore 2 (Representation.BinaryOffender.actionImage ρ) = ⊥ ∧
          IsOffender (Representation.BinaryOffender.imageRepresentation ρ)
            (actionSubgroup ρ (V.subgroupOf Mc))) at hpacket
  rw [hHeq] at hpacket
  obtain ⟨_,hDF,hDC,hnD,_,_,_,heF,ρ,⟨dF⟩,hfaith,hker,hcard,hcore,hoff⟩ := hpacket
  let : IsElementaryAbelian 2 F := heF
  let σ := Representation.BinaryOffender.imageRepresentation ρ
  let A := actionSubgroup ρ (V.subgroupOf Mc)
  have hUE : Uc≤E := (h.decomposable_five_partner_control
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).2.2
  have hEF : E≤F := le_conjugateSpanBy E C
  have hUCV : Uc≤centralizer (V:Set G) := (hUE.trans inf_le_left).trans V.le_centralizer
  have hVC : V≤C := le_centralizer_iff.mpr hUCV
  have hCMc : C≤Mc := localModule_centralizer_le_partner T Mc hu
  have hVMc : V≤Mc := hVC.trans hCMc
  have hUD : Uc≤D := by
    intro x hx
    refine ⟨⟨x,dF.section_le (hEF (hUE hx))⟩,?_,rfl⟩
    intro n
    have hx' := le_normalizer_iff.mp
      (le_normalizer_conjugateSpanBy (centralInvolutions T) Mc) n n.property x hx
    exact ⟨hEF (hUE hx'),hUCV hx'⟩
  have hpositive : 0 < fixedCodim σ A := fixedCodim_pos_of_faithful σ hfaith hoff.1.1
  have hcodim := fixedCodim_add_finrank σ A
  have hdimpos : 0 < Module.finrank (ZMod 2) (Additive (F ⧸ D.subgroupOf F)) := by
    change fixedCodim σ A + Module.finrank (ZMod 2) (fixedSpace σ A) =
      Module.finrank (ZMod 2) (Additive (F ⧸ D.subgroupOf F)) at hcodim
    omega
  let : Nontrivial (Additive (F ⧸ D.subgroupOf F)) :=
    (Module.finrank_pos_iff (R:=ZMod 2) (M:=Additive (F ⧸ D.subgroupOf F))).mp hdimpos
  have hirr : IsIrreducible ρ := (h.decomposable_five_canonical_section_irreducible
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).2 ρ dF
  have hquad : IsQuadratic σ A := by
    apply dF.quadratic_of_commutator_bounds σ
      (Representation.BinaryOffender.actionHom ρ) V E hVF.le
    exact (commutator_eq_bot_iff_le_centralizer.mpr
      (V.le_centralizer.trans (centralizer_le inf_le_left))).le.trans bot_le
  have himage : dF.imageSpace E = subspaceCommutator σ ⊤ A := by
    change _ = subspaceCommutator σ ⊤ ((V.subgroupOf Mc).map
      (Representation.BinaryOffender.actionHom ρ))
    rw [←subspaceCommutator_comp_map]
    change _ = subspaceCommutator ρ ⊤ (V.subgroupOf Mc)
    have hh := dF.imageSpace_commutator V F hVMc le_rfl
    have hself : dF.imageSpace F = ⊤ := dF.imageSpace_self
    simpa only [hVF,hself] using hh
  have hindex : Uc.relIndex E = 8 := by
    have hm := (Uc.subgroupOf E).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hUE).toEquiv] at hm
    change Uc.relIndex E * Nat.card Uc = Nat.card E at hm
    rw [hcU,s.fixed_card] at hm
    omega
  have hbound : Nat.card (dF.imageSpace E)≤8 := by
    rw [dF.imageSpace_card_eq_relIndex E hEF]
    exact (relIndex_le_of_le_left hUD index_ne_zero_of_finite).trans_eq hindex
  rw [Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_zmod] at hbound
  have hdim : Module.finrank (ZMod 2) (dF.imageSpace E)≤3 :=
    (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hbound
  exact Or.inr ⟨hDF,hUD,hDC,hnD,heF,ρ,dF,hfaith,hker,hcard,hcore,hoff,hirr,
    imageRepresentation_isIrreducible ρ hirr,hquad,himage,hdim⟩

end CFSG.Quasithin.Chapter15.Section01
