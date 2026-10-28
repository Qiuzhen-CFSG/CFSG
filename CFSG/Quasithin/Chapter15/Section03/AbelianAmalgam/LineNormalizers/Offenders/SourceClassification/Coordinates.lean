module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.SourceClassification
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorExtraction.Rows
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.AtlasPort.LinearGroups.SL2Order

/-!
# Whole fixed-quotient coordinates for the surviving SL₂ family

The full B.5.1 action comparison retains its natural rows on the actual
moved section. Embedded SL₃ and alternating-five sections contradict the
source prime-to-three marker bound. In the SL₂ row, the ratio-one offender
comparison and Sylow averaging prove that the moved section supplements the
whole fixed space. Its quotient is therefore the whole fixed quotient.
The separate B.5.6 symmetric-three branch gives the same coordinates from
its faithful two-dimensional moved module.

The original central extension is retained; no complement to its fixed
kernel is assumed. Field degree and the marked Thompson-normalizer comparison
remain unrestricted. The actual temporary-source consumer below supplies all
classification hypotheses and the marker bound from their existing producers.

Source: Aschbacher–Smith, B.4.2(1), B.5.1 and B.5.6, printed pp.86, 99–105,
and proof of 15.3.67, printed pp.1153–1154 (1 March 2004 manuscript).
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.SourceClassification
open BestReduction BestReduction.FullCoreTransfer ChapterB.QuasisimpleSource
  ChapterB.SourceInduction
open ChapterB.SourceInduction.FactorExtraction ChapterB.QuasisimpleSource.ExtensionConsequences
  ChapterB.SourceInduction.ComponentReduction.ProductGeometry
universe u v w z
variable {D : Type u} [Group D] {W : Type v}
  [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) D W}

private noncomputable def coordinatesOfImage
    {H : Type w} [Group H] {X : Type z} [AddCommGroup X] [Module (ZMod 2) X]
    {τ : Representation (ZMod 2) H X}
    (U : Subrepresentation ρ) (hs : U.toSubmodule ⊔ ρ.invariants = ⊤)
    (e : ActionEquiv (((fixed ρ).quotientImage U).toRepresentation.comp
      (⊤ : Subgroup D).subtype) τ) : CentralQuotientCoordinates ρ τ := by
  let I := (fixed ρ).quotientImage U
  have hI : I.toSubmodule = ⊤ := by
    have h := (Subrepresentation.quotientImage_eq_top_iff (fixed ρ) U).mpr
      (show ρ.invariants ⊔ U.toSubmodule = ⊤ by rw [sup_comm]; exact hs)
    exact congrArg Subrepresentation.toSubmodule h
  let i : I.toSubmodule ≃ₗ[ZMod 2] (W ⧸ ρ.invariants) :=
    LinearEquiv.ofBijective I.toSubmodule.subtype
      ⟨Subtype.val_injective, fun v => ⟨⟨v, hI.symm ▸ Submodule.mem_top⟩, rfl⟩⟩
  refine ⟨Subgroup.topEquiv.symm.trans e.groupEquiv, i.symm.trans e.linearEquiv, ?_⟩
  intro g v
  change e.linearEquiv (i.symm (ρ.invariants.mkQ (ρ g v))) =
    τ (e.groupEquiv ⟨g, mem_top _⟩) (e.linearEquiv (i.symm (ρ.invariants.mkQ v)))
  rw [← e.intertwines]
  congr 1
  apply i.injective
  rw [i.apply_symm_apply]
  change ρ.invariants.mkQ (ρ g v) =
    (fixed ρ).quotientRepresentation g (i (i.symm (ρ.invariants.mkQ v)))
  rw [i.apply_symm_apply]
  rfl

private theorem quasisimple_coordinates [Finite D] [Nontrivial D]
    [FiniteDimensional (ZMod 2) W] {J : Subgroup D}
    (d : MarkedNormalizer ρ J)
    (hP : Nat.Coprime 3 (Nat.card (subspaceKernel ρ d.marker ⊤)))
    {L : Subgroup D} [L.Normal]
    (c : ProjectiveLine.QuasisimpleSourceConclusion ρ L)
    (hj : offenderSubgroup ρ = ⊤) (hr : primeRank 3 D ≤ 1) :
    ∃ F : BinaryField, Nonempty (CentralQuotientCoordinates ρ (linearNatural F 2)) := by
  cases c.rank_one_action hr with
  | doubleThree F _ _ e _ _ =>
    exact (no_linearThree_section d hP F 2
      (L.subtype.comp e.groupEquiv.symm.toMonoidHom)
      (L.subtype_injective.comp e.groupEquiv.symm.injective)
      (RankOneDispatch.modelSection_of_moved c.sectionData e)).elim
  | irreducible _ _ _ hrow _ =>
    cases hrow with
    | linearThree F _ _ e _ =>
      exact (no_linearThree_section d hP F 1
        (L.subtype.comp e.groupEquiv.symm.toMonoidHom)
        (L.subtype_injective.comp e.groupEquiv.symm.injective)
        (RankOneDispatch.repeatedOneSection
          (RankOneDispatch.modelSection_of_moved_quotient c.sectionData e))).elim
    | symmetricFive e _ _ =>
      let a := markedRestriction e
      exact (no_alternatingFive_section d hP
        (L.subtype.comp a.groupEquiv.symm.toMonoidHom)
        (L.subtype_injective.comp a.groupEquiv.symm.injective)
        (RankOneDispatch.modelSection_of_moved_quotient c.sectionData a)).elim
    | linearTwo F hg e hoff hq =>
      have ht : L = ⊤ := hg.symm.trans (DualExtensions.section_generated c.sectionData hq hj)
      subst L
      obtain ⟨A, hA⟩ := FactorExtraction.ff_of_generated hj
      obtain ⟨S, hS⟩ := hoff A (DualExtensions.offender_equality c.sectionData hq hA).1
      have hs := sylow_supplement c.sectionData ⟨S, hS⟩
        (DualExtensions.offender_equality c.sectionData hq hA).2.2.1
      rw [fixedSpace_top] at hs
      exact ⟨F, ⟨coordinatesOfImage c.sectionData.space hs
        (transAction (imageSectionAction c.sectionData fixedSpace_top ⊤) e)⟩⟩

private theorem natural_of_faithful_binary_plane
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) W = 2) (hc : Nat.card D = 6) :
    Nonempty (ActionEquiv ρ (linearNatural BinaryField.two 2)) := by
  let X := Fin 2 → ZMod 2
  let e : W ≃ₗ[ZMod 2] X := LinearEquiv.ofFinrankEq W X (by
    simpa only [X, Module.finrank_pi, Fintype.card_fin] using hd)
  let c := LinearMap.GeneralLinearGroup.congrLinearEquiv e
  let l := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) X
  let s := BinaryLinear.OuterCyclic.slEquivLinear 2
  let f := s.symm.toMonoidHom.comp (l.toMonoidHom.comp (c.toMonoidHom.comp ρ.asGroupHom))
  have hfi : Function.Injective f := by
    intro g h he
    apply hf
    exact congrArg Units.val (c.injective (l.injective (s.symm.injective he)))
  have hbij : Function.Bijective f := (Nat.bijective_iff_injective_and_card f).mpr
    ⟨hfi, by rw [hc, Atlas.card_sl_two]; norm_num⟩
  let a := MulEquiv.ofBijective f hbij
  refine ⟨⟨a, e, ?_⟩⟩
  intro g v
  have he : s (a g) = l (c (ρ.asGroupHom g)) := s.apply_symm_apply _
  have he' := congrArg (fun t : X ≃ₗ[ZMod 2] X => t (e v)) he
  change e (ρ g v) = Matrix.mulVec (a g).val (e v)
  change Matrix.mulVec (a g).val (e v) = e (ρ g (e.symm (e v))) at he'
  simpa only [e.symm_apply_apply] using he'.symm

private theorem symmetricThree_coordinates
    [FiniteDimensional (ZMod 2) W]
    (hf : Function.Injective ρ) (h : SymmetricThreeCase ρ) :
    Nonempty (CentralQuotientCoordinates ρ (linearNatural BinaryField.two 2)) := by
  let s := MovedSection.ofNormal ρ (⊤ : Subgroup D)
  have hfs : Function.Injective s.space.toRepresentation := by
    intro g k he
    apply hf
    apply LinearMap.ext
    intro v
    have hv : v ∈ moved ρ ⊤ ⊔ ρ.invariants := by rw [h.decomposition.sup_eq_top]; trivial
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
    change ρ g (x + y) = ρ k (x + y)
    rw [map_add, map_add, hy g, hy k]
    exact congrArg (fun z : W => z + y)
      (congrArg Subtype.val (LinearMap.congr_fun he ⟨x, hx⟩))
  have hd : Module.finrank (ZMod 2) s.space.toSubmodule = 2 := h.dimension
  have hc : Nat.card D = 6 := by
    rw [Nat.card_congr h.equiv.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
    decide
  obtain ⟨e⟩ := natural_of_faithful_binary_plane s.space.toRepresentation hfs hd hc
  let q := imageEquivOfDisjoint s.space h.decomposition.disjoint
  let a : ActionEquiv
      (((fixed ρ).quotientImage s.space).toRepresentation.comp (⊤ : Subgroup D).subtype)
      (linearNatural BinaryField.two 2) := {
    groupEquiv := Subgroup.topEquiv.trans e.groupEquiv
    linearEquiv := q.symm.trans e.linearEquiv
    intertwines := by
      intro g v
      change e.linearEquiv (q.symm (((fixed ρ).quotientImage s.space).toRepresentation g v)) =
        linearNatural BinaryField.two 2 (e.groupEquiv g) (e.linearEquiv (q.symm v))
      rw [← e.intertwines]
      congr 1
      apply q.injective
      rw [q.apply_symm_apply]
      exact ((imageEquivOfDisjoint_equivariant s.space h.decomposition.disjoint g (q.symm v)).trans
        (congrArg (((fixed ρ).quotientImage s.space).toRepresentation g) (q.apply_symm_apply v))).symm }
  exact ⟨coordinatesOfImage s.space h.decomposition.sup_eq_top a⟩

/-- The full earlier alternatives and the prime-to-three source marker bound
supply coordinates on the WHOLE fixed quotient in the remaining SL₂ family.
The field degree remains unrestricted and positive. -/
theorem linearTwo_coordinates_of_classification [Finite D] [Nontrivial D]
    {K : GroupClass.{u}} (hyp : FFHypothesis K ρ)
    (hr : primeRank 3 D ≤ 1) (h : NontrivialAdequateAlternative ρ)
    {J : Subgroup D} (d : MarkedNormalizer ρ J)
    (hP : Nat.Coprime 3 (Nat.card (subspaceKernel ρ d.marker ⊤))) :
    ∃ F : BinaryField, Nonempty (CentralQuotientCoordinates ρ (linearNatural F 2)) := by
  let := hyp.finite_module
  rcases ChapterB.SourceInduction.NontrivialAdequateAlternative.at_three_rank_le_one h hr with
    ⟨_, ⟨c⟩⟩ | ⟨c⟩
  · exact quasisimple_coordinates d hP c hyp.generated hr
  · exact ⟨BinaryField.two, symmetricThree_coordinates hyp.faithful (Classical.choice c)⟩

open BestReduction.SourceAssembly Replacement.Transvections
open scoped IsMulCommutative
variable {G L X : Type u} [Group G] [Finite G] [Group L]
  [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]
  {K : GroupClass.{u}} {Y T V E : Subgroup G} [IsMulCommutative V]
  [(Replacement.Transvections.localSpan T V E).Normal]
  [IsElementaryAbelian 2 (Replacement.Transvections.localSpan T V E)]
  {σ : Representation (ZMod 2) ((temporaryLineNormalizer T V E) ⧸ localCore T V E) X}

/-- Coordinates on the whole fixed quotient of the actual temporary image.
The field is still arbitrary and positive; no Borel or marked-Sylow equality
is assumed. The universal earlier classifier is the only classification input. -/
theorem temporary_linearTwo_coordinates (d : TemporarySource K Y T V E L σ)
    (classify : AdequateClassificationInput.{u,u} K) :
    ∃ F : BinaryField, Nonempty (CentralQuotientCoordinates
      (imageRepresentation (σ.comp (thompsonImage T V E).subtype)) (linearNatural F 2)) := by
  let ρ := σ.comp (thompsonImage T V E).subtype
  let : Nontrivial (thompsonImage T V E) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr d.actor_nontrivial
  obtain ⟨A, hA⟩ := BestReduction.SourceAssembly.ff_of_generated ρ (d.generated classify)
  let B := actionSubgroup ρ A
  have hB : IsOffender (imageRepresentation ρ) B := hA.actionImage_of_odd_kernel ρ d.odd_kernel
  let : Nontrivial B := (Subgroup.nontrivial_iff_ne_bot _).mpr hB.1.1
  let : Nontrivial (actionImage ρ) := B.subtype_injective.nontrivial
  exact linearTwo_coordinates_of_classification (d.imageHypothesis classify)
    d.image_threeRank (d.classification classify) d.imageMarked (temporary_marker_coprime d)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.SourceClassification
