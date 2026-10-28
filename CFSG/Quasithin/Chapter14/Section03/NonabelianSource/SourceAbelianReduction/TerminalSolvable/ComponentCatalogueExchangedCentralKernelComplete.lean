module
public import CFSG.Quasithin.ChapterG.Section12.RecognitionTransitive
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedCentralKernelNondegenerateOrthogonalHigher
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedFaithfulAction

/-!
# The complete exchanged central-kernel branch

The full-linear action is excluded by the checked graph-Sylow degree bound
and the original degree-four small-actor obstruction. For a nondegenerate
constituent, G.12 recognition is now complete: the nontransitive case is the
actual orthogonal residual, and a transitive action above degree four is the
full symplectic group. The degree-four, orthogonal, symplectic and natural
SL₂(4) exclusions have all been discharged on the original marked action.

The remaining constituent is isotropic and faithful, is not self-dual, and
its exchanged companion is its dual. The final adapter constructs exactly
the properness and constituent premises required by the original faithful
exchanged classification consumer, retaining the selected I and all source
maps. No recognition or model premise remains in this central-kernel branch.
The other exchanged branches and final image assembly remain with
`qt-e-14315-component-exchanged-images`.

Source: Aschbacher--Smith G.10.15(2)(II),(3), printed pp.361--363.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open scoped IsMulCommutative
namespace ExchangedCentralSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : ExchangedCentralSource T M Mc F g B v L I)

include s

/-- G.12 residual recognition on the actual source HY-image. The exceptional
degree-four branch is excluded by the original actor bound; all other cases
are recognized as the literal symplectic or orthogonal residual. -/
theorem nondegenerate_recognition (u i : I)
    (h : ChapterG.Section12.ClassificationHypotheses
      s.constituentGeneratedImage (B.restrict I) u i) :
    ChapterG.Section12.ResidualModel
      (ChapterG.Section12.embeddedResidual s.constituentGeneratedImage) (B.restrict I) := by
  by_cases hd : finrank (ZMod 2) I=4
  · exact (s.not_nondegenerate_four hd h.nondegenerate).elim
  obtain ⟨n,hn⟩ := AlternatingForm.even_finrank (B.restrict I)
    h.alternating h.nondegenerate
  have h6 : 6≤finrank (ZMod 2) I := by have := h.dimension; omega
  rcases s.nondegenerate_transitive_or_orthogonal h.nondegenerate h with ht|⟨_,q,hq,he⟩
  · exact Or.inl (congrArg ChapterG.Section12.embeddedResidual
      (h.eq_formStabilizer_of_transitive_ge_six h6 ht))
  · exact Or.inr (Or.inl ⟨q,hq,s.constituentGeneratedImage_residual.trans he⟩)

/-- Complete nondegenerate exclusion on the marked source constituent.
Every recognition and model premise in the original assembly is discharged. -/
theorem not_nondegenerate : ¬(B.restrict I).Nondegenerate :=
  s.not_nondegenerate_of_classical_model_inputs s.not_fullLinear s.nondegenerate_recognition
    s.false_of_symplectic s.false_of_orthogonal

/-- Complete G.10.15(2)(II) on the original selected central-kernel constituent. -/
theorem faithful_data :
    ExchangedFaithfulConstituentData F.terminalRepresentation B L
      (F.terminalDot (F.X g)) I s.selected :=
  s.faithful_data_of_not_nondegenerate s.not_nondegenerate

/-- The two source conclusions, without any remaining local classification premise. -/
theorem proper_and_faithful :
    (¬ Function.Surjective (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I
      s.selected.invariant).toRepresentation.asGroupHom) ∧
    ExchangedFaithfulConstituentData F.terminalRepresentation B L
      (F.terminalDot (F.X g)) I s.selected :=
  ⟨s.not_fullLinear,s.faithful_data⟩

/-- The classification consumer receives the same constituent and the original
maps, with both formerly explicit central-kernel premises now proved. -/
theorem faithful_source : ExchangedFaithfulSource T M Mc F g B v L I where
  simple := s.simple
  empty := s.empty
  maximal := s.maximal
  unique_overgroup := s.unique_overgroup
  many_overgroups := s.many_overgroups
  seed_card := s.seed_card
  centralizer_quotient := s.centralizer_quotient
  not_model := s.not_model
  nonabelian := s.nonabelian
  parabolic_mem := s.parabolic_mem
  normalizer_not_mem := s.normalizer_not_mem
  nonsolvable := s.nonsolvable
  hypothesis := s.hypothesis
  small_actor := s.small_actor
  component := s.component
  moved := s.moved
  orthogonal := s.orthogonal
  fixedSpace_eq_bot := s.fixedSpace_eq_bot
  commutator_eq_top := s.commutator_eq_top
  selected := s.selected
  irreducible := s.irreducible
  conjugate_span := s.conjugate_span
  conjugate_disjoint := s.conjugate_disjoint
  form_cases := s.form_cases
  dimension_gt_two := s.dimension_gt_two
  independent := s.independent
  point_not_mem := s.point_not_mem
  proper := s.not_fullLinear
  faithful_data := s.faithful_data

/-- The literal source stabilizer degree now follows in the central-kernel
branch without assuming the properness that it uses. -/
theorem stabilizer_degree :
    let Y := (subspaceStabilizer F.terminalRepresentation I).subgroupOf (F.terminalDot (F.X g))
    letI : IsElementaryAbelian 2 Y :=
      IsElementaryAbelian.of_injective Y.subtype Y.subtype_injective
    finrank (ZMod 2) I = finrank (ZMod 2) (Additive Y) + 2 :=
  s.faithful_source.stabilizer_degree

/-- The central-kernel branch supplies the actual G.9/G.11 action-image
consumer, with the original stabilizer quotient and its sharp actor degree. -/
theorem faithful_image_setup :
    ChapterG.Section09.Setup s.faithful_source.imageAction
      (s.faithful_source.image
        (ExchangedFaithfulSource.actor (F := F) (g := g) (I := I)))
      (finrank (ZMod 2) I - 2) := s.faithful_source.image_setup

/-- Properness descends to the literal H-image in the HY action quotient. -/
theorem faithful_image_not_surjective : ¬ Function.Surjective
    (Representation.asGroupHom (s.faithful_source.imageAction.comp
      (s.faithful_source.image (componentOrbit L ⊤)).subtype)) :=
  s.faithful_source.image_not_surjective

/-- Non-self-duality descends with the same H-marking in the action quotient. -/
theorem faithful_image_not_selfDual : ¬ Nonempty (Representation.Equiv
    (s.faithful_source.imageAction.comp (s.faithful_source.image (componentOrbit L ⊤)).subtype)
    (Representation.dual (s.faithful_source.imageAction.comp
      (s.faithful_source.image (componentOrbit L ⊤)).subtype))) :=
  s.faithful_source.image_not_selfDual

end ExchangedCentralSource

variable {G : Type*} [Group G] [Finite G]

/-- G.10.15(2)(II),(3) from the original terminal source prefix and the
fixed constituent-selection witness. The kernel is only assumed central;
properness, faithfulness and the complete exchanged duality data are conclusions. -/
theorem source_exchanged_central_kernel
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (g : G)
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hn : ¬ Group.IsSolvable F.TerminalHdot)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hsmall : finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ≤
      finrank (ZMod 2) (Additive F.Uhat) / 2 - 1)
    {L : Subgroup F.TerminalHdot} (hL : IsComponent F.TerminalHdot L)
    (hm : ⁅L,F.terminalDot (F.X g)⁆ ≠ ⊥)
    (ho : ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B L)
    (hfix : fixedSpace F.terminalRepresentation (componentOrbit L ⊤)=⊥)
    (hcom : subspaceCommutator F.terminalRepresentation ⊤ (componentOrbit L ⊤)=⊤)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation
      (componentOrbit L ⊤) (F.terminalDot (F.X g)) I)
    (hirr : IsIrreducible
      (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I hI.invariant).toRepresentation)
    (hspan : letI : (componentOrbit L ⊤).Normal := componentOrbit_top_normal L
      (⨆ a : F.TerminalHdot, conjugateSubrepresentation F.terminalRepresentation
        (componentOrbit L ⊤)
        (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I hI.invariant) a)=⊤)
    (hdis : ∀ a : F.TerminalHdot,
      I.map (F.terminalRepresentation a)=I ∨ Disjoint (I.map (F.terminalRepresentation a)) I)
    (hform : (∀ u∈I,∀ w∈I,B u w=0) ∨ (B.restrict I).Nondegenerate)
    (hdim : 2 < finrank (ZMod 2) I)
    (hind : sSupIndep (subspaceOrbit F.terminalRepresentation (F.terminalDot (F.X g)) I))
    (hv : v∉I)
    (hker : (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I
      hI.invariant).toRepresentation.asGroupHom.ker≤Subgroup.center (componentOrbit L ⊤)) :
    (¬ Function.Surjective (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I
      hI.invariant).toRepresentation.asGroupHom) ∧
    ExchangedFaithfulConstituentData F.terminalRepresentation B L
      (F.terminalDot (F.X g)) I hI := by
  let s : ExchangedCentralSource T M Mc F g B v L I := {
    simple := hG
    empty := hempty
    maximal := hM
    unique_overgroup := hu
    many_overgroups := hmany
    seed_card := hcard
    centralizer_quotient := ⟨e⟩
    not_model := hnot
    nonabelian := hne
    parabolic_mem := hgP
    normalizer_not_mem := hgH
    nonsolvable := hn
    hypothesis := hyp
    small_actor := hsmall
    component := hL
    moved := hm
    orthogonal := ho
    fixedSpace_eq_bot := hfix
    commutator_eq_top := hcom
    selected := hI
    irreducible := hirr
    conjugate_span := hspan
    conjugate_disjoint := hdis
    form_cases := hform
    dimension_gt_two := hdim
    independent := hind
    point_not_mem := hv
    central_kernel := hker }
  exact s.proper_and_faithful

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
