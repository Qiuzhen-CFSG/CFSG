module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.LinearThreeReconstruction
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.LinearThreeCommonActors.FullAxis
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.Irreducible
/-!
# The genuine complete B.5.1 source implication

Induct on the original binary module dimension. The Irr+ branch uses the
complete corrected B.4.2 source theorem. In the reducible branch the proved
chief-factor and central-cover reductions identify the original component
as SL3 or binary SL4/SL5. The SL3 branch supplies doubled natural coordinates,
G=L, exact full-axis best offenders and original ratio one. The binary branch
uses only strictly smaller-dimensional induction to construct its actual
semisimple sum and exact natural multiplicities, including the dual exception.

All six corrected B.5.1 clauses are constructed on the original representation
and its literal moved section. No classifier, chief flag, constituent,
splitting, socle, ratio or whole-group conclusion is an extra hypothesis.
The inputs are precisely the genuine earlier semisimplicity/A.3.6/B.4.2 source
implications and nonbinary G2 root placement. Their universal producers are
owned by the main assembly; the full known-simple catalogue is specialized here.
Legacy public encodings and declarations remain unchanged.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), B.5.1,
printed pp.99--103, with A.1.42, A.3.6, B.4.2, B.4.8--9 and I.1.6.
-/

public section
open Representation Representation.BinaryOffender Theory.GroupTheory Subgroup
open scoped MatrixGroups ENNReal
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
universe u v
variable {G : Type u} [Group G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

private theorem bestOffender_actionEquiv [FiniteDimensional (ZMod 2) V]
    {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] {σ : Representation (ZMod 2) H W}
    (e : ActionEquiv ρ σ) (A : Subgroup G) :
    IsBestOffender ρ A ↔ IsBestOffender σ (A.map e.groupEquiv.toMonoidHom) := by
  constructor
  · exact fun h => h.map_of_fixedCodim ρ σ _ e.groupEquiv.injective
      (fixedCodim_map_equivariant ρ σ _ e.linearEquiv e.intertwines)
  · intro h
    let d := ExtensionConsequences.actionSymm e
    have hh := h.map_of_fixedCodim σ ρ d.groupEquiv.toMonoidHom d.groupEquiv.injective
      (fixedCodim_map_equivariant σ ρ d.groupEquiv.toMonoidHom d.linearEquiv d.intertwines)
    have hc : (A.map e.groupEquiv.toMonoidHom).map d.groupEquiv.toMonoidHom = A := by
      rw [map_map]
      have he : d.groupEquiv.toMonoidHom.comp e.groupEquiv.toMonoidHom = MonoidHom.id G := by
        ext g
        exact e.groupEquiv.symm_apply_apply g
      rw [he,map_id]
    rwa [hc] at hh

/-- Exact best offenders on the original moved action, under its actual group mark. -/
theorem doubleThree_source_offenders [Finite G] [FiniteDimensional (ZMod 2) V]
    {L : Subgroup G} (s : MovedSection ρ L) (hL : L = ⊤) (F : BinaryField)
    (e : ActionEquiv (s.space.toRepresentation.comp L.subtype)
      (repeated (linearNatural F 3) 2)) :
    ∀ A, IsBestOffender s.space.toRepresentation A ↔
      IsFullAxisGroup F 3 ((A.subgroupOf L).map e.groupEquiv.toMonoidHom) := by
  let c := ((MulEquiv.subgroupCongr hL).trans Subgroup.topEquiv).symm
  let a : ActionEquiv s.space.toRepresentation (repeated (linearNatural F 3) 2) :=
    ⟨c.trans e.groupEquiv,e.linearEquiv,fun g v => e.intertwines (c g) v⟩
  intro A
  have hc : A.map c.toMonoidHom = A.subgroupOf L := by
    ext l
    constructor
    · rintro ⟨g,hg,rfl⟩
      exact hg
    · intro hl
      exact ⟨l.val,hl,Subtype.ext rfl⟩
  have he : A.map a.groupEquiv.toMonoidHom = (A.subgroupOf L).map e.groupEquiv.toMonoidHom := by
    rw [← hc,map_map]
    rfl
  rw [bestOffender_actionEquiv s.space.toRepresentation a A,
    doubledThree_bestOffender_iff_fullAxis F,he]

/-- All six original source clauses in every reducible SL3 field degree. -/
theorem linearThree_reducible_conclusion [Finite G]
    {K : CFSG.Quasithin.GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (hsemisimple : SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput K)
    (h36 : Chapter1.Section02.A36Input K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    (hroot : NonbinaryG2RootPairInput)
    {L : Subgroup G} (h : QuasisimpleSourceHypothesis ρ K L)
    (hnot : ¬ IsIrrPlus ρ L (moved ρ L))
    (F : BinaryField) (mark : L ≃* SL(3,F.Carrier)) :
    Nonempty (SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ L) := by
  let := h.finite_module
  let s := h.movedSection ρ
  obtain ⟨hL,hq,E,⟨a⟩⟩ := linearThree_reducible_structure ρ hK hsemisimple h36 earlier h hnot s F mark
  have hfit : L = generalizedFitting G := by rw [h.fitting,hL,top_sup_eq]
  exact ⟨conclusion_of_action hroot h s hfit (.doubleThree E hL a
    (doubleThree_source_offenders ρ s hL E a) hq)⟩

/-- Full B.5.1, with strict dimension induction discharged internally. -/
theorem quasisimpleClassificationInput_of_earlier_sources
    {K : CFSG.Quasithin.GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (hsemisimple : SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput K)
    (h36 : Chapter1.Section02.A36Input K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    (hroot : NonbinaryG2RootPairInput) :
    SourceInduction.ProjectiveLine.QuasisimpleClassificationInput.{u,v} K := by
  have hstep (n : ℕ) : ∀ (D : Type u) [Group D] [Finite D]
      (W : Type v) [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
      (δ : Representation (ZMod 2) D W) (C : Subgroup D),
      Module.finrank (ZMod 2) W = n → QuasisimpleSourceHypothesis δ K C →
        Nonempty (SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion δ C) := by
    intro D hD hfD W hW hmW hdW δ C heq h
    induction n using Nat.strong_induction_on generalizing D W with
    | h n ih =>
      have ihu : SmallerDimensionInput.{u,v} K (Module.finrank (ZMod 2) W) := by
        intro E _ _ X _ _ _ τ B hd hs
        exact ih (Module.finrank (ZMod 2) X) (heq ▸ hd) E X τ B rfl hs
      by_cases hirr : IsIrrPlus δ C (moved δ C)
      · exact irreducible_conclusion earlier hK hroot h hirr
      · have hn := (reducible_naturalActor δ hK hsemisimple h36 earlier h hirr).1
        rcases hn with ⟨F,⟨mark⟩⟩ | ⟨d,hd,⟨mark⟩⟩
        · exact linearThree_reducible_conclusion δ hK hsemisimple h36 earlier hroot h hirr F mark
        · exact binary_reducible_conclusion δ hK earlier hroot ihu h hirr hd mark
  intro D _ _ W _ _ δ C h
  let := h.finite_module
  exact hstep (Module.finrank (ZMod 2) W) D W δ C rfl h

/-- Full B.5.1 for the complete known-simple carrier catalogue. -/
theorem knownSimple_quasisimpleClassificationInput
    (hsemisimple : SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput.{u}
      KnownSimple.IsKnownSimple)
    (h36 : Chapter1.Section02.A36Input.{u} KnownSimple.IsKnownSimple)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v}
      KnownSimple.IsKnownSimple)
    (hroot : NonbinaryG2RootPairInput) :
    SourceInduction.ProjectiveLine.QuasisimpleClassificationInput.{u,v} KnownSimple.IsKnownSimple :=
  quasisimpleClassificationInput_of_earlier_sources
    ComponentRecognition.SQTKSectionImage.knownSimple_containsSimpleTwoGroups
    hsemisimple h36 earlier hroot

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
