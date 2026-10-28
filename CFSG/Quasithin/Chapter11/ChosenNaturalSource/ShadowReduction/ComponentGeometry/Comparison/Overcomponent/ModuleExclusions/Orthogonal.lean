module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Classification.CentralQuotients
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceIrreducible
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTransfer

/-!
# Excluding orthogonal-minus overcomponent actions

The marked orthogonal alternative identifies the actual component image
with SL2 over its specified binary quadratic extension. Its natural action
is a faithful irreducible FF test action. Applying B.4 to that action gives
central-quotient restrictions on the same component, without claiming that
the original orthogonal representation is FF. The canonical quotient map
transports those restrictions to the original J/O2(J).

ModuleExclusions combines this with the complete six-pair comparison.
Source: Aschbacher--Smith 7.0.1 and 11.4.2, printed pp.695,776.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.ModuleExclusions
open Quasisimple.Classification ChapterB.QuasisimpleSource

private theorem restrictions_of_irreducible
    {A U : Type*} [Group A] [Finite A] [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U] (σ : Representation (ZMod 2) A U) (K : Subgroup A)
    (hsq : IsSQTK KnownSimple.IsKnownSimple A) (hfit : generalizedFitting A = K)
    (hK : IsQuasisimple K) (hf : Function.Injective σ)
    (hi : IsIrreducible (σ.comp K.subtype)) (hff : IsFFModule σ) :
    CentralQuotientRestrictions (K ⧸ center K) := by
  have hs := ChapterB.SourceClassification.source_hypotheses hsq hfit hK hf hi hff
  refine ⟨ChapterB.SourceClassification.sporadic_false hs hff,
    fun p hp ho hm => ChapterB.SourceClassification.not_ff_odd_psl3 hs hp ho hm hff,
    fun p d hp ho hd hlo hm => ChapterB.SourceClassification.odd_pslTwo_parameters hs hff hp ho hd hlo hm,
    ?_,fun n hn hm => ChapterB.SourceClassification.triality_not_ff hs n hn hm hff,
    fun m hm he => ChapterB.SourceClassification.reeF4_excluded hs hff hm he.some⟩
  intro p hp ho hm
  exact ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion.source_unitaryRestriction
    σ K ⟨hsq,hfit.symm,hK,hf,hi⟩ hp ho hm hs.smallCubic

/-- An actual binary SL2 marking supplies a natural FF test action on the
same component. This is independent of the orthogonal representation. -/
theorem restrictions_of_binaryLinearTwo
    {P : Type*} [Group P] [Finite P] [IsQuasisimple P]
    (hsq : IsSQTK KnownSimple.IsKnownSimple P) (F : BinaryField)
    (e : P ≃* Matrix.SpecialLinearGroup (Fin 2) F.Carrier) :
    CentralQuotientRestrictions (P ⧸ center P) := by
  let σ := (linearNatural F 2).comp e.toMonoidHom
  let a : ActionEquiv σ (linearNatural F 2) :=
    ⟨e,LinearEquiv.refl _ _,fun _ _ => rfl⟩
  have hf : Function.Injective σ := (SmallMoved.linearNatural_faithful F 2).comp e.injective
  have hi : IsIrreducible σ := ExtensionConsequences.irreducible_of_equiv a
    (ExtensionConsequences.linearNatural_irreducible F (by decide))
  have hiTop : IsIrreducible (σ.comp (⊤ : Subgroup P).subtype) :=
    (irreducible_comp_surjective_iff (topEquiv (G := P)).toMonoidHom
      (topEquiv (G := P)).surjective σ).mpr hi
  have hff : IsFFModule σ := by
    have hn : IsFFModule (linearNatural F 2) :=
      ⟨_,(ChapterK.Linear.Natural.hyperplaneCentralizer_best F 2 ⟨0,by decide⟩ (by decide)).isOffender _⟩
    exact hn.map_equivariant _ _ e.symm.toMonoidHom e.symm.injective
      (LinearEquiv.refl _ _) (fun _ _ => by simp [σ])
  let : IsQuasisimple (⊤ : Subgroup P) := IsQuasisimple.of_mulEquiv topEquiv.symm
  let : IsSimpleGroup (P ⧸ center P) := IsQuasisimple.simple
  let : Nontrivial P := (QuotientGroup.mk'_surjective (center P)).nontrivial
  exact (restrictions_of_irreducible σ ⊤ hsq
    generalizedFitting_eq_top_of_quasisimple inferInstance hf hiTop hff).of_mulEquiv
    (IsQuasisimple.centralQuotientEquiv (topEquiv (G := P)).toMonoidHom
      (topEquiv (G := P)).surjective).symm

/-- The marked orthogonal-minus row has the central quotient of binary
SL2. Natural-module testing gives the same negative model restrictions. -/
theorem orthogonal_restrictions
    {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {J W : Subgroup G}
    (D : Chapter12.Section02.ChosenModule T J W)
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T J)
    (ho : Chapter7.NormalizedSource.OrthogonalMinusAlternative
      D.orbitRepresentation D.orbitComponent) :
    CentralQuotientRestrictions ((J ⧸ pCore 2 J) ⧸ center (J ⧸ pCore 2 J)) := by
  obtain ⟨n,hn,⟨M⟩⟩ := ho
  let : NeZero n := ⟨by omega⟩
  let : NeZero (2 * n) := ⟨by omega⟩
  let F : BinaryField := {
    Carrier := Representation.OrthogonalFourMinus.FiniteModel.Field n
    degree := 2 * n
    degree_pos := by omega
    card_eq := GaloisField.card 2 (2 * n) (by omega) }
  let := D.orbitComponent_quasisimple h
  exact (restrictions_of_binaryLinearTwo ((D.sourceOrbit_sqtk h).subgroup D.orbitComponent)
    F M.groupEquiv).of_mulEquiv (D.orbitCentralQuotientEquiv h)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.ModuleExclusions
