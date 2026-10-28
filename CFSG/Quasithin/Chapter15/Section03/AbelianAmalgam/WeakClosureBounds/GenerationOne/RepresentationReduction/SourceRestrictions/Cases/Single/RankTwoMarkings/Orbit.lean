module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.RankTwoMarkings.Transport

/-!
# The aligned diagram pair on the actual orbit quotient

The two-constituent orbit construction uses the constituent's group marking
exactly. Expressing its twist through the transported diagram witness retains
the same Borel map and the original inducing element of T. The linear map
on the constituent uses the same model element as its inner group correction.
The source sum clause and existence of the natural constituent remain inputs.

Source: Aschbacher–Smith, F.9.18(4)(iii), printed pp.325–326, and the
natural-plus-diagram pair in 15.3.65, printed p.1152.
-/

@[expose] public noncomputable section
open Representation Representation.BinaryOffender Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.RankTwoMarkings
variable {D E V X : Type*} [Group D] [Group E]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup X] [Module (ZMod 2) X]
  {ρ : Representation (ZMod 2) D V} {K T : Subgroup D}
  {I : Submodule (ZMod 2) V} {σ : Representation (ZMod 2) E X}

/-- The aligned group map is exactly the indicated inner correction. -/
@[simp] theorem innerIdentification_groupEquiv
    {hI : K ≤ subspaceStabilizer ρ I}
    (d : CentralQuotientIdentification ρ K I hI σ) (g : E) :
    (innerIdentification d g).groupEquiv = d.groupEquiv.trans (MulAut.conj g) := rfl

/-- The linear map uses precisely the same model element. -/
@[simp] theorem innerIdentification_linearEquiv
    {hI : K ≤ subspaceStabilizer ρ I}
    (d : CentralQuotientIdentification ρ K I hI σ) (g : E) :
    (innerIdentification d g).linearEquiv = d.linearEquiv.trans (innerIntertwiner σ g) := rfl

/-- The existing orbit construction, expressed with the transported diagram
witness's actual automorphism. The geometric sum clause remains an input. -/
def diagramOrbitIdentification (hI : IsIrrPlusWith ρ K T I)
    (d : CentralQuotientIdentification ρ K I hI.invariant σ)
    {B P Q : Subgroup E} (a : InducedDiagramAction K T d.groupEquiv B P Q)
    (hne : I ≠ rightConjugate ρ I a.element)
    (hspan : (orbitSpan ρ T I).map (fixedSpace ρ K).mkQ =
      (I ⊔ rightConjugate ρ I a.element).map (fixedSpace ρ K).mkQ) :
    CentralQuotientIdentification ρ K (orbitSpan ρ T I)
      (orbitSpan_component_invariant ρ hI.normalizes hI.isIrrPlus)
      (σ.prod (σ.comp a.automorphism.toMonoidHom)) := by
  let p := orbitPairIdentification ρ hI d a.element a.mem_T hne hspan
  refine { groupEquiv := d.groupEquiv, linearEquiv := p.linearEquiv, equivariant := ?_ }
  intro g v
  have hp := p.equivariant g v
  have hg : p.groupEquiv = d.groupEquiv :=
    orbitPairIdentification_groupEquiv ρ hI d a.element a.mem_T hne hspan
  rw [hg] at hp
  simpa only [a.induced] using hp

/-- The orbit pair keeps the aligned constituent marking exactly. -/
@[simp] theorem diagramOrbitIdentification_groupEquiv (hI : IsIrrPlusWith ρ K T I)
    (d : CentralQuotientIdentification ρ K I hI.invariant σ)
    {B P Q : Subgroup E} (a : InducedDiagramAction K T d.groupEquiv B P Q)
    (hne : I ≠ rightConjugate ρ I a.element)
    (hspan : (orbitSpan ρ T I).map (fixedSpace ρ K).mkQ =
      (I ⊔ rightConjugate ρ I a.element).map (fixedSpace ρ K).mkQ) :
    (diagramOrbitIdentification hI d a hne hspan).groupEquiv = d.groupEquiv := rfl

/-- In particular the same marking identifies the actual overlap on the
constituent and on the two-constituent orbit. -/
theorem diagramOrbitIdentification_borel (hI : IsIrrPlusWith ρ K T I)
    (d : CentralQuotientIdentification ρ K I hI.invariant σ)
    {B P Q : Subgroup E} (a : InducedDiagramAction K T d.groupEquiv B P Q)
    (hne : I ≠ rightConjugate ρ I a.element)
    (hspan : (orbitSpan ρ T I).map (fixedSpace ρ K).mkQ =
      (I ⊔ rightConjugate ρ I a.element).map (fixedSpace ρ K).mkQ)
    (C : Subgroup K) (hC : C.map d.groupEquiv.toMonoidHom = B) :
    C.map (diagramOrbitIdentification hI d a hne hspan).groupEquiv.toMonoidHom = B := hC

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.RankTwoMarkings
