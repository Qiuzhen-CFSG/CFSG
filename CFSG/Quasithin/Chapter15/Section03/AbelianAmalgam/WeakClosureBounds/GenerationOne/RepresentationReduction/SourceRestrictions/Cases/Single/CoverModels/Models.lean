module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.CoverModels.Transport
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.BorelReduction.LinearCases
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions.ModelRigidity.CanonicalModels

/-!
# Marked E.2.2 models on the single actor

The canonical comparison transports all three Bender models and both
rank-two models to the literal actor, conditional on the center calculation.
PSU₃ is retained over its quadratic field. At odd exponent the existing
PSL₃-to-SL₃ comparison transports both parabolics, and at f>1 the actual
Sp₄ derived inclusion transports the Borel and both symplectic parabolics.
Each diagram witness is retained as an element of the original T, acting
by conjugation on the actor. No choice of module coordinates is made.

These are conditional transport results. They do not discharge the
concrete covering calculations needed for centerlessness.
Source: Aschbacher--Smith, E.2.2, pp.215--216, and 15.3.65, p.1152.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single
open BorelReduction SourceCases
open FFExclusions.ModelRigidity
namespace CoverModels

private theorem preservesParabolicClass_map {X Y : Type*} [Group X] [Group Y]
    (φ : X ≃* Y) {α : MulAut X} {P : Subgroup X}
    (hP : PreservesParabolicClass α P) :
    PreservesParabolicClass (MulAut.congr φ α) (P.map φ.toMonoidHom) := by
  obtain ⟨g, hg⟩ := hP
  refine ⟨φ g, ?_⟩
  have he := congrArg (fun S : Subgroup X => S.map φ.toMonoidHom) hg
  rw [map_map, map_map] at he ⊢
  convert he using 1 <;> congr 1 <;> ext x <;> simp [MulAut.congr]

/-- Transport the source diagram condition through the same model map,
retaining the source automizer witness. -/
theorem movesDiagram_map {G : Type*} [Group G] {H M K T : Subgroup G}
    {X Y : Type*} [Group X] [Group Y]
    (e : sourceImage H M K ≃* X) (φ : X ≃* Y) (P Q : Subgroup X)
    (hd : MovesDiagram H M K T e P Q) :
    MovesDiagram H M K T (e.trans φ) (P.map φ.toMonoidHom) (Q.map φ.toMonoidHom) := by
  obtain ⟨α, hα, hd⟩ := hd
  refine ⟨α, hα, ?_⟩
  rintro ⟨hP, hQ⟩
  apply hd
  have he : MulAut.congr φ.symm (MulAut.congr (e.trans φ) α) = MulAut.congr e α := by
    ext x
    simp [MulAut.congr]
  have hP' := preservesParabolicClass_map φ.symm hP
  have hQ' := preservesParabolicClass_map φ.symm hQ
  have hid : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id X := by
    ext x
    exact φ.symm_apply_apply x
  simpa only [he, map_map, hid, Subgroup.map_id] using And.intro hP' hQ'

/-- E.2.2's Sp₄′ Borel and parabolics all use the actual derived inclusion. -/
theorem spFourDerivedEquiv_subgroupOf {F : Type*} [Field F] [Finite F] {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (hf : 1 < f)
    (P : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F)) :
    (P.subgroupOf (Sp4Derived F)).map (spFourDerivedEquiv hF hf).toMonoidHom = P := by
  rw [spFourDerivedEquiv_subgroup]
  apply map_subgroupOf_eq_of_le
  rw [Sp4Derived, spFour_derived_eq_top hF hf]
  exact le_top

universe u
variable {G : Type u} [Group G] [Finite G]
variable {𝒦 : GroupClass.{u}} {H M K T Z ZS : Subgroup G} {f : ℕ}
variable [IsElementaryAbelian 2 (conjugateSpanBy ZS H)]
variable {a : LocalQuotientAction H (conjugateSpanBy ZS H) Z}
variable {I : Submodule (ZMod 2)
  (Additive ((conjugateSpanBy ZS H) ⧸ Z.subgroupOf (conjugateSpanBy ZS H)))}
variable (h : LocalInput 𝒦 H M K T Z ZS f a I)
variable (hz : center (actorImage H K) = ⊥)

/-- The marked Borel inside the representation component. -/
def ActorBorelPair (H M K : Subgroup G) {X : Type*} [Group X] (B : Subgroup X) : Prop :=
  ∃ e : actorImage H K ≃* X,
    ((actorImage H (M ⊓ K)).subgroupOf (actorImage H K)).map e.toMonoidHom = B

/-- The actual T-element and its conjugation on A witness diagram movement. -/
def ActorMovesDiagram {X : Type*} [Group X] (e : actorImage H K ≃* X)
    (P Q : Subgroup X) : Prop :=
  ∃ t : H, t.val ∈ T ∧
    ¬ (PreservesParabolicClass (MulAut.congr e (actorConjugation h t)) P ∧
      PreservesParabolicClass (MulAut.congr e (actorConjugation h t)) Q)

include h hz in
/-- Every source Borel pair lifts through the canonical component comparison. -/
theorem actorBorelPair {X : Type*} [Group X] (B : Subgroup X)
    (hm : ModelBorelPair H M K B) : ActorBorelPair H M K B := by
  obtain ⟨e, he⟩ := hm
  exact ⟨modelEquiv h hz e, modelEquiv_overlap h hz B e he⟩

/-- All three Bender models remain actual marked groups; the unitary entry
is PSU₃ over the quadratic field, and is never replaced by SU₃. -/
def ActorBenderModel (H M K : Subgroup G) (f : ℕ) : Prop :=
  (∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
    2 ≤ f ∧ Nat.card F = 2 ^ f ∧ ActorBorelPair H M K (BenderSuzuki.Converse.Borel F)) ∨
  (∃ m : ℕ, 1 ≤ m ∧ f = 2 * m + 1 ∧ ActorBorelPair H M K (SuzukiBorelSubgroup m)) ∨
  (∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
    (J : HermitianForm 3 F) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]),
    2 ≤ f ∧ Nat.card F = (2 ^ f) ^ 2 ∧
    (∀ x, J.conj x = x ^ (2 ^ f)) ∧
    Nat.card {x : F // J.conj x = x} = 2 ^ f ∧ ActorBorelPair H M K (unitaryBorel J hJ))

include h hz in
theorem actor_bender_model (hm : BenderModel H M K f) : ActorBenderModel H M K f := by
  rcases hm with hm | hm
  · rcases hm.linear with ⟨F, hF, hfin, hc, hf, hcard, hB⟩ | ⟨m, hm, hf, hB⟩
    · exact Or.inl ⟨F, hF, hfin, hc, hf, hcard, actorBorelPair h hz _ hB⟩
    · exact Or.inr (Or.inl ⟨m, hm, hf, actorBorelPair h hz _ hB⟩)
  · obtain ⟨F, hF, hfin, hc, J, hJ, hf, hcard, hconj, hfix, hB⟩ := hm
    exact Or.inr (Or.inr ⟨F, hF, hfin, hc, J, hJ, hf, hcard, hconj, hfix,
      actorBorelPair h hz _ hB⟩)

/-- The two actual rank-two actors, with standard matrix parabolics and the
same inducing T element. These are group markings, without module coordinates. -/
def ActorDiagramModel : Prop :=
  (∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
    1 < f ∧ Nat.card F = 2 ^ f ∧
    ∃ e : actorImage H K ≃* Matrix.SpecialLinearGroup (Fin 3) F,
      ((actorImage H (M ⊓ K)).subgroupOf (actorImage H K)).map e.toMonoidHom =
        Matrix.PSL3.LinearThree.borelSL F ∧
      ActorMovesDiagram h e (Matrix.PSL3.LinearThree.pointParabolicSL F)
        (Matrix.PSL3.LinearThree.lineParabolicSL F)) ∨
  (∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
    1 < f ∧ Nat.card F = 2 ^ f ∧
    ∃ e : actorImage H K ≃* Theory.SpecificGroups.SymplecticFour.Sp F,
      ((actorImage H (M ⊓ K)).subgroupOf (actorImage H K)).map e.toMonoidHom =
        Theory.SpecificGroups.SymplecticFour.borel (F := F) ∧
      ActorMovesDiagram h e (Theory.SpecificGroups.SymplecticFour.pointParabolic (F := F))
        (Theory.SpecificGroups.SymplecticFour.planeParabolic (F := F)))

include h hz in
theorem actor_diagram_model (hm : DiagramModel H M K T f) : ActorDiagramModel h := by
  rcases hm.linear h.odd with
    ⟨F, hF, hfin, hc, _, hcard, e, hB, hd⟩ | ⟨F, hF, hfin, hc, _, hcard, e, hB, hd⟩
  · exact Or.inl ⟨F, hF, hfin, hc, h.source.exponent_gt_one, hcard, modelEquiv h hz e,
      modelEquiv_overlap h hz _ e hB, diagram_witness h hz e _ _ hd⟩
  · let φ := spFourDerivedEquiv hcard h.source.exponent_gt_one
    have hB' : (componentOverlap H M K).map (e.trans φ).toMonoidHom =
        Theory.SpecificGroups.SymplecticFour.borel (F := F) := by
      change Subgroup.map (φ.toMonoidHom.comp e.toMonoidHom) _ = _
      rw [← map_map, hB]
      exact spFourDerivedEquiv_subgroupOf hcard h.source.exponent_gt_one _
    have hd' := movesDiagram_map e φ _ _ hd
    rw [spFourDerivedEquiv_subgroupOf, spFourDerivedEquiv_subgroupOf] at hd'
    exact Or.inr ⟨F, hF, hfin, hc, h.source.exponent_gt_one, hcard,
      modelEquiv h hz (e.trans φ), modelEquiv_overlap h hz _ _ hB',
      diagram_witness h hz (e.trans φ) _ _ hd'⟩

include h hz in
/-- Conditional final group transport. Discharging hz still requires the
concrete central-cover results; this is not the completed source deduction. -/
theorem actor_models : ActorBenderModel H M K f ∨ ActorDiagramModel h := by
  rcases (single_source_cases h.source.cases h.single).2 with hm | hm
  · exact Or.inl (actor_bender_model h hz hm)
  · exact Or.inr (actor_diagram_model h hz hm)

end CoverModels
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single
