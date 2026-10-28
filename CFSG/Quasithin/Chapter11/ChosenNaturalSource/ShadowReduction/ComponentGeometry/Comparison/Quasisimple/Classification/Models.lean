module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Classification.Action

/-!
# The actual FF image catalogue before the 11.1.1 comparison

Extract the actor isomorphism from every genuine B.4.2 and B.5.1 action
row. The reducible linear-three, natural-plus-dual and repeated-natural
rows are included. The binary derived endpoints and triple cover retain
their actual carriers. Transport from the offender restriction identifies
this list with the literal component image in KzT/C(VK).

The original field parameter has not yet been matched with these fields.
Intersecting this proved list with the complete 11.1.1 list remains part
of the component-comparison owner; ImageModel is not SurvivingModels.
Source: Aschbacher--Smith 11.4.2, printed p.777, and B.4.2/B.5.1.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Classification
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (E : Closure.Geometry D)

open ChapterB.QuasisimpleSource

/-- The complete group-image list supplied by B.4.2 and B.5.1 before its
intersection with the source 11.1.1 catalogue. Every row has a literal marking. -/
inductive ImageModel (A : Type*) [Group A] : Prop where
  | linearTwo (F : BinaryField) (mark : A ≃* Matrix.SpecialLinearGroup (Fin 2) F.Carrier)
  | linearThree (F : BinaryField) (mark : A ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier)
  | symplectic (F : BinaryField) (large : 1 < F.degree)
      (mark : A ≃* Matrix.symplecticGroup (Fin 2) F.Carrier)
  | g2 (F : BinaryField) (large : 1 < F.degree)
      (mark : A ≃* Atlas.G2.Model F.Carrier)
  | symplecticTwo (mark : A ≃* commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)))
  | g2Two (mark : A ≃* commutator (Atlas.G2.Model (ZMod 2)))
  | alternating (n : ℕ) (degree : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8)
      (mark : A ≃* alternatingGroup (Fin n))
  | tripleSix (centerMark : center A ≃* Multiplicative (ZMod 3))
      (quotientMark : (A ⧸ center A) ≃* alternatingGroup (Fin 6))
  | binaryLinear (n : ℕ) (degree : n = 4 ∨ n = 5)
      (mark : A ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2))

private theorem center_map_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (center A).map e.toMonoidHom = center B := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact (Subgroup.centerCongr e ⟨y,hy⟩).property
  · intro hx
    exact ⟨e.symm x,(Subgroup.centerCongr e.symm ⟨x,hx⟩).property,e.apply_symm_apply x⟩

theorem ImageModel.of_mulEquiv {A B : Type*} [Group A] [Group B]
    (h : ImageModel B) (e : A ≃* B) : ImageModel A := by
  cases h with
  | linearTwo F a => exact .linearTwo F (e.trans a)
  | linearThree F a => exact .linearThree F (e.trans a)
  | symplectic F hn a => exact .symplectic F hn (e.trans a)
  | g2 F hn a => exact .g2 F hn (e.trans a)
  | symplecticTwo a => exact .symplecticTwo (e.trans a)
  | g2Two a => exact .g2Two (e.trans a)
  | alternating n hn a => exact .alternating n hn (e.trans a)
  | tripleSix z a =>
    exact .tripleSix ((Subgroup.centerCongr e).trans z)
      ((QuotientGroup.congr _ _ e (center_map_equiv e)).trans a)
  | binaryLinear n hn a => exact .binaryLinear n hn (e.trans a)

omit [Finite G] in
private theorem irreducible_image_model
    {Q W : Type*} [Group Q] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) Q W} {K I : Subgroup Q}
    (hc : ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ K I) :
    ImageModel K := by
  cases hc with
  | linearTwo F _ e _ _ => exact .linearTwo F e.groupEquiv
  | linearThree F _ e _ => exact .linearThree F e.groupEquiv
  | symplectic F hn _ e _ => exact .symplectic F hn e.groupEquiv
  | symplecticTwo e _ => exact .symplecticTwo e.subgroupEquiv
  | g2 F hn _ e _ _ => exact .g2 F hn e.groupEquiv
  | g2Two e _ _ => exact .g2Two e.subgroupEquiv
  | symmetric n hn e _ _ =>
    exact .alternating n (by rcases hn with h | h <;> omega) e.subgroupEquiv
  | alternatingSix _ e _ _ => exact .alternating 6 (by omega) e.groupEquiv
  | alternatingSeven _ _ e _ _ _ => exact .alternating 7 (by omega) e
  | tripleSix _ a _ => exact .tripleSix a.centerEquiv a.quotientEquiv
  | binaryLinear n hn _ e _ => exact .binaryLinear n hn e.groupEquiv
  | orthogonalSix _ _ e _ _ => exact .alternating 8 (by omega) e.groupEquiv
  | symmetricEight _ e _ => exact .alternating 8 (by omega) e.subgroupEquiv
  | exteriorFive _ _ e _ _ _ => exact .binaryLinear 5 (Or.inr rfl) e

/-- The reducible B.5.1 rows are retained as well as every irreducible B.4.2 row. -/
theorem image_model_of_source
    {Q W : Type*} [Group Q] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) Q W} {K : Subgroup Q}
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ K) :
    ImageModel K := by
  cases c.clause_one with
  | irreducible _ _ _ hc _ => exact irreducible_image_model hc
  | doubleThree F _ e _ _ => exact .linearThree F e.groupEquiv
  | naturalDual n hn _ e => exact .binaryLinear n hn e.some.groupEquiv
  | repeatedNatural n _ hn _ _ _ e => exact .binaryLinear n hn e.some.groupEquiv

/-- The actual image in KzT/C(VK), with no recognition or irreducibility input. -/
theorem image_model
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G)) (hff : IsFFModule (action E)) :
    ImageModel (componentImage E) := by
  obtain ⟨hK,⟨c⟩⟩ := source_classification E h hf hne hstar hcent hff
  exact (image_model_of_source c).of_mulEquiv (subgroupOfEquivOfLe hK).symm


end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Classification
