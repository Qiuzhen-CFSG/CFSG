module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Models
public import CFSG.Quasithin.ChapterB.InternalThompsonFixedSpace

/-!
# The moving fixed seed in the actual 11.4.2 quotient action

The point z is centralized by Kz. The vector required in the last paragraph
of 11.4.2 is instead the vector in V1 supplied by strict comparison. We
transport that vector through the original subgroup inclusions to the
binary representation on the omega-center, retaining the literal images
of L1 and Kz in KzT/C_KzT(VK).

Source: Aschbacher--Smith, 11.4.2, printed p.777. This is the fixed-seed
input to the four-dimensional exclusion, not the terminal A7 contradiction.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (E : Closure.Geometry D)

/-- The marked L1 image in the literal action quotient. -/
def seedImage : Subgroup (ActionQuotient E) :=
  (E.L₁.subgroupOf (localGroup E)).map (projection E)

/-- The marked Kz image in that same quotient. -/
def componentImage : Subgroup (ActionQuotient E) :=
  (component E).map (projection E)

theorem seedImage_le_componentImage : seedImage E ≤ componentImage E :=
  map_mono (subgroupOf_mono _ (le_conjugateSpanBy _ _))

/-- Fixed vectors of either marked image are exactly ambient centralizing vectors.
The containment prevents subgroup restriction from silently changing the actor. -/
theorem mem_fixedSpace_image_iff (A : Subgroup G) (hA : A ≤ localGroup E)
    (v : Additive (moduleSubgroup E)) :
    v ∈ fixedSpace (action E) ((A.subgroupOf (localGroup E)).map (projection E)) ↔
      ((v.toMul : localGroup E) : G) ∈ centralizer (A : Set G) := by
  change v ∈ fixedSpace (ChapterB.InternalThompsonAction.action (moduleSubgroup E))
    ((A.subgroupOf (localGroup E)).map
      (ChapterB.InternalThompsonAction.actionMk (moduleSubgroup E))) ↔ _
  rw [ChapterB.InternalThompsonAction.mem_fixedSpace_iff]
  constructor
  · intro hv a ha
    exact congrArg (localGroup E).subtype (hv ⟨a,hA ha⟩ ha)
  · intro hv a ha
    exact Subtype.ext (hv a ha)

/-- The repaired source witness is fixed by the marked seed and moved by the
marked component on the actual binary module, before any representation comparison. -/
theorem exists_fixed_not_component_fixed (h : EarlierGeometry E)
    (hf : V ⊓ centralizer (L : Set G) = ⊥) (hne : E.Kz ≠ E.K)
    (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G)) :
    ∃ v : Additive (moduleSubgroup E),
      v ∈ fixedSpace (action E) (seedImage E) ∧
      v ∉ fixedSpace (action E) (componentImage E) := by
  obtain ⟨v,_,hv,hvL,hvK⟩ := exists_seed_fixed_moving_vector E h hf hne hstar hcent
  obtain ⟨w,hw,rfl⟩ := hv
  let u : Additive (moduleSubgroup E) := Additive.ofMul ⟨w,hw⟩
  refine ⟨u,?_,?_⟩
  · exact (mem_fixedSpace_image_iff E E.L₁
      ((le_conjugateSpanBy _ _).trans le_sup_left) u).mpr hvL
  · exact fun hu => hvK ((mem_fixedSpace_image_iff E E.Kz le_sup_left u).mp hu)

/-- Application on the original field flag, with fixed-space vanishing supplied
by 11.4.1 rather than assumed again. -/
theorem ofFlag_exists_fixed_not_component_fixed
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hstar : (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G)) :
    let E := ofFlag S f X z H
    ∃ v : Additive (moduleSubgroup E),
      v ∈ fixedSpace (action E) (seedImage E) ∧
      v ∉ fixedSpace (action E) (componentImage E) :=
  exists_fixed_not_component_fixed _ h (fixed_and_transitive D S _ hlinear h1132).1
    hne hstar hcent

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven
