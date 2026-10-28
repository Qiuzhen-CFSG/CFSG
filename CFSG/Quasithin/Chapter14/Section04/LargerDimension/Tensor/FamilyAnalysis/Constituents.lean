module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.Invariant
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.Intersection
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.CanonicalForm

/-!
# Constituent geometry and the first tensor family member

Source: Aschbacher–Smith, Lemma 14.4.10(2) and its first proof paragraph,
printed p.1010, combined manuscript of 1 March 2004.

The elementary order-eight image of the actual Wᵍ selects a nonidentity
component-centralizing element. Its displacement space is the unique
T-invariant irreducible K₀-submodule, containing C_Ũ(T) and Ṽ₂. Its cubic
translate is an actual K₀-complement. Both constituent alternatives give
the displayed complement intersection bound, and the earlier [Wᵍ,W] ≤ E
bound puts the entire first moved plane in Ẽ. The central-quotient lift
then gives actual order eight and X₁ ∈ Y.

The canonical form is constructed from extraspeciality and the published
quotient coordinates. No selected-constituent, form, intersection-calculation
or moved-space conclusion is assumed. The precise earlier-source inputs
remain in EarlierGeometry. The source assembly retains the genuine
Hypothesis 14.3.10 configuration and supplies the independent component-image
marking. These conditional common-geometry results do not assert the other
clauses of 14.4.10 or replace its ambient hypotheses.
-/

public section

open Subgroup TensorProduct Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.CaseFiveCoordinates
variable {G : Type*} [Group G]
  {D : Subgroup Five} {hAD : AltFive ≤ D}
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {H U T P : Subgroup G} {g : G}
  (c : CaseFiveCoordinates hAD (V := V) H U)

/-- There is exactly one T-invariant irreducible K₀-submodule. Its existence
comes from the elementary order-eight image, for either constituent model. -/
theorem EarlierGeometry.exists_unique_T_invariant_constituent
    (h : c.EarlierGeometry T P g)
    (hK : c.actorImage (component H) = (⊥ : Subgroup Three).prod (AltFive.subgroupOf D)) :
    ∃! M : Submodule (ZMod 2) (BinaryPermutation.core (Fin 3) ⊗[ZMod 2] V),
      c.IsIrreducibleFor (component H) M ∧
        c.actorImage T ≤ subspaceStabilizer (sourceTensorAction c.constituent) M := by
  obtain ⟨s⟩ := h.exists_selectedConstituent c hK
  exact ⟨s.firstSpace, ⟨s.first_irreducible, s.T_invariant⟩,
    fun M hM => s.unique M hM.1 hM.2⟩

/-- The second displayed inequality in the source follows from the actual
12.8.11(1) bound, restricted to the chosen complement and component actors. -/
theorem EarlierGeometry.complement_commutator_le
    (h : c.EarlierGeometry T P g) (s : c.SelectedConstituent T P g) :
    subspaceCommutator (sourceTensorAction c.constituent)
      (c.image (centralLayer U P) ⊓ s.secondSpace)
      (c.actorImage (conjugateLayer U P g) ⊓ c.actorImage (component H)) ≤
        c.image (intersectionLayer U P g) := by
  apply le_trans _ (h.source_bound c)
  apply Submodule.span_le.mpr
  rintro v ⟨a, ha, w, hw, rfl⟩
  exact Submodule.subset_span ⟨a, ha.1, w, hw.1, rfl⟩

variable [Finite G] [IsExtraspecial 2 U]

/-- Construct the constituent and its actual cubic-translate complement,
then prove the perpendicular identity, plane splitting and both source
intersection inequalities for that same choice. The form is constructed
from extraspeciality; neither a form nor a constituent witness is assumed. -/
theorem EarlierGeometry.exists_constituent_geometry
    (h : c.EarlierGeometry T P g)
    (hK : c.actorImage (component H) = (⊥ : Subgroup Three).prod (AltFive.subgroupOf D)) :
    ∃ s : c.SelectedConstituent T P g,
      c.image (centralLayer U P) = (c.image P).orthogonalBilin c.canonicalForm.form ∧
      c.image (movedSpace P (first H)) = c.image P ⊔
        (c.image (movedSpace P (first H)) ⊓ s.secondSpace) ∧
      c.image (movedSpace P (first H)) ⊓ s.secondSpace ≤
        subspaceCommutator (sourceTensorAction c.constituent)
          (c.image (centralLayer U P) ⊓ s.secondSpace)
          (c.actorImage (conjugateLayer U P g) ⊓ c.actorImage (component H)) ∧
      subspaceCommutator (sourceTensorAction c.constituent)
        (c.image (centralLayer U P) ⊓ s.secondSpace)
        (c.actorImage (conjugateLayer U P g) ⊓ c.actorImage (component H)) ≤
          c.image (intersectionLayer U P g) := by
  obtain ⟨s⟩ := h.exists_selectedConstituent c hK
  exact ⟨s, h.centralLayer_image c c.canonicalForm, s.first_image_split c h,
    h.intersection c c.canonicalForm s hK, h.complement_commutator_le c s⟩

/-- Both constituent alternatives give a plane in the literal image of E.
The source point is in E, and the rest of the plane lies in the chosen
complement, where the two proved intersection bounds apply. -/
theorem EarlierGeometry.first_tilde_calculation
    (h : c.EarlierGeometry T P g)
    (hK : c.actorImage (component H) = (⊥ : Subgroup Three).prod (AltFive.subgroupOf D)) :
    Nat.card (tilde U (movedSpace P (first H))) = 4 ∧
      tilde U (movedSpace P (first H)) ≤ tilde U (intersectionLayer U P g) := by
  obtain ⟨s, _, hsplit, hintersection, hbound⟩ := h.exists_constituent_geometry c hK
  refine ⟨c.first_tilde_card_four h.point_le_U h.point_rank, c.image_le_iff.mp ?_⟩
  rw [hsplit]
  exact sup_le (c.image_mono h.point_le_intersection) (hintersection.trans hbound)

/-- Apply the literal central-quotient lift to the proved plane calculation.
This supplies actual order eight and X₁ ∈ Y, including the central factor
Z(U), without a constituent, intersection or moved-space premise. -/
theorem EarlierGeometry.first_mem_Y_from_geometry
    (h : c.EarlierGeometry T P g)
    (hK : c.actorImage (component H) = (⊥ : Subgroup Three).prod (AltFive.subgroupOf D)) :
    first H ∈ YFamily H T P (intersectionLayer U P g) := by
  obtain ⟨hcard, hle⟩ := h.first_tilde_calculation c hK
  exact first_mem_Y_of_tilde_calculation h.T_le_H h.U_le_T c.H_normalizes_U
    h.point_le_U h.center_le_point
    (h.center_le_point.trans (subgroupOf_mono U h.point_le_intersection))
    c.actor_models hcard hle

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.CaseFiveCoordinates
