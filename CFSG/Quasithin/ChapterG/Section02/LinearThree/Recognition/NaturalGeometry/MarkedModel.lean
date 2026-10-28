module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.NaturalGeometry.HomogeneousCoordinates
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.DualGeometry.MarkedModel.Algebra

/-!
# The marked upper homogeneous model in G.2.5

An actual homogeneous realization, together with the proved projective criterion,
identifies the three literal images of W, Wᵍ and Wʰ with copies of the three
independent source lines. Their coordinate decomposition gives the upper internal
direct sum, including multiplicity zero. The ambient-conjugation equation and
image orders are the exact upper inputs to `ChiefFactors.MarkedLayers` and its
local-residual restriction. No inclusion S₃ ≤ W is used.

The homogeneous realization is an explicit input in this module. The assembly
module constructs it from the universally quantified G.1.3 implication; the
source recognition owner retains discharge of that earlier theorem and of the
permitted earlier structural inputs.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.5(7–8), printed pp.335–336, PDF pp.346–347.
-/

@[expose] public section
open Subgroup Matrix
open scoped IsMulCommutative
attribute [local instance] ZMod.algebra
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.NaturalGeometry
open Setup Projective
open CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : Setup G}
  {F : Type*} [Field F] [Finite F] [CharP F 2] {n : ℕ} {g h : G}
  (d : LinearThree.Hypothesis D F n g h)
  [((S₃ D g h).subgroupOf (S D g h)).Normal]
  [IsElementaryAbelian 2 (UpperQuotient D g h)]
  {hLI : D.L ≤ I D g h} (c : StarComparison D g h hLI) (r : ℕ)

/-- An actual equivariant upper realization with the canonical quotient map.
Marked images and directness are conclusions, not fields of this input. -/
structure Model where
  representation : Representation (ZMod 2) (D.star D.L) (Additive (UpperQuotient D g h))
  actionSection : Representation.BinaryConjugationSection (I D g h) (S D g h) (S₃ D g h)
    (representation.comp c.projection)
  coordinate_eq (a : S D g h) : (actionSection.coordinates a).toAdd =
    Additive.ofMul (QuotientGroup.mk' ((S₃ D g h).subgroupOf (S D g h)) a)
  equivalence : Additive (UpperQuotient D g h) ≃ₗ[ZMod 2] (Fin r → Fin 3 → F)
  equivariant (a : D.star D.L) (v : Additive (UpperQuotient D g h)) (i : Fin r) :
    equivalence (representation a v) i = naturalAction d a (equivalence v i)

namespace Model
variable {d c r} (m : Model d c r)

/-- Multiplicative coordinates on the literal upper quotient. -/
def coordinates : UpperQuotient D g h ≃* Multiplicative (Fin r → Fin 3 → F) :=
  m.equivalence.toAddEquiv.toMultiplicativeRight

/-- The exact conjugation equation used for counting and restriction to L₁. -/
theorem coordinates_equivariant (l : D.L) (a : S D g h) (i : Fin r) :
    (m.coordinates (QuotientGroup.mk' ((S₃ D g h).subgroupOf (S D g h))
      ⟨(l : G) * a * (l : G)⁻¹,
        (mem_normalizer_iff.mp (I_normalizes_core D g h (hLI l.property)) a).mp
          a.property⟩)).toAdd i =
      (d.model (starProjection D l)).val *ᵥ
        (m.coordinates (QuotientGroup.mk' ((S₃ D g h).subgroupOf (S D g h)) a)).toAdd i := by
  have he := m.actionSection.equivariant (inclusion hLI l) a
  rw [m.coordinate_eq, m.coordinate_eq] at he
  change Additive.ofMul _ = m.representation (c.projection (inclusion hLI l)) _ at he
  rw [c.projection_on_L] at he
  exact (congrArg (fun v => m.equivalence v i) he).trans (m.equivariant _ _ i)

variable (hUT : D.U ≤ D.T) (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
  (hU : S D g h ≤ normalizer (D.U : Set G))
  (hgen : S D g h = (W D g h ⊔ conjugate (W D g h) g) ⊔ conjugate (W D g h) h)
  (hrad : UpperRadicalIdentification d c)

include hUT hf hU hgen hrad in
/-- All three original upper marks under the actual homogeneous coordinates. -/
theorem marked_coordinates :
    (upperImage D g h (W D g h)).map m.coordinates.toMonoidHom =
      ChiefFactors.lineCopies d.point r ∧
    (upperImage D g h (conjugate (W D g h) g)).map m.coordinates.toMonoidHom =
      ChiefFactors.lineCopies (conjugatePoint d ⟨g, d.g_mem⟩).val r ∧
    (upperImage D g h (conjugate (W D g h) h)).map m.coordinates.toMonoidHom =
      ChiefFactors.lineCopies (conjugatePoint d ⟨h, d.h_mem⟩).val r :=
  upperImage_three_homogeneous_coordinates c m.representation m.actionSection
    m.coordinate_eq m.equivalence d hUT hf hU hgen hrad m.equivariant

private theorem disjoint_of_map {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) {A B : Subgroup X}
    (hd : Disjoint (A.map e.toMonoidHom) (B.map e.toMonoidHom)) : Disjoint A B := by
  apply Subgroup.disjoint_def.mpr
  intro x hx hy
  apply e.injective
  exact (Subgroup.disjoint_def.mp hd (mem_map_of_mem _ hx)
    (mem_map_of_mem _ hy)).trans e.map_one.symm

include m hUT hf hU hgen hrad in
/-- The literal internal sum W/S₃ ⊕ Wᵍ/S₃ ⊕ Wʰ/S₃ in S/S₃.
Each term is an image, and the statement retains multiplicity zero. -/
theorem marked_direct :
    let A := upperImage D g h (W D g h)
    let B := upperImage D g h (conjugate (W D g h) g)
    let C := upperImage D g h (conjugate (W D g h) h)
    Disjoint A B ∧ IsCompl (A ⊔ B) C := by
  obtain ⟨ha, hb, hc⟩ := m.marked_coordinates hUT hf hU hgen hrad
  refine ⟨disjoint_of_map m.coordinates ?_, disjoint_of_map m.coordinates ?_, ?_⟩
  · rw [ha, hb]
    exact DualGeometry.MarkedModel.copies_disjoint (DualGeometry.natural_points_disjoint d) r
  · rw [Subgroup.map_sup, ha, hb, hc]
    change Disjoint (DualGeometry.MarkedModel.copies d.point r ⊔
      DualGeometry.MarkedModel.copies (conjugatePoint d ⟨g, d.g_mem⟩).val r)
      (DualGeometry.MarkedModel.copies (conjugatePoint d ⟨h, d.h_mem⟩).val r)
    rw [← DualGeometry.MarkedModel.copies_sup]
    exact DualGeometry.MarkedModel.copies_disjoint (DualGeometry.natural_third_disjoint d) r
  · apply codisjoint_iff.mpr
    apply Subgroup.map_injective (f := m.coordinates.toMonoidHom) m.coordinates.injective
    rw [Subgroup.map_sup, Subgroup.map_sup, ha, hb, hc,
      Subgroup.map_top_of_surjective m.coordinates.toMonoidHom m.coordinates.surjective]
    change (DualGeometry.MarkedModel.copies d.point r ⊔
      DualGeometry.MarkedModel.copies (conjugatePoint d ⟨g, d.g_mem⟩).val r) ⊔
      DualGeometry.MarkedModel.copies (conjugatePoint d ⟨h, d.h_mem⟩).val r = ⊤
    rw [← DualGeometry.MarkedModel.copies_sup, ← DualGeometry.MarkedModel.copies_sup]
    change DualGeometry.MarkedModel.copies (pairPlane d ⊔
      (conjugatePoint d ⟨h, d.h_mem⟩).val) r = ⊤
    rw [DualGeometry.natural_points_span]
    ext v
    simp [DualGeometry.MarkedModel.copies]

include m hUT hf hU hgen hrad in
/-- Each of the three actual marked images has the source order 2^(nr). -/
theorem marked_card :
    Nat.card (upperImage D g h (W D g h)) = 2 ^ (n * r) ∧
    Nat.card (upperImage D g h (conjugate (W D g h) g)) = 2 ^ (n * r) ∧
    Nat.card (upperImage D g h (conjugate (W D g h) h)) = 2 ^ (n * r) := by
  obtain ⟨ha, hb, hc⟩ := m.marked_coordinates hUT hf hU hgen hrad
  have card (A : Subgroup (UpperQuotient D g h)) (P : Point F (Fin 3 → F))
      (hm : A.map m.coordinates.toMonoidHom = ChiefFactors.lineCopies P.val r) :
      Nat.card A = 2 ^ (n * r) := by
    rw [← card_map_of_injective (f := m.coordinates.toMonoidHom) m.coordinates.injective,
      hm, ChiefFactors.card_lineCopies _ _ P.property, d.field_card, ← pow_mul]
  exact ⟨card _ (naturalPoint d) ha, card _ (conjugatePoint d ⟨g, d.g_mem⟩) hb,
    card _ (conjugatePoint d ⟨h, d.h_mem⟩) hc⟩

include m hUT hf hU hgen hrad in
/-- The order adapter uses the actual kernel W ∩ S₃, identified with the
join of the two pair intersections inside W. -/
theorem marked_pair_index :
    ((W D g h ⊓ conjugate (W D g h) g) ⊔
      (W D g h ⊓ conjugate (W D g h) h)).relIndex (W D g h) = 2 ^ (n * r) := by
  rw [← d.card_upperImage_pair_index hUT hf hLI]
  exact (m.marked_card hUT hf hU hgen hrad).1

end Model
end CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.NaturalGeometry
