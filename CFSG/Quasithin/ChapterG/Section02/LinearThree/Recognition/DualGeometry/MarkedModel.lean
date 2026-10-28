module
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.DualGeometry.MarkedModel.Algebra
public import Theory.Representation.BinaryConjugationSection.QuadraticPair

/-!
# Marked lower images in an actual homogeneous dual model

The Frattini bound makes each literal pair intersection fixed, modulo S₂,
by its two U-groups. Equivariance and the model fixed-space identity put its
image in the corresponding annihilator copies. Spanning and the direct dual
frame then force all three containments to be equalities. Dot-product duality
provides the precise inverse-transpose coordinates used by the counting and
unchanged local-residual consumers, including multiplicity zero.

This is a conditional helper for G.2.5(6,8). The homogeneous model, the three
point-radical image identities, and the dual fixed-space identity are explicit
inputs; constructing them remains with the source-theorem assembly owner.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.5(6,8), printed pp.335–336, PDF pp.346–347.
-/
@[expose] public section
noncomputable section
open Subgroup Matrix
open scoped IsMulCommutative
attribute [local instance] ZMod.algebra
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.DualGeometry
open Setup Projective
open CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Hypothesis
namespace MarkedModel

variable {G : Type*} [Group G] [Finite G] {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g h : G} (d : LinearThree.Hypothesis D F n g h)

/-- The full point radical in the actual natural action: displacements land
in A and A is fixed pointwise. -/
def pointRadical (A : Point F (Fin 3 → F)) : Subgroup (D.star D.L) :=
  rootGroup (naturalAction d) A.val A.val

/-- The model bridges deliberately concern the U-groups and fixed vectors,
not the marked images of the lower quotient. -/
structure Bridges {hLI : D.L ≤ I D g h} (c : StarComparison D g h hLI) : Prop where
  image_u : (D.U.subgroupOf (I D g h)).map c.projection =
    pointRadical d (naturalPoint d)
  image_g : ((conjugate D.U g).subgroupOf (I D g h)).map c.projection =
    pointRadical d (conjugatePoint d ⟨g, d.g_mem⟩)
  image_h : ((conjugate D.U h).subgroupOf (I D g h)).map c.projection =
    pointRadical d (conjugatePoint d ⟨h, d.h_mem⟩)
  fixed_pair (A B : Point F (Fin 3 → F)) (hAB : Disjoint A.val B.val)
      (f : Module.Dual F (Fin 3 → F)) :
    (∀ a ∈ pointRadical d A ⊔ pointRadical d B, dualAction d a f = f) ↔
      f ∈ (A.val ⊔ B.val).dualAnnihilator

include d in
/-- Each of the three original U-groups has derived subgroup killed by the
literal lower denominator. This is the source Frattini argument. -/
theorem derived_bounds (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) :
    ⁅D.U, D.U⁆ ≤ S₂ D g h ∧
    ⁅conjugate D.U g, conjugate D.U g⁆ ≤ S₂ D g h ∧
    ⁅conjugate D.U h, conjugate D.U h⁆ ≤ S₂ D g h := by
  have hVE := (d.intersection hUT hf).1
  exact ⟨((derived_le_of_frattini_image_le (d.U_isPGroup hUT) hf).trans
      d.setup.point_le).trans hVE,
    (conjugate_derived_le d hUT hf g d.g_mem).trans hVE,
    (conjugate_derived_le d hUT hf h d.h_mem).trans hVE⟩

variable [CharP F 2]
  [((S₂ D g h).subgroupOf (S₃ D g h)).Normal]
  [IsElementaryAbelian 2 (LowerQuotient D g h)]
  {hLI : D.L ≤ I D g h} (c : StarComparison D g h hLI) (s : ℕ)

/-- A genuine homogeneous model with the original quotient coordinate equation.
The representation and section can be obtained from `Hypothesis.lower_action`.
No marked-image or order clause is an input. -/
structure Model where
  representation : Representation (ZMod 2) (D.star D.L) (Additive (LowerQuotient D g h))
  actionSection : Representation.BinaryConjugationSection (I D g h) (S₃ D g h) (S₂ D g h)
    (representation.comp c.projection)
  coordinate_eq (a : S₃ D g h) : (actionSection.coordinates a).toAdd =
    Additive.ofMul (QuotientGroup.mk' ((S₂ D g h).subgroupOf (S₃ D g h)) a)
  equivalence : Additive (LowerQuotient D g h) ≃ₗ[ZMod 2]
    (Fin s → Module.Dual F (Fin 3 → F))
  equivariant (a : D.star D.L) (v : Additive (LowerQuotient D g h)) (i : Fin s) :
    equivalence (representation a v) i = dualAction d a (equivalence v i)

namespace Model
variable {d c s} (m : Model d c s)

/-- The multiplicative version of the supplied binary linear equivalence. -/
def dualCoordinates : LowerQuotient D g h ≃* Multiplicative (Fin s → Module.Dual F (Fin 3 → F)) :=
  m.equivalence.toAddEquiv.toMultiplicativeRight

/-- Compose the actual model with the dot-product dual equivalence. -/
def coordinates : LowerQuotient D g h ≃* Multiplicative (Fin s → Fin 3 → F) :=
  m.dualCoordinates.trans (dotCoordinates (F := F) s).toAddEquiv.toMultiplicative

private def fixer (f : Module.Dual F (Fin 3 → F)) : Subgroup (D.star D.L) where
  carrier := {a | dualAction d a f = f}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change dualAction d a f = f at ha
    change dualAction d b f = f at hb
    change dualAction d (a * b) f = f
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' ha := ((dualAction d).inv_apply_eq_iff).mpr ha.symm

private theorem pair_image_le
    (U₁ U₂ B : Subgroup G) (A₁ A₂ : Point F (Fin 3 → F))
    (h₁ : ⁅U₁, B⁆ ≤ S₂ D g h) (h₂ : ⁅U₂, B⁆ ≤ S₂ D g h)
    (hm₁ : (U₁.subgroupOf (I D g h)).map c.projection = pointRadical d A₁)
    (hm₂ : (U₂.subgroupOf (I D g h)).map c.projection = pointRadical d A₂)
    (hfix : ∀ f : Module.Dual F (Fin 3 → F),
      (∀ a ∈ pointRadical d A₁ ⊔ pointRadical d A₂, dualAction d a f = f) ↔
        f ∈ (A₁.val ⊔ A₂.val).dualAnnihilator) :
    (lowerImage D g h B).map m.dualCoordinates.toMonoidHom ≤
      copies (A₁.val ⊔ A₂.val).dualAnnihilator s := by
  rintro v ⟨q, hq, rfl⟩ i
  obtain ⟨b, hb, rfl⟩ := hq
  have hv : Additive.ofMul (QuotientGroup.mk' ((S₂ D g h).subgroupOf (S₃ D g h)) b) ∈
      m.actionSection.imageSpace B :=
    (m.actionSection.mem_imageSpace_iff B _).mpr ⟨b, hb, m.coordinate_eq b⟩
  apply (hfix _).mp
  have hu (U : Subgroup G) (hU : ⁅U, B⁆ ≤ S₂ D g h) :
      (U.subgroupOf (I D g h)).map c.projection ≤
        fixer (d := d) (m.equivalence (Additive.ofMul
          (QuotientGroup.mk' ((S₂ D g h).subgroupOf (S₃ D g h)) b)) i) := by
    rintro a ⟨u, hu, rfl⟩
    change dualAction d (c.projection u) _ = _
    rw [← m.equivariant]
    have he := m.actionSection.fixed_on_imageSpace_of_commutator_le U B hU u hu _ hv
    change m.representation (c.projection u) _ = _ at he
    rw [he]
  have he := sup_le (hu U₁ h₁) (hu U₂ h₂)
  rw [hm₁, hm₂] at he
  exact he

/-- All three marked images are the full annihilator copies. The proof uses
containment from centralization and spanning, without prescribed image orders. -/
theorem dual_marks (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (b : Bridges d c) :
    (lowerImage D g h (W D g h ⊓ conjugate (W D g h) g)).map m.dualCoordinates.toMonoidHom =
      copies (dualPoint d).val s ∧
    (lowerImage D g h (W D g h ⊓ conjugate (W D g h) h)).map m.dualCoordinates.toMonoidHom =
      copies (dualPointH d).val s ∧
    (lowerImage D g h (conjugate (W D g h) g ⊓ conjugate (W D g h) h)).map
        m.dualCoordinates.toMonoidHom = copies (dualPointGH d).val s := by
  obtain ⟨hU, hg, hh⟩ := derived_bounds (d := d) hUT hf
  have hWg : conjugate (W D g h) g ≤ conjugate D.U g := map_mono inf_le_left
  have hWh : conjugate (W D g h) h ≤ conjugate D.U h := map_mono inf_le_left
  apply three_eq_of_span m.dualCoordinates
    (lower_marked_direct d hUT hf hLI).2.codisjoint.eq_top
    (dual_points_disjoint d) (dual_third_complement d)
  · exact m.pair_image_le D.U (conjugate D.U g) _ (naturalPoint d)
      (conjugatePoint d ⟨g, d.g_mem⟩)
      ((commutator_mono le_rfl (inf_le_left.trans inf_le_left)).trans hU)
      ((commutator_mono le_rfl (inf_le_right.trans hWg)).trans hg)
      b.image_u b.image_g
      (b.fixed_pair _ _ (natural_points_disjoint d))
  · exact m.pair_image_le D.U (conjugate D.U h) _ (naturalPoint d)
      (conjugatePoint d ⟨h, d.h_mem⟩)
      ((commutator_mono le_rfl (inf_le_left.trans inf_le_left)).trans hU)
      ((commutator_mono le_rfl (inf_le_right.trans hWh)).trans hh)
      b.image_u b.image_h
      (b.fixed_pair _ _ ((natural_third_disjoint d).mono_left le_sup_left))
  · exact m.pair_image_le (conjugate D.U g) (conjugate D.U h) _
      (conjugatePoint d ⟨g, d.g_mem⟩) (conjugatePoint d ⟨h, d.h_mem⟩)
      ((commutator_mono le_rfl (inf_le_left.trans hWg)).trans hg)
      ((commutator_mono le_rfl (inf_le_right.trans hWh)).trans hh)
      b.image_g b.image_h
      (b.fixed_pair _ _ ((natural_third_disjoint d).mono_left le_sup_right))

include m in
/-- Full I-invariance in the supplied actual section restricts to L. -/
theorem lower_normalizes : D.L ≤ normalizer (S₃ D g h : Set G) :=
  hLI.trans m.actionSection.normalized

/-- The exact ambient-conjugation equation required by `MarkedLayers`.
Its actor remains the original star projection and original SL₃ model. -/
theorem coordinates_equivariant (l : D.L) (a : S₃ D g h) (i : Fin s) :
    (m.coordinates (QuotientGroup.mk' ((S₂ D g h).subgroupOf (S₃ D g h))
      ⟨(l : G) * a * (l : G)⁻¹,
        (mem_normalizer_iff.mp (m.lower_normalizes l.property) a).mp a.property⟩)).toAdd i =
      (d.model (starProjection D l)⁻¹).val.transpose *ᵥ
        (m.coordinates (QuotientGroup.mk' ((S₂ D g h).subgroupOf (S₃ D g h)) a)).toAdd i := by
  have he := m.actionSection.equivariant (inclusion hLI l) a
  rw [m.coordinate_eq, m.coordinate_eq] at he
  change Additive.ofMul _ = m.representation (c.projection (inclusion hLI l)) _ at he
  rw [c.projection_on_L] at he
  change (dotProductEquiv F (Fin 3)).symm (m.equivalence (Additive.ofMul _) i) = _
  have he' := congrArg (fun v => m.equivalence v i) he
  have hd := (dualMarking d).equivariant (starProjection D l)
    (m.equivalence (Additive.ofMul (QuotientGroup.mk' ((S₂ D g h).subgroupOf (S₃ D g h)) a)) i)
  refine (congrArg (dotProductEquiv F (Fin 3)).symm
    (he'.trans (m.equivariant _ _ i))).trans ?_
  change (dotProductEquiv F (Fin 3)).symm
      (dualAction d (starProjection D l)
        (m.equivalence (Additive.ofMul (QuotientGroup.mk'
          ((S₂ D g h).subgroupOf (S₃ D g h)) a)) i)) =
      ((d.model (starProjection D l))⁻¹).val.transpose *ᵥ
        (m.coordinates (QuotientGroup.mk' ((S₂ D g h).subgroupOf (S₃ D g h)) a)).toAdd i at hd
  simpa only [map_inv] using hd

private theorem map_coordinates {B : Subgroup (LowerQuotient D g h)}
    {P : Submodule F (Module.Dual F (Fin 3 → F))}
    (hB : B.map m.dualCoordinates.toMonoidHom = copies P s) :
    B.map m.coordinates.toMonoidHom = ChiefFactors.lineCopies (coordinateLine P) s := by
  change B.map ((dotCoordinates (F := F) s).toAddEquiv.toMultiplicative.toMonoidHom.comp
    m.dualCoordinates.toMonoidHom) = _
  rw [← Subgroup.map_map, hB, copies_map_dotCoordinates]

/-- All three equalities in ordinary vector coordinates. The first two match
`MarkedLayers.lower_mark_g` and `MarkedLayers.lower_mark_h` literally. -/
theorem coordinate_marks (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (b : Bridges d c) :
    (lowerImage D g h (W D g h ⊓ conjugate (W D g h) g)).map m.coordinates.toMonoidHom =
      ChiefFactors.lineCopies (coordinateLine (dualPoint d).val) s ∧
    (lowerImage D g h (W D g h ⊓ conjugate (W D g h) h)).map m.coordinates.toMonoidHom =
      ChiefFactors.lineCopies (coordinateLine (dualPointH d).val) s ∧
    (lowerImage D g h (conjugate (W D g h) g ⊓ conjugate (W D g h) h)).map
        m.coordinates.toMonoidHom =
      ChiefFactors.lineCopies (coordinateLine (dualPointGH d).val) s := by
  obtain ⟨hg, hh, hgh⟩ := m.dual_marks hUT hf b
  exact ⟨m.map_coordinates hg, m.map_coordinates hh, m.map_coordinates hgh⟩

include m in
/-- Cardinalities of the three actual pair images, not assumed model orders. -/
theorem card_images (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (b : Bridges d c) :
    Nat.card (lowerImage D g h (W D g h ⊓ conjugate (W D g h) g)) = 2 ^ (n * s) ∧
    Nat.card (lowerImage D g h (W D g h ⊓ conjugate (W D g h) h)) = 2 ^ (n * s) ∧
    Nat.card (lowerImage D g h (conjugate (W D g h) g ⊓ conjugate (W D g h) h)) =
      2 ^ (n * s) := by
  have hc (B : Subgroup (LowerQuotient D g h)) (P : Point F (Module.Dual F (Fin 3 → F)))
      (hB : B.map m.coordinates.toMonoidHom = ChiefFactors.lineCopies (coordinateLine P.val) s) :
      Nat.card B = 2 ^ (n * s) := by
    rw [← card_map_of_injective (f := m.coordinates.toMonoidHom) m.coordinates.injective,
      hB, ChiefFactors.card_lineCopies _ _ ((coordinateLine_dimension P.val).trans P.property),
      d.field_card, ← pow_mul]
  obtain ⟨hg, hh, hgh⟩ := m.coordinate_marks hUT hf b
  exact ⟨hc _ (dualPoint d) hg, hc _ (dualPointH d) hh, hc _ (dualPointGH d) hgh⟩

/-- Feed the proved lower markings into the existing counting and L₁-restriction
interface. Only the independent upper coordinates and their two clauses remain
inputs; no actor or residual is replaced. -/
def toMarkedLayers (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (b : Bridges d c)
    [((S₃ D g h).subgroupOf (S D g h)).Normal] {r : ℕ}
    (upper : UpperQuotient D g h ≃* Multiplicative (Fin r → Fin 3 → F))
    (upper_equivariant : ∀ (l : D.L) (a : S D g h) (i : Fin r),
      (upper (QuotientGroup.mk' ((S₃ D g h).subgroupOf (S D g h))
        ⟨(l : G) * a * (l : G)⁻¹,
          (mem_normalizer_iff.mp (I_normalizes_core D g h (hLI l.property)) a).mp
            a.property⟩)).toAdd i =
        (d.model (starProjection D l)).val *ᵥ
          (upper (QuotientGroup.mk' ((S₃ D g h).subgroupOf (S D g h)) a)).toAdd i)
    (upper_mark : (upperImage D g h (W D g h)).map upper.toMonoidHom =
      ChiefFactors.lineCopies d.point r) : ChiefFactors.MarkedLayers d hLI r s where
  lower := m.coordinates
  upper := upper
  lower_normalizes := m.lower_normalizes
  lower_equivariant := m.coordinates_equivariant
  upper_equivariant := upper_equivariant
  lowerLineG := coordinateLine (dualPoint d).val
  lowerLineH := coordinateLine (dualPointH d).val
  lowerLineG_dimension := (coordinateLine_dimension _).trans (dualPoint d).property
  lowerLineH_dimension := (coordinateLine_dimension _).trans (dualPointH d).property
  lower_mark_g := (m.coordinate_marks hUT hf b).1
  lower_mark_h := (m.coordinate_marks hUT hf b).2.1
  upper_mark := upper_mark

end Model
end MarkedModel
end CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.DualGeometry
