module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.DualGeometry.Criterion
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.DualGeometry.MarkedModel

/-!
# Dual projective geometry on the literal S₃/S₂ quotient

The frame-root argument supplies full I-invariance, allowing the canonical
lower quotient action with its original coordinate map. The constructed dual
point map satisfies the complete recognition criterion and has exactly the
three prescribed pair-intersection images. The concrete model geometry also
discharges every bridge in the conditional homogeneous marked model, yielding
all three dual and ordinary coordinate marks and their orders, even at
multiplicity zero.

The earlier structural inputs are produced by qt-g025-structure and discharged
by qt-g02-linear-three. The universal G.1.3 implication and recognition assembly
remain with qt-g025-recognition and qt-g-01; no recognition output is assumed
in the construction of the criterion.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.1.1–4 and G.2.5, printed pp.327–328,335–336.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.DualGeometry
open Subgroup Setup Projective
open CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g h : G} (d : LinearThree.Hypothesis D F n g h)

open scoped IsMulCommutative

/-- All concrete model bridges required by the conditional marked-model
construction, including every conjugate radical and the exact dual fixed space. -/
theorem marked_model_bridges {hLI : D.L ≤ I D g h}
    (e : StarComparison D g h hLI) (hrad : UpperRadicalIdentification d e) :
    MarkedModel.Bridges d e where
  image_u := hrad
  image_g := conjugate_radical_image d e hrad ⟨g, d.g_mem⟩
  image_h := conjugate_radical_image d e hrad ⟨h, d.h_mem⟩
  fixed_pair A B _ f := by
    have hn (P : Point F (Fin 3 → F)) : P.val ≠ ⊤ := by
      intro he
      have hd := P.property
      rw [he] at hd
      simp at hd
    have he : MarkedModel.pointRadical d A ⊔ MarkedModel.pointRadical d B =
        (Matrix.SpecialLinearGroup.FrameGeometry.pointRadical A.val ⊔
          Matrix.SpecialLinearGroup.FrameGeometry.pointRadical B.val).comap d.model.toMonoidHom := by
      apply Subgroup.map_injective (f := d.model.toMonoidHom) d.model.injective
      rw [Subgroup.map_sup]
      change (rootGroup (naturalAction d) A.val A.val).map d.model.toMonoidHom ⊔
          (rootGroup (naturalAction d) B.val B.val).map d.model.toMonoidHom = _
      rw [ModelGeometry.map_rootGroup, ModelGeometry.map_rootGroup,
        Subgroup.map_comap_eq_self_of_surjective d.model.surjective]
      rfl
    have hfix : Representation.invariants ((dualAction d).comp
        (MarkedModel.pointRadical d A ⊔ MarkedModel.pointRadical d B).subtype) =
          (A.val ⊔ B.val).dualAnnihilator := by
      rw [he, ModelGeometry.dualFixed_comap]
      exact Matrix.SpecialLinearGroup.FrameGeometry.dualFixed_pair _ _ (hn A) (hn B)
    constructor
    · intro hf
      rw [← hfix]
      exact fun a => hf a a.property
    · intro hf a ha
      rw [← hfix] at hf
      exact hf ⟨a, ha⟩

/-- The literal lower image as a binary subspace. -/
def lowerSubspace [((S₂ D g h).subgroupOf (S₃ D g h)).Normal]
    [IsElementaryAbelian 2 (LowerQuotient D g h)] (A : Subgroup G) :
    Submodule (ZMod 2) (Additive (LowerQuotient D g h)) :=
  AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup (lowerImage D g h A))

omit d [Field F] [Finite F] [Finite G] in
theorem canonical_image_eq_lowerSubspace
    [((S₂ D g h).subgroupOf (S₃ D g h)).Normal]
    [IsElementaryAbelian 2 (LowerQuotient D g h)]
    {hLI : D.L ≤ I D g h} (e : StarComparison D g h hLI)
    (σ : Representation (ZMod 2) (D.star D.L) (Additive (LowerQuotient D g h)))
    (s : Representation.BinaryConjugationSection (I D g h) (S₃ D g h) (S₂ D g h)
      (σ.comp e.projection))
    (hq : ∀ a : S₃ D g h, (s.coordinates a).toAdd =
      Additive.ofMul (QuotientGroup.mk' ((S₂ D g h).subgroupOf (S₃ D g h)) a))
    (A : Subgroup G) : SectionGeometry.image s A = lowerSubspace A := by
  ext v
  constructor
  · rintro ⟨a, ha, he⟩
    refine ⟨a, ha, ?_⟩
    change (s.coordinates a).toAdd = v at he
    rw [hq] at he
    exact he
  · rintro ⟨a, ha, he⟩
    apply (SectionGeometry.mem_image s A v).mpr
    exact ⟨a, ha, (hq a).trans he⟩

/-- Full I-invariance and the genuine dual projective criterion on the literal
S₃/S₂ quotient, with its original coordinate map and all three marked values.
Only the earlier G.2.2 and G.2.5(1–3) structural inputs remain explicit. -/
theorem lower_projective_geometry (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (hLI : D.L ≤ I D g h)
    (hU : S D g h ≤ normalizer (D.U : Set G))
    (hUg : S D g h ≤ normalizer (conjugate D.U g : Set G))
    (hUh : S D g h ≤ normalizer (conjugate D.U h : Set G))
    (hgen : S D g h = (W D g h ⊔ conjugate (W D g h) g) ⊔ conjugate (W D g h) h)
    (e : StarComparison D g h hLI) (hrad : UpperRadicalIdentification d e) :
    I D g h ≤ normalizer (S₃ D g h : Set G) ∧
    letI := lower_normal d hUT hf hLI
    letI := lower_elementary d hUT hf hLI
    ∃ (σ : Representation (ZMod 2) (D.star D.L) (Additive (LowerQuotient D g h)))
      (s : Representation.BinaryConjugationSection (I D g h) (S₃ D g h) (S₂ D g h)
        (σ.comp e.projection))
      (φ : Point F (Module.Dual F (Fin 3 → F)) → Submodule (ZMod 2) (Additive (LowerQuotient D g h))),
      (∀ a : S₃ D g h, (s.coordinates a).toAdd =
        Additive.ofMul (QuotientGroup.mk' ((S₂ D g h).subgroupOf (S₃ D g h)) a)) ∧
      Criterion (dualAction d) σ φ ∧
      φ (dualPoint d) = lowerSubspace (W D g h ⊓ conjugate (W D g h) g) ∧
      φ (dualPointH d) = lowerSubspace (W D g h ⊓ conjugate (W D g h) h) ∧
      φ (dualPointGH d) = lowerSubspace (conjugate (W D g h) g ⊓ conjugate (W D g h) h) := by
  have hN := I_normalizes_third d hUT hf hLI hU hUg hUh e hrad
  refine ⟨hN, ?_⟩
  let := lower_normal d hUT hf hLI
  let := lower_elementary d hUT hf hLI
  obtain ⟨σ, s, hq⟩ := lower_action d hUT hf hLI hU hUg hUh hgen hN e
  refine ⟨σ, s, PointMap.map d e σ s, hq, PointMap.criterion d e σ s hUT hf hU hUg hrad, ?_⟩
  have hmark (i j : Fin 3) : PointMap.mark d e σ s i j = lowerSubspace (frameW d i ⊓ frameW d j) :=
    canonical_image_eq_lowerSubspace e σ s hq _
  rw [PointMap.mark_eq d e σ s hUT hf hrad,
    PointMap.pair_mark d e σ s hUT hf hrad 0 2 (by decide) (dualPointH d) rfl,
    PointMap.pair_mark d e σ s hUT hf hrad 1 2 (by decide) (dualPointGH d) rfl,
    hmark, hmark, hmark,
    (frameW_values d hLI).1, (frameW_values d hLI).2.1, (frameW_values d hLI).2.2]
  exact ⟨rfl, rfl, rfl⟩

section Homogeneous
attribute [local instance] ZMod.algebra
variable [CharP F 2]
  [((S₂ D g h).subgroupOf (S₃ D g h)).Normal]
  [IsElementaryAbelian 2 (LowerQuotient D g h)]
  {hLI : D.L ≤ I D g h} (e : StarComparison D g h hLI) {s : ℕ}
  (m : MarkedModel.Model d e s)

/-- An actual homogeneous dual equivalence sends all three original pair images
to the complete annihilator copies. The geometric bridges are proved here;
no marked-image assumption or prescribed image order remains. -/
theorem homogeneous_dual_marks (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (hrad : UpperRadicalIdentification d e) :
    (lowerImage D g h (W D g h ⊓ conjugate (W D g h) g)).map m.dualCoordinates.toMonoidHom =
      MarkedModel.copies (dualPoint d).val s ∧
    (lowerImage D g h (W D g h ⊓ conjugate (W D g h) h)).map m.dualCoordinates.toMonoidHom =
      MarkedModel.copies (dualPointH d).val s ∧
    (lowerImage D g h (conjugate (W D g h) g ⊓ conjugate (W D g h) h)).map
      m.dualCoordinates.toMonoidHom = MarkedModel.copies (dualPointGH d).val s :=
  m.dual_marks hUT hf (marked_model_bridges d e hrad)

/-- The genuine dot-product coordinates give all three one-dimensional marks
used in counting and restriction to the unchanged source L₁ actor. -/
theorem homogeneous_coordinate_marks (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (hrad : UpperRadicalIdentification d e) :
    (lowerImage D g h (W D g h ⊓ conjugate (W D g h) g)).map m.coordinates.toMonoidHom =
      ChiefFactors.lineCopies (MarkedModel.coordinateLine (dualPoint d).val) s ∧
    (lowerImage D g h (W D g h ⊓ conjugate (W D g h) h)).map m.coordinates.toMonoidHom =
      ChiefFactors.lineCopies (MarkedModel.coordinateLine (dualPointH d).val) s ∧
    (lowerImage D g h (conjugate (W D g h) g ⊓ conjugate (W D g h) h)).map
      m.coordinates.toMonoidHom = ChiefFactors.lineCopies (MarkedModel.coordinateLine (dualPointGH d).val) s :=
  m.coordinate_marks hUT hf (marked_model_bridges d e hrad)

include m in
/-- The orders of the three actual images, including the case of zero copies. -/
theorem homogeneous_card_images (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (hrad : UpperRadicalIdentification d e) :
    Nat.card (lowerImage D g h (W D g h ⊓ conjugate (W D g h) g)) = 2 ^ (n * s) ∧
    Nat.card (lowerImage D g h (W D g h ⊓ conjugate (W D g h) h)) = 2 ^ (n * s) ∧
    Nat.card (lowerImage D g h (conjugate (W D g h) g ⊓ conjugate (W D g h) h)) = 2 ^ (n * s) :=
  m.card_images hUT hf (marked_model_bridges d e hrad)
end Homogeneous

end CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.DualGeometry
