module

public import CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.QuotientAction.MarkedRoot
public import CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.QuotientAction.ProjectiveOrbit.Geometry

/-!
# The projective map on the actual G.2.3 quotient

The preceding quotient construction supplies the representation on the literal
additive group of S/S₂, its marked complementary W and Wᵍ images, and the
displacement, fixation and normalizer bounds for the original field line.
The orbit construction now proves every G.1.3 clause for that representation.
The marked translate uses the projection of the original g⁻¹, so its image is
the specified right conjugate Wᵍ, without replacing the conjugator.

The earlier Frattini, starred-group, Sylow, Borel and splitting outputs remain
explicit. Final G.2.3 assembly discharges these earlier-source premises and
applies the G.1 recognition theorem and the counting lemmas.
No recognition or natural-decomposition witness is used here.

Source: Aschbacher–Smith, G.2.3(6), printed pp.333–334, PDF pp.344–345,
and G.1.5(3), printed p.328, PDF p.339.
-/

@[expose] public section
open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields
open Setup QuotientAction.Projective
variable {G : Type*} [Group G] [Finite G]
variable {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g : G} (d : Hypothesis D F n g)

namespace Hypothesis

/-- The literal S/S₂ action and its marked projective map satisfy the full
G.1.3 criterion. This discharges the projective-map premise in G.2.3(6). -/
theorem exists_quotient_projective_map (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hstar : D.star (D.I g) = D.star D.L)
    (hSylow : ∃ P : Sylow 2 (D.star D.L),
      (P : Subgroup (D.star D.L)).map (D.star D.L).subtype = D.star D.U)
    (hB : D.star D.L₁ = D.star D.L ⊓ normalizer (D.star D.U : Set D.Star))
    (hsplit : D.S g = WProduct D g) :
    letI := d.quotientIntersection_normal hUT hf
    letI := d.quotient_elementary hUT hf hstar hsplit
    ∃ (σ : Representation (ZMod 2) SL(2, F)
        (Additive ((D.S g) ⧸ (D.S₂ g).subgroupOf (D.S g))))
      (c : Representation.BinaryConjugationSection (D.I g) (D.S g) (D.S₂ g)
        (σ.comp (d.quotientActionProjection hUT hstar)))
      (φ : Point F → Submodule (ZMod 2)
        (Additive ((D.S g) ⧸ (D.S₂ g).subgroupOf (D.S g)))),
      (∀ s : D.S g, (c.coordinates s).toAdd =
        Additive.ofMul (QuotientGroup.mk' ((D.S₂ g).subgroupOf (D.S g)) s)) ∧
      Criterion σ φ ∧
      φ ⟨d.point, d.point_dimension⟩ = c.imageSpace (D.W g) ∧
      φ (translate (d.quotientActionProjection hUT hstar
        (⟨g, d.g_mem_I_of_star hUT hstar.ge⟩ : D.I g)⁻¹)
        ⟨d.point, d.point_dimension⟩) = c.imageSpace (conjugate (D.W g) g) := by
  let := d.quotientIntersection_normal hUT hf
  let := d.quotient_elementary hUT hf hstar hsplit
  obtain ⟨σ, c, hcoord, hcompl, hmove, hroot, hN⟩ :=
    d.exists_quotient_root_configuration hUT hf hstar hSylow hB hsplit
  let A : Point F := ⟨d.point, d.point_dimension⟩
  let t := d.quotientActionProjection hUT hstar
    (⟨g, d.g_mem_I_of_star hUT hstar.ge⟩ : D.I g)⁻¹
  have hcompl' : IsCompl (c.imageSpace (D.W g)) ((c.imageSpace (D.W g)).map (σ t)) := by
    rw [← hmove]
    exact hcompl
  obtain ⟨φ, hA, hφ, hcriterion⟩ := exists_orbit_criterion σ A (c.imageSpace (D.W g)) t
    (d.quotient_marked_point_ne hUT hstar) hcompl' hN hroot
  exact ⟨σ, c, φ, hcoord, hcriterion, hA,
    (hφ t (translate t A) (translate_val t A)).trans hmove.symm⟩

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields
