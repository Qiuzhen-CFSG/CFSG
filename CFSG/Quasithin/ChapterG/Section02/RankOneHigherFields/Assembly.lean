module

public import CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.Star
public import CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.CentralCover
public import CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.QuotientAction

/-!+# The seven conclusions of G.2.3 for n > 1

The natural line geometry proves the starred Sylow and Borel conclusions.
They supply the faithful Sylow lift in I/(WWᵍ); transfer eliminates its
central two-kernel. The resulting product gives an elementary quotient S/S₂
with its literal conjugation action. Its constructed projective orbit map
satisfies the universal G.1 criterion, giving the natural decomposition,
the marked fixed space, and the order formula with the same multiplicity.

`lemma_G_2_3` retains all seven source clauses and the original g. Its only
earlier-source inputs are U ≤ T and Φ(U) ≤ V₁ from G.2.2, and the universally
quantified G.1.3/G.1.5 recognition implication. The parent §G.2 assembly owns
their discharge (with recognition supplied by the G.1 owner). No starred
generation, Sylow, splitting, or quotient-decomposition premise remains.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.3, printed pp.333–334, PDF pp.344–345.
-/

@[expose] public section
open Subgroup
open scoped MatrixGroups Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields
open Setup QuotientAction.Projective
universe uG uF
variable {G : Type uG} [Group G] [Finite G]
variable {D : Setup G} {F : Type uF} [Field F] [Finite F]
  {n : ℕ} {g : G} (d : Hypothesis D F n g)

namespace Hypothesis
include d

/-- The higher-field central-cover conclusion with its starred premises
discharged by the natural line and Borel calculations. -/
theorem S_eq_WProduct_of_source (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) :
    D.S g = WProduct D g := by
  obtain ⟨P, hP⟩ := d.exists_star_U_sylow hUT hf
  exact d.S_eq_WProduct hUT (d.star_I_eq_star_L hUT hf) P hP
    (d.star_commutator_U_L₁ hUT hf)

/-- The elementary structure on the actual quotient, without a splitting
premise. This provides the binary module used in the assembled conclusion. -/
theorem quotient_elementary_of_source (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) :
    letI := d.quotientIntersection_normal hUT hf
    IsElementaryAbelian 2 ((D.S g) ⧸ (D.S₂ g).subgroupOf (D.S g)) :=
  d.quotient_elementary hUT hf (d.star_I_eq_star_L hUT hf)
    (d.S_eq_WProduct_of_source hUT hf)

/-- G.2.3 for n > 1, with all seven conclusions and the original conjugator.

The first five conjunctions give (1) the actual SL₂ model and Sylow image,
(2) I = LU, (3) S = WWᵍ, (4) the relative I-series with central first layer,
and (5) the central elementary second layer. The final witnesses give (6)
the actual quotient action, marked direct sum, natural copies and U*-fixed
space, and (7) the order formula, using the very same natural number s.
The projective map and its full criterion are also retained for inspection.

Only the exact earlier G.2.2 conclusions and the universal earlier G.1
recognition implication remain explicit; their source owners must supply
them when assembling the full §G.2 theorem. -/
theorem lemma_G_2_3 (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hrecognition : letI := d.field_char_two; RecognitionImplication.{uF, uG} F) :
    letI := d.quotientIntersection_normal hUT hf
    letI := d.quotient_elementary_of_source hUT hf
    letI := d.field_char_two
    (Nonempty ((D.star D.L ⊔ D.star D.U : Subgroup D.Star) ≃* SL(2, F)) ∧
      ∃ P : Sylow 2 (D.star D.L ⊔ D.star D.U : Subgroup D.Star),
        (P : Subgroup (D.star D.L ⊔ D.star D.U : Subgroup D.Star)).map
          (D.star D.L ⊔ D.star D.U).subtype = D.star D.U) ∧
    (D.I g = D.L ⊔ D.U ∧
      (D.I g : Set G) = (D.L : Set G) * (D.U : Set G) ∧ g ∈ D.I g) ∧
    ((D.S g : Set G) = (D.W g : Set G) * (conjugate (D.W g) g : Set G) ∧
      conjugate (D.W g) g = conjugate D.U g ⊓ D.S g) ∧
    (D.V ≤ D.S₂ g ∧ D.S₂ g ≤ D.S g ∧
      (D.V.subgroupOf (D.I g)).Normal ∧
      ((D.S₂ g).subgroupOf (D.I g)).Normal ∧
      ((D.S g).subgroupOf (D.I g)).Normal ∧
      D.V ≤ centralizer (D.S g : Set G)) ∧
    (⁅D.S₂ g, D.I g⁆ ≤ D.V ∧ IsElementaryAbelian 2 (D.S₂ g)) ∧
    ∃ (σ : Representation (ZMod 2) SL(2, F)
        (Additive ((D.S g) ⧸ (D.S₂ g).subgroupOf (D.S g))))
      (c : Representation.BinaryConjugationSection (D.I g) (D.S g) (D.S₂ g)
        (σ.comp (d.quotientActionProjection hUT (d.star_I_eq_star_L hUT hf))))
      (φ : Point F → Submodule (ZMod 2)
        (Additive ((D.S g) ⧸ (D.S₂ g).subgroupOf (D.S g))))
      (s : ℕ),
      (∀ x : D.S g, (c.coordinates x).toAdd =
        Additive.ofMul (QuotientGroup.mk' ((D.S₂ g).subgroupOf (D.S g)) x)) ∧
      Criterion σ φ ∧
      φ ⟨d.point, d.point_dimension⟩ = c.imageSpace (D.W g) ∧
      φ (translate (d.quotientActionProjection hUT (d.star_I_eq_star_L hUT hf)
        (⟨g, d.g_mem_I hUT hf⟩ : D.I g)⁻¹)
        ⟨d.point, d.point_dimension⟩) = c.imageSpace (conjugate (D.W g) g) ∧
      IsCompl (c.imageSpace (D.W g)) (c.imageSpace (conjugate (D.W g) g)) ∧
      NaturalCopies σ s ∧
      c.imageSpace (D.W g) = Representation.BinaryOffender.fixedSpace σ
        (d.quotientRoot hUT (d.star_I_eq_star_L hUT hf)) ∧
      (D.S₂ g).relIndex (D.W g) = 2 ^ (n * s) ∧
      Nat.card D.U = 2 ^ (n * (s + 3)) * D.V.relIndex (D.S₂ g) := by
  let := d.quotientIntersection_normal hUT hf
  let := d.quotient_elementary_of_source hUT hf
  let := d.field_char_two
  obtain ⟨hVS₂, hS₂S, hnV, hnS₂, hnS, hcentral, hcomm, helem⟩ := d.series hUT hf
  have hproduct : (D.S g : Set G) =
      (D.W g : Set G) * (conjugate (D.W g) g : Set G) := by
    rw [d.S_eq_WProduct_of_source hUT hf]
    exact d.WProduct_eq_product hUT (d.star_I_eq_star_L hUT hf).ge
  refine ⟨⟨⟨d.starJoinEquiv hUT hf⟩, d.exists_starJoin_U_sylow hUT hf⟩,
    ⟨d.I_eq_LU hUT hf, d.I_product hUT hf, d.g_mem_I hUT hf⟩,
    ⟨hproduct, conjugate_W (d.g_mem_I hUT hf)⟩,
    ⟨hVS₂, hS₂S, hnV, hnS₂, hnS, hcentral⟩, ⟨hcomm, helem⟩, ?_⟩
  exact d.exists_quotient_natural_decomposition hUT hf (d.star_I_eq_star_L hUT hf)
    (d.exists_star_U_sylow hUT hf) (d.card_star_U hUT hf)
    (d.star_L₁_eq_normalizer hUT hf) (d.S_eq_WProduct_of_source hUT hf) hrecognition

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields
