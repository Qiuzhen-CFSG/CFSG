module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.SmallUnitaryConstituents
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.BinaryCatalogue
public import Theory.Representation.RankOne.QuadraticRecognition.DihedralResidual

/-!
# The full source catalogue in the Chapter 9 module comparison

The binary-model estimate extends to every retained source row. In D10 the
actual quotient has trivial two-core, and residual-fixed-space vanishing
forces faithfulness. Its separate quadratic square bound prevents the strict
comparison that selects a linear group. All other rows use the concrete
binary-model adapter, with the same action, actor and residual.

The mixed and reciprocal initial recognition consumers use this statement
before constructing any natural residual section, avoiding circular exclusion
of the dihedral row. Source: DGS, Groups and Graphs (1985), 9.3, p.142.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
universe u

/-- The literal generated-module bound and strict linear selection for every
row of the source rank-one catalogue, including D10. -/
theorem generated_source_rank_one_bound_and_selection
    {H D : Type u} [Group H] [Finite H] [Group D] [Finite D]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W] [Nontrivial W]
    (e₀ : (H ⧸ pCore 2 H) ≃* D) (M : IsRankOneModel D)
    (ρ : Representation (ZMod 2) D W) (S : Sylow 2 D)
    (A : Subgroup D) [IsElementaryAbelian 2 A] (hAS : A ≤ S)
    (hq : IsQuadratic ρ A) (hg : GeneratedByFixedSpace ρ S)
    (hr : fixedSpace ρ (pResidual 2 D) = ⊥) :
    Nat.card A ≤ Nat.card (W ⧸ fixedSpace ρ A) ∧
      (Nat.card (W ⧸ fixedSpace ρ A) < Nat.card A ^ 2 →
        ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (n : ℕ),
          0 < n ∧ Nat.card F = 2^n ∧ Nonempty (D ≃* SL(2,F))) := by
  by_cases hd : Nonempty (D ≃* DihedralGroup 5)
  · obtain ⟨ed⟩ := hd
    have hc : Nat.card D = 10 := by
      rw [Nat.card_congr ed.toEquiv, DihedralGroup.nat_card]
    have hcore : pCore 2 D = ⊥ := by
      rw [←pCore_map_iso 2 e₀, pCore_quotient_pCore_eq_bot, Subgroup.map_bot]
    have hs := card_ten_residual_fixed_quadratic_square_bound hc hcore ρ hr A
      (IsElementaryAbelian.isPGroup 2 A) hq
    exact ⟨(Nat.le_self_pow (by decide) _).trans hs,
      fun hlt => (Nat.not_lt_of_ge hs hlt).elim⟩
  · obtain ⟨M'⟩ := M.binaryModel_of_not_dihedral hd
    exact generated_rank_one_bound_and_selection e₀ M' ρ S A hAS hq hg hr

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
