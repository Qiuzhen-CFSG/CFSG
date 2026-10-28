module
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.HigherRank.RootRelations
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.HigherRank.Blocks
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.NaturalDualCohomology

/-!
# Common-center quadratic roots in actual dual extensions

An ordinary section of the original quotient gives matrix derivations.
The sparse root identities force their double displacement to vanish.
The dot-product identification uses inverse transpose on the quotient,
and the final application pulls the actors back through the original
natural marking. No splitting or FF hypothesis is used.

This is the dual-orientation matrix step for Aschbacher–Smith B.4.9(2)(i),
printed pp.92–95, in every higher binary dimension.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Representation Matrix
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.HigherRank
open QuasisimpleSource

noncomputable def dualCoordinates (n : ℕ) :=
  (specialLinearNatural (k := ZMod 2) n).comp (BinaryLinear.OuterCyclic.graphSL n).toMonoidHom

private lemma natural_matrix {n : ℕ} (g : SpecialLinearGroup (Fin n) (ZMod 2)) :
    LinearMap.toMatrix' (specialLinearNatural (k := ZMod 2) n g) = g.val :=
  LinearMap.toMatrix'_toLin' g.val

private lemma dual_matrix {n : ℕ} (g : SpecialLinearGroup (Fin n) (ZMod 2)) :
    LinearMap.toMatrix' (dualCoordinates n g) = (g⁻¹).val.transpose := by
  change LinearMap.toMatrix' (specialLinearNatural (k := ZMod 2) n
    (BinaryLinear.OuterCyclic.graphSL n g)) = _
  rw [natural_matrix]
  change ((SpecialLinearGroup.transpose g)⁻¹).val = _
  exact (Matrix.adjugate_transpose g.val).symm

private noncomputable def dualCoordinateEquiv (n : ℕ) :
    (specialLinearNatural (k := ZMod 2) n).dual.Equiv (dualCoordinates n) :=
  .mk (dualNaturalEquiv n).linearEquiv (by
    intro g
    apply LinearMap.ext
    intro v
    exact (dualNaturalEquiv n).intertwines g v)

private lemma natural_root_matrix {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    LinearMap.toMatrix' (specialLinearNatural (k := ZMod 2) n
      (SpecialLinearGroup.transvection hij 1) - 1) = Matrix.single i j 1 := by
  rw [map_sub, natural_matrix, LinearMap.toMatrix'_one, SpecialLinearGroup.transvection_coe]
  exact add_sub_cancel_left _ _

private lemma dual_root_matrix {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    LinearMap.toMatrix' (dualCoordinates n (SpecialLinearGroup.transvection hij 1) - 1) =
      Matrix.single j i 1 := by
  rw [map_sub, dual_matrix, LinearMap.toMatrix'_one, SpecialLinearGroup.transvection_inv,
    CharTwo.neg_eq, SpecialLinearGroup.transvection_coe]
  simp

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The off-diagonal calculation gives quadratic root pairs on the original
extension, with the quotient identified with the literal contragredient. -/
theorem dual_extension_root_product {n : ℕ} (hn : 5 ≤ n)
    (ρ : Representation (ZMod 2) (SpecialLinearGroup (Fin n) (ZMod 2)) V)
    (N : Subrepresentation ρ)
    (en : N.toRepresentation.Equiv (specialLinearNatural (k := ZMod 2) n))
    (eq : N.quotientRepresentation.Equiv (specialLinearNatural (k := ZMod 2) n).dual)
    {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) :
    (ρ (SpecialLinearGroup.transvection hij 1) - 1) *
      (ρ (SpecialLinearGroup.transvection hik 1) - 1) = 0 := by
  obtain ⟨b⟩ := exists_extensionBlocks N en (eq.trans (dualCoordinateEquiv n))
  let c (g : SpecialLinearGroup (Fin n) (ZMod 2)) := LinearMap.toMatrix' (b.block g)
  have hc : IsDualDerivation c := by
    intro g h
    dsimp only [c]
    rw [b.derivation, map_add, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp,
      natural_matrix, dual_matrix]
  apply b.displacement_product
  · apply LinearMap.toMatrix'.injective
    rw [LinearMap.toMatrix'_mul, natural_root_matrix, natural_root_matrix, map_zero]
    exact Matrix.single_mul_single_of_ne _ _ _ _ hij.symm _
  · apply LinearMap.toMatrix'.injective
    rw [LinearMap.toMatrix'_mul, dual_root_matrix, dual_root_matrix, map_zero]
    exact Matrix.single_mul_single_of_ne _ _ _ _ hik _
  · apply LinearMap.toMatrix'.injective
    rw [map_add, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp,
      natural_root_matrix, dual_root_matrix, map_zero]
    exact dualDerivation_root_product hn hc hij hik

end CFSG.Quasithin.ChapterB.NaturalExtensions.HigherRank
