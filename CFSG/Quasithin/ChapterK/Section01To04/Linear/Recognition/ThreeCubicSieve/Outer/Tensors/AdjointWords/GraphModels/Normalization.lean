module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.AdjointWords.Models
public import Theory.GroupTheory.PerfectCentralCoverExistence
public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.Graph

/-!
# Central-kernel normalization of the graph action

Squaring the literal intertwining equation gives the identity automorphism on
its representation image. Uniqueness of maps from a perfect group through a
central kernel then gives square one on SL₃ itself. The existing projective
matrix calculation consequently makes the inner-diagonal graph matrix symmetric.
Neither faithfulness on SL₃ nor absolute irreducibility over the binary field
is needed. This is the group normalization used by the actual tensor model.

Source: GM, Classification of 2F-modules II, Proposition 4.8 step 3A,
manuscript p.27; Aschbacher–Smith K.3.2, printed pp.454–456.
-/

public section
set_option backward.isDefEq.respectTransparency false
open Representation Representation.BinaryOffender
open Representation.BinaryOffender.SchurNormalizer
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups TensorProduct
open Matrix.PSL3.OuterSolvable
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.AdjointWords
variable {B : BinaryField} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    {σ : Representation (ZMod 2) SL(3,B.Carrier) V} [IsIrreducible σ]

omit [FiniteDimensional (ZMod 2) V] [IsIrreducible σ] in
/-- The induced component automorphism squares to one on the actual cover. -/
theorem component_square {t : linearNormalizer σ} (ht : t ^ 2 = 1)
    (hk : σ.ker ≤ Subgroup.center _) (α : MulAut SL(3,B.Carrier))
    (hi : ∀ g, t.val.val * σ g = σ (α g) * t.val.val) : α ^ 2 = 1 := by
  let : Group.IsPerfect SL(3,B.Carrier) := Atlas.sl_perfect 3 (by decide)
  have ht2 : t.val.val * t.val.val = 1 := by
    have h := congrArg (fun u : linearNormalizer σ => u.val.val) ht
    simpa only [pow_two, Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one,
      Units.val_one] using h
  have he (g) : σ (α (α g)) = σ g := by
    calc
      σ (α (α g)) = σ (α (α g)) * (t.val.val * t.val.val) := by rw [ht2, mul_one]
      _ = t.val.val * (t.val.val * σ g) := by rw [← mul_assoc, ← hi, mul_assoc, ← hi]
      _ = σ g := by rw [← mul_assoc, ht2, one_mul]
  apply MulEquiv.toMonoidHom_injective
  apply PerfectCentralCovering.monoidHom_eq_of_isPerfect_of_comp_eq σ.asGroupHom
    (by
      intro g hg
      apply hk
      exact congrArg Units.val hg)
  apply MonoidHom.ext
  intro g
  apply Units.ext
  exact he g

omit [FiniteDimensional (ZMod 2) V] [IsIrreducible σ] in
/-- The literal conjugating matrix of a graph involution is symmetric. -/
theorem graph_matrix_symmetric {t : linearNormalizer σ} (ht : t ^ 2 = 1)
    (hk : σ.ker ≤ Subgroup.center _) (c : GL (Fin 3) B.Carrier)
    (hi : ∀ g, t.val.val * σ g =
      σ (linearConjSL B.Carrier c (graphSL B.Carrier g)) * t.val.val) :
    c.val.transpose = c.val := by
  have h := component_square ht hk (linearConjSL B.Carrier c * graphSL B.Carrier) hi
  apply Matrix.PSL3.OddInvolutionFixed.graph_involution_symmetric c
  have he := congrArg (centerAction B.Carrier) h
  simpa only [map_pow, map_mul, map_one, linearConj, graph, MonoidHom.comp_apply] using he
end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.AdjointWords
