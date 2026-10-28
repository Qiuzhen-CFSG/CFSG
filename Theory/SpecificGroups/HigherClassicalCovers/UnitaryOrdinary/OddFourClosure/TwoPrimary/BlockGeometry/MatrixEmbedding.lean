module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.TwoPrimary.BlockModel
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.TwoPrimary.BlockGeometry.Fusion

/-!
# Matrix input for the unitary block-pair construction

This interface isolates the semidirect-product embedding and transverse
rank-one torus from the two involution fusions. It specifies the actual
matrix values of the plane sign, rotation and reflection. The second
reflection's matrix and both fusions are proved from these values below.
Existence of the embedding is a separate geometric obligation: this module
does not assume or assert any covering or index conclusion.

Source: the orthogonal-plane stabilizer calculation supporting
Aschbacher--Smith I.1.4(3), printed p.408, and GLS3 §6.1.
-/

public section
open Matrix BenderSuzuki.MatrixGroups

namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.TwoPrimary.BlockGeometry

variable {F : Type*} [Field F]

/-- The matrix embedding before fusion. In the intended construction `a`
generates the norm-one units, the base acts on the two coordinate planes,
and the transverse factor acts on coordinates 0 and 2. -/
structure MatrixEmbedding (J : HermitianForm 4 F) (q : ℕ) [Fact q.Prime] where
  action : DihedralGroup (q + 1) →* MulAut (RankOne q × RankOne q)
  inclusion : (RankOne q × RankOne q) ⋊[action] DihedralGroup (q + 1) →*
    J.specialSubgroup
  injective : Function.Injective inclusion
  transverse : RankOne q →* J.specialSubgroup
  transverse_injective : Function.Injective transverse
  torus : RankOne q
  torus_pow : torus ^ (q + 1) = 1
  rotation_eq : transverse torus = inclusion (SemidirectProduct.inr (.r 1))
  a : Fˣ
  norm_a : J.conj (a : F) = (a⁻¹ : Fˣ)
  base_sign_matrix : (inclusion (SemidirectProduct.inl (-1, 1))).val.val = planeSign
  rotation_matrix : (inclusion (SemidirectProduct.inr (.r 1))).val.val = rotationMatrix a
  reflection_matrix : (inclusion (SemidirectProduct.inr (.sr 0))).val.val = weightedSwap 1

variable {J : HermitianForm 4 F} {q : ℕ} [Fact q.Prime]

/-- The literal dihedral multiplication convention gives the weighted reflection. -/
theorem MatrixEmbedding.reflection_one_matrix (m : MatrixEmbedding J q) :
    (m.inclusion (SemidirectProduct.inr (.sr 1))).val.val = weightedSwap m.a := by
  rw [show (DihedralGroup.sr (1 : ZMod (q + 1))) = .sr 0 * .r 1 by simp,
    map_mul, map_mul]
  change (m.inclusion (SemidirectProduct.inr (.sr 0))).val.val *
    (m.inclusion (SemidirectProduct.inr (.r 1))).val.val = _
  rw [m.reflection_matrix, m.rotation_matrix, ← weightedSwap_eq_swap_mul_rotation]

/-- The explicit special-unitary conjugators discharge both fusion fields of
the published block model. Only the embedding and torus data remain inputs. -/
noncomputable def MatrixEmbedding.toBlockModel [Finite F]
    (m : MatrixEmbedding J q) (hJ : J.form = 1)
    (hq : 3 < q) (hc : Nat.card F = q ^ 2) (hj : ∀ x, J.conj x = x ^ q) :
    BlockModel J q where
  action := m.action
  inclusion := m.inclusion
  injective := m.injective
  transverse := m.transverse
  transverse_injective := m.transverse_injective
  torus := m.torus
  torus_pow := m.torus_pow
  rotation_eq := m.rotation_eq
  reflection_zero_conjugate := isConj_planeSign_weightedSwap J hJ hq hc hj
    1 (by simp) _ _ m.base_sign_matrix m.reflection_matrix
  reflection_one_conjugate := isConj_planeSign_weightedSwap J hJ hq hc hj
    m.a m.norm_a _ _ m.base_sign_matrix m.reflection_one_matrix

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.TwoPrimary.BlockGeometry
