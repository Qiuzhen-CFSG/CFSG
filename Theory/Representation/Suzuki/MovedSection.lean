module
public import Theory.Representation.Suzuki.AbelianIntersection
/-!
# Moved Suzuki sections inside literal subgroups

A faithful binary Suzuki action, restricted to a full Sylow omega, moves
at least the square of the defining field order. Apply the proved square
bound to the dual representation and identify its fixed codimension with
the original moved dimension. The quotient-image commutator formula then
places this moved space in any specified subgroup containing [D,X].

The DGS (12.9) application uses D = Q_beta, K = G_beta^(2), and the
actual radius-two center span intersected with Q_beta. This supplies the
strict growth step on printed p.189, with the original quotient maps.
-/
public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender
open BenderSuzuki.MatrixGroups
namespace Subgroup
variable {G : Type*} [Group G]
/-- The moved image of a full Suzuki Sylow omega forces a square-field
lower bound in every subgroup containing the literal commutator. -/
theorem suzuki_commutator_section_index_lower
    (D K X P : Subgroup G) [Finite D] [(K.subgroupOf D).Normal]
    [IsElementaryAbelian 2 (D ⧸ K.subgroupOf D)]
    (hP : P ≤ D) (hXD : X ≤ normalizer (D : Set G))
    {n : ℕ} (hn : 0 < n)
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup n)
      (Additive (D ⧸ K.subgroupOf D))) (hf : Function.Injective ρ)
    (f : X →* SuzukiMatrixGroup n) (T : Sylow 2 (SuzukiMatrixGroup n))
    (hT : f.range = omegaOneAmbient (T : Subgroup _))
    (hρ : ∀ x : X, ∀ y : D,
      ρ (f x) (Additive.ofMul (QuotientGroup.mk y)) =
        Additive.ofMul (QuotientGroup.mk ⟨(x : G) * y * (x : G)⁻¹,
          le_normalizer_iff.mp hXD x x.property y y.property⟩))
    (hcomm : ⁅D,X⁆ ≤ P) : (2^(2*n+1))^2 ≤ K.relIndex P := by
  let W := Additive (D ⧸ K.subgroupOf D)
  let π := QuotientGroup.mk' (K.subgroupOf D)
  let E := omegaOneAmbient (T : Subgroup (SuzukiMatrixGroup n))
  let M := quotientImage D π P
  let : IsElementaryAbelian 2 E := suzukiSylow_omega_elementary hn (MulEquiv.refl _) T
  have hEcard : Nat.card E = 2^(2*n+1) := suzukiSylow_omega_card hn (MulEquiv.refl _) T
  have hEbig : 2 < Nat.card E := by
    rw [hEcard]
    exact (show 2 = (2:ℕ)^1 by norm_num).trans_lt
      (Nat.pow_lt_pow_right (by decide) (by omega))
  have htop : quotientImage D π D = ⊤ := by
    apply top_unique
    intro v _
    obtain ⟨y,hy⟩ := QuotientGroup.mk'_surjective (K.subgroupOf D) v.toMul
    exact ⟨y,y.property,hy⟩
  have hm : subspaceCommutator ρ ⊤ E ≤ M := by
    have he := quotientImage_commutator ρ D D X hXD le_rfl f π
      (QuotientGroup.mk'_surjective _) hρ
    rw [htop,hT] at he
    rw [←he]
    change ((⁅D,X⁆).subgroupOf D).map π ≤ (P.subgroupOf D).map π
    exact map_mono (subgroupOf_mono D hcomm)
  let : Finite (Module.Dual (ZMod 2) W) := Finite.of_injective
    (fun f : Module.Dual (ZMod 2) W => (f : W → ZMod 2)) DFunLike.coe_injective
  have hdual := Representation.RankOne.QuadraticRecognition.suzuki_noncyclic_square_bound
    hn ρ.dual (faithful_dual ρ hf) T E (omegaOneAmbient_le _) hEbig
  have hdualcard : Nat.card (Module.Dual (ZMod 2) W ⧸ fixedSpace ρ.dual E) =
      Nat.card (subspaceCommutator ρ ⊤ E) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2)
        (V := Module.Dual (ZMod 2) W ⧸ fixedSpace ρ.dual E),
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := subspaceCommutator ρ ⊤ E)]
    exact congrArg (fun d => Nat.card (ZMod 2)^d) (fixedCodim_dual_eq_moved_finrank ρ E)
  rw [hdualcard,hEcard] at hdual
  have hlow := hdual.trans
    (Nat.card_le_card_of_injective (Submodule.inclusion hm) (Submodule.inclusion_injective hm))
  have hindex : Nat.card M = K.relIndex P := by
    rw [←binarySubgroup_card]
    change Nat.card ((P.subgroupOf D).map π) = _
    rw [←relIndex_ker,QuotientGroup.ker_mk',relIndex_subgroupOf hP]
  exact hlow.trans_eq hindex
end Subgroup
