module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.DegreeDivisibility.ModelTransitivity.Transport
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.LinearGeometry
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.SuzukiGeometry
public import Theory.SpecificGroups.PSL2.InvolutionFusion
public import Theory.SpecificGroups.Suzuki.InvolutionFusion

/-!
# Root fusion in the linear and Suzuki models

The concrete groups have a single involution class. Their Sylow omega
subgroups are elementary abelian, so their nonidentity elements fuse.
Together with the embedded-center equality this gives Sylow-normalizer
transitivity by the transport leaf's Burnside argument.

Source: GLS4, Chapter 4, Lemma 3.2(b,c), used in Chapter 2, 16.4(c).
-/

namespace BenderSuzuki.ZD.Source16ModelTransitivity
open Subgroup _root_.BenderSuzuki.MatrixGroups RankOneModelGeometry
variable {G : Type*} [Group G] [Finite G]

public theorem linear_omega_fusion {n : ℕ} (hn : 0 < n)
    (e : G ≃* PSL2BinaryMatrixGroup n) (P : Sylow 2 G) :
    ∀ z ∈ omegaOneAmbient (P : Subgroup G), z ≠ 1 →
      ∀ x ∈ omegaOneAmbient (P : Subgroup G), x ≠ 1 → IsConj z x := by
  let : IsElementaryAbelian 2 (omegaOneAmbient (P : Subgroup G)) :=
    (LinearGeometry.omega_geometry hn e P).2.2.1
  intro z hz hz1 x hx hx1
  have hi (a : G) (ha : a ∈ omegaOneAmbient (P : Subgroup G)) (ha1 : a ≠ 1) :
      orderOf (e a) = 2 := by
    rw [e.orderOf_eq]
    exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian a ha) ha1
  have hh := e.symm.toMonoidHom.map_isConj
    (Theory.PSL2.involutions_isConj (e z) (e x) (hi z hz hz1) (hi x hx hx1))
  simpa only [MulEquiv.coe_toMonoidHom,e.symm_apply_apply] using hh

public theorem suzuki_omega_fusion {m : ℕ} (hm : 1 ≤ m)
    (e : G ≃* SuzukiMatrixGroup m) (P : Sylow 2 G) :
    ∀ z ∈ omegaOneAmbient (P : Subgroup G), z ≠ 1 →
      ∀ x ∈ omegaOneAmbient (P : Subgroup G), x ≠ 1 → IsConj z x := by
  let : IsElementaryAbelian 2 (omegaOneAmbient (P : Subgroup G)) :=
    (suzuki_omega_geometry hm e P).2.1
  intro z hz hz1 x hx hx1
  have hi (a : G) (ha : a ∈ omegaOneAmbient (P : Subgroup G)) (ha1 : a ≠ 1) :
      orderOf (e a) = 2 := by
    rw [e.orderOf_eq]
    exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian a ha) ha1
  have hh := e.symm.toMonoidHom.map_isConj
    (suzuki_involutions_isConj m hm (e z) (e x) (hi z hz hz1) (hi x hx hx1))
  simpa only [MulEquiv.coe_toMonoidHom,e.symm_apply_apply] using hh

end BenderSuzuki.ZD.Source16ModelTransitivity
