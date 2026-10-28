module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.CoreFusion
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.ComponentGeneration
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.StrongEmbedding
public import BenderSuzuki.SE.SingleInvolutionClass
/-!
# Global connectedness of the original cubic geometry

All Sylow involutions are fused to z inside the actual component
stabilizer. Sylow conjugacy within this subgroup gives one involution
class. It contains the full C_G(z), so if proper it is strongly embedded,
contrary to the proved original IsType obstruction. Thus the component
stabilizer is G, the geometry is connected with 280 points, G is generated
by its original point and line normalizers, and |G|=3265920.
Source: Aschbacher, Sporadic Groups (1994),45.10(9)–(10) and45.11, pp.248–249.
-/
public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsType z}
variable {P : Sylow 3 (centralizer z)} (c : SourceConfiguration h P)
theorem component_involution_fused (v:G) (hv : v∈c.componentStabilizer) (hv2 : orderOf v=2) :
    ∃g∈c.componentStabilizer,g*z*g⁻¹=v := by
  obtain ⟨R⟩ := h.exists_rootPair
  obtain ⟨S,hS⟩ := R.exists_sylow_T h
  have hSH : (S:Subgroup G)≤c.componentStabilizer := by
    rw [hS]
    exact R.T_le_centralizer.trans c.centralizer_le_componentStabilizer
  let H := c.componentStabilizer
  let SH : Sylow 2 H := S.subtype hSH
  let vH : H := ⟨v,hv⟩
  have hvH : orderOf vH=2 := (orderOf_coe vH).symm.trans hv2
  have hp : IsPGroup 2 (zpowers vH) := IsPGroup.of_card (n:=1) (by
    rw [Nat.card_zpowers,hvH,pow_one])
  obtain ⟨U,hU⟩ := hp.exists_le_sylow
  obtain ⟨a,ha⟩ := MulAction.exists_smul_eq H U SH
  have hm : MulAut.conj a vH∈(SH:Subgroup H) := by
    rw [←ha,Sylow.smul_def,Sylow.pointwise_smul_def]
    exact smul_mem_pointwise_smul vH (MulAut.conj a) (U:Subgroup H) (hU (mem_zpowers vH))
  change (a:G)*v*(a:G)⁻¹∈(S:Subgroup G) at hm
  rw [hS] at hm
  have ho : orderOf ((a:G)*v*(a:G)⁻¹)=2 := ((MulAut.conj (a:G)).orderOf_eq v).trans hv2
  obtain ⟨k,hk,hkv⟩ := c.sylow_involution_fused_in_component R _ hm ho
  refine ⟨(a:G)⁻¹*k,H.mul_mem (H.inv_mem a.property) hk,?_⟩
  calc
    _ = (a:G)⁻¹*(k*z*k⁻¹)*(a:G) := by group
    _ = v := by rw [hkv]; group

/-- The original local geometry has no other component. -/
theorem componentStabilizer_eq_top : c.componentStabilizer=⊤ := by
  by_contra hproper
  exact c.componentStabilizer_not_stronglyEmbedded
    (BenderSuzuki.isStronglyEmbedded_of_single_involution_class c.componentStabilizer hproper z
      h.involution (c.core_le_componentStabilizer (RootPair.z_mem_core h))
      c.centralizer_le_componentStabilizer c.component_involution_fused)


theorem original_point_reachable (U : c.points) :
    c.collinearity.Reachable ⟨c.W,c.point_mem⟩ U := by
  obtain ⟨g,hg⟩ := U.property
  have hm : g∈c.componentStabilizer := c.componentStabilizer_eq_top ▸ mem_top g
  have he : c.conjugatePoint ⟨c.W,c.point_mem⟩ g=U := Subtype.ext hg.symm
  exact he ▸ hm

theorem collinearity_connected : c.collinearity.Connected :=
  c.collinearity.connected_iff_exists_forall_reachable.mpr ⟨⟨c.W,c.point_mem⟩,c.original_point_reachable⟩

theorem points_card : Nat.card c.points=280 := by
  let e : {U : c.points // c.collinearity.Reachable ⟨c.W,c.point_mem⟩ U} ≃ c.points := {
    toFun := Subtype.val
    invFun := fun U=>⟨U,c.original_point_reachable U⟩
    left_inv := fun _=>rfl
    right_inv := fun _=>rfl }
  exact (Nat.card_congr e).symm.trans c.component_card

include c in
theorem ambient_card : Nat.card G=3265920 := by
  rw [←card_top (G:=G),←c.componentStabilizer_eq_top,c.componentStabilizer_card]

theorem ambient_eq_normalizers_sup :
    normalizer (c.W:Set G)⊔normalizer (c.V:Set G)=⊤ :=
  c.componentStabilizer_eq_normalizers_sup.symm.trans c.componentStabilizer_eq_top

end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
