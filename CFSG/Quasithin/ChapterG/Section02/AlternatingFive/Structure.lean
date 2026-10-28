module

public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Structure.KernelGeometry
public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Structure.CentralKernel
public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Structure.Starred
public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Structure.OrthogonalGeometry
public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Block.Inputs
public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Recognition.Counting

/-!
# The structure and orthogonal geometry of G.2.4

The original Sylow hypothesis and equivariant five-point core identify the
point stabilizer as a Borel and U* as its Sylow four-group. The original g
moves that point, so starred generation lifts to I=LU. Transfer eliminates
the central kernel of I/WWᵍ, giving S=WWᵍ as an actual set product.

These proved starred facts discharge all premises of the orthogonal geometry:
V_L∩U=V, |V|=8, |V_L|=16 and V∨Vᵍ=V_L. The literal star restriction has
kernel O₂(I), hence [U:W]=4. We construct the structural input used by the
terminal branch and apply the intersection to the counting denominator.
Generation also discharges L≤I in the orthogonal layers, proving (4–5).

Thus (1–5) and the required geometry are unconditional under Hypothesis.
The natural upper layer and terminal block recognition remain separate.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.4, printed pp.334–335.
-/

public section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section02.AlternatingFive
open Setup
namespace Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G}
  (d : Hypothesis D g)
include d

/-- The core in the quotient agrees with the image of the original local
core; the two constructions are compared through the actual star map. -/
theorem star_U_eq_star_local_core : D.star D.U = D.star (D.L₁.pCoreIn 2) :=
  d.star_U_eq_local_core.trans star_local_core.symm

/-- G.2.4(2), for the original source conjugator. -/
theorem I_eq_LU : D.I g = D.L ⊔ D.U := d.I_eq_LU_of_starred

theorem L_le_I : D.L ≤ D.I g := d.L_le_I_of_star d.star_I_eq_L.ge

theorem g_mem_I : g ∈ D.I g := d.L_le_I d.g_mem

/-- The source's product LU is a literal ordered set product. -/
theorem I_product : (D.I g : Set G) = (D.L : Set G) * (D.U : Set G) :=
  d.I_product_of_star d.star_I_eq_L.ge

/-- G.2.4(3), as an equality of subgroups. -/
theorem S_eq_sup : D.S g = D.W g ⊔ conjugate (D.W g) g :=
  d.S_eq_WProduct_of_starred

/-- G.2.4(3), including the source's literal ordered product WWᵍ. -/
theorem S_eq_product :
    (D.S g : Set G) = (D.W g : Set G) * (conjugate (D.W g) g : Set G) :=
  d.S_eq_product_of_borel d.star_I_eq_L d.star_U_sylow d.star_U_commutator

/-- The two-core of I is the intersection with the kernel of the source star map. -/
theorem S_eq_star_kernel : D.S g = D.I g ⊓ D.LT.pCoreIn 2 :=
  d.S_eq_star_kernel_of_star d.star_I_eq_L.ge

/-- The actual restricted star map is onto L* and has precisely O₂(I) as kernel.
The ambient value records its compatibility with LT→LT/O₂(LT). -/
theorem star_restriction :
    Function.Surjective (d.IStarProjection d.star_I_eq_L) ∧
    (d.IStarProjection d.star_I_eq_L).ker = pCore 2 (D.I g) ∧
    ∀ i : D.I g, (d.IStarProjection d.star_I_eq_L i : D.Star) =
      QuotientGroup.mk' (pCore 2 D.LT) (inclusion d.I_le_LT i) :=
  ⟨d.IStarProjection_surjective d.star_I_eq_L,
    d.IStarProjection_ker d.star_I_eq_L, fun _ => rfl⟩

/-- The index in the counting argument is computed by that same star restriction. -/
theorem W_index_four : (D.W g).relIndex D.U = 4 := d.W_index_four_of_starred

/-- All starred premises of the moved-hyperplane calculation are discharged. -/
theorem orthogonal_geometry :
    D.VL ⊓ D.U = D.V ∧ Nat.card D.V = 8 ∧
      D.V ⊔ conjugate D.V g = D.VL ∧ ⁅D.VL, D.U⁆ = D.V :=
  d.orthogonal_geometry_of_borel d.star_I_eq_L d.star_U_eq_local_core d.star_U_sylow

theorem VL_inf_U : D.VL ⊓ D.U = D.V := d.orthogonal_geometry.1

theorem card_V : Nat.card D.V = 8 := d.orthogonal_geometry.2.1

theorem V_sup_conjugate : D.V ⊔ conjugate D.V g = D.VL :=
  d.orthogonal_geometry.2.2.1

theorem commutator_VL_U : ⁅D.VL, D.U⁆ = D.V := d.orthogonal_geometry.2.2.2

/-- The source span is also a literal product in the elementary abelian module. -/
theorem VL_product : (D.VL : Set G) = (D.V : Set G) * (conjugate D.V g : Set G) := by
  have hV : D.V ≤ D.VL := d.VL_inf_U ▸ (show D.VL ⊓ D.U ≤ D.VL from inf_le_left)
  have hconj : conjugate D.V g ≤ D.VL :=
    d.V_sup_conjugate ▸ (show conjugate D.V g ≤ D.V ⊔ conjugate D.V g from le_sup_right)
  let := d.VL_elementary
  have hn : conjugate D.V g ≤ normalizer (D.V : Set G) := by
    apply le_trans _ (centralizer_le_normalizer (D.V : Set G))
    intro x hx v hv
    exact congrArg Subtype.val (mul_comm (⟨v, hV hv⟩ : D.VL) ⟨x, hconj hx⟩)
  rw [← d.V_sup_conjugate]
  exact coe_mul_of_right_le_normalizer_left _ _ hn

/-- Actual application to the terminal branch's earlier-clause interface.
No field of this record is assumed in the source hypothesis. -/
theorem earlierStructure : Block.EarlierStructure D g where
  star_core := d.star_U_eq_local_core
  star_sylow := d.star_U_sylow
  generated := d.I_eq_LU
  core_generated := d.S_eq_sup
  star_kernel := d.S_eq_star_kernel
  orthogonal_intersection := d.VL_inf_U
  seed_span := d.V_sup_conjugate
  seed_card := d.card_V
  orthogonal_card := d.card_VL
  closure_index := d.W_index_four

/-- The counting denominator now uses the proved source intersection and
generation, without assuming that S₂ is contained in W. -/
theorem card_upper_kernel_source :
    Nat.card (D.W g ⊓ S₂ D g : Subgroup G) =
      8 * D.VL.relIndex (S₂ D g) := by
  rw [d.card_upper_kernel d.L_le_I d.VL_inf_U, d.card_V]

/-- Actual application of G.2.4(2) to the complete layer conclusion (4–5). -/
theorem source_layers :
    D.VL ≤ D.S g ⊓ centralizer (D.S g : Set G) ∧
    D.VL ≤ S₂ D g ∧ S₂ D g ≤ D.S g ∧
    (D.VL.subgroupOf (D.I g)).Normal ∧
    ((S₂ D g).subgroupOf (D.I g)).Normal ∧
    ⁅S₂ D g, D.I g⁆ ≤ D.VL ∧ IsElementaryAbelian 2 (S₂ D g) :=
  d.orthogonal_layers d.L_le_I

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.AlternatingFive
