module

public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Structure.Reduction

/-!+# The orthogonal star kernel and local core comparison

The given five-point coordinates give |V_L|=16. Irreducibility makes the
two-core of LT centralize V_L. The star map therefore retains the specified
orthogonal action. Its two-group kernel also proves that the image of
O₂(L₁) equals O₂(L₁*); these are distinct constructions, compared here by
the actual quotient map. Starred generation discharges L≤I in the existing
orthogonal-layer consumer.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.4, printed pp.334–335, using the kernel argument of G.2.3.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterG.Section02.AlternatingFive
open Setup
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G}

omit [Finite G] in
private theorem core_subgroupOf_map {A K : Subgroup G} (hAK : A ≤ K) :
    ((A.subgroupOf K).pCoreIn 2).map K.subtype = A.pCoreIn 2 := by
  let e := subgroupOfEquivOfLe hAK
  calc
    _ = ((pCore 2 (A.subgroupOf K)).map e.toMonoidHom).map A.subtype := by
      rw [pCoreIn, map_map, map_map]
      rfl
    _ = _ := by rw [pCore_map_iso]; rfl

/-- Cores commute with this star image because its kernel is a two-group. -/
theorem star_pCoreIn (A : Subgroup G) (hA : A ≤ D.LT) :
    D.star (A.pCoreIn 2) = (D.star A).pCoreIn 2 := by
  have hcore : (A.subgroupOf D.LT).pCoreIn 2 = (A.pCoreIn 2).subgroupOf D.LT := by
    apply map_injective D.LT.subtype_injective
    rw [core_subgroupOf_map hA, map_subgroupOf_eq_of_le ((pCoreIn_le 2 A).trans hA)]
  let q := QuotientGroup.mk' (pCore 2 D.LT)
  have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have he := map_pCoreIn_of_ker_isPGroup q hk (A.subgroupOf D.LT)
  rw [hcore] at he
  exact he

/-- The starred image of the original local two-core is the core of L₁*.
This does not itself identify that subgroup with U*. -/
theorem star_local_core : D.star (D.L₁.pCoreIn 2) = (D.star D.L₁).pCoreIn 2 :=
  star_pCoreIn D.L₁ (((map_subtype_le _).trans inf_le_left).trans le_sup_left)

namespace Hypothesis
variable (d : Hypothesis D g)
include d

theorem card_VL : Nat.card D.VL = 16 := by
  calc
    Nat.card D.VL = Nat.card (BinaryPermutation.core (Fin 5)) :=
      Nat.card_congr d.coordinates.toEquiv
    _ = 16 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
        BinaryPermutation.finrank_core]
      rfl

theorem VL_le_LT : D.VL ≤ D.LT :=
  conjugateSpanBy_le (d.setup.point_le.trans (d.setup.V_le_T.trans le_sup_right))
    ((show D.L ≤ D.LT from le_sup_left).trans D.LT.le_normalizer)

theorem LT_normalizes_VL : D.LT ≤ normalizer (D.VL : Set G) :=
  sup_le (L_normalizes_VL D) d.T_normalizes_VL

theorem LT_core_centralizes_VL : D.LT.pCoreIn 2 ≤ centralizer (D.VL : Set G) := by
  let := d.VL_elementary
  exact pCoreIn_le_centralizer_of_irreducible D.VL D.L D.LT
    (IsElementaryAbelian.isPGroup 2 D.VL) d.VL_le_LT d.LT_normalizes_VL
    le_sup_left d.irreducible

/-- The comparison also preserves conjugation on the actual orthogonal module,
for every element of I, rather than only for the original subgroup L. -/
theorem IStarProjection_equivariant (hstar : D.star (D.I g) = D.star D.L) (i : D.I g) (v : D.VL) :
    d.coordinates ⟨(i : G) * v * (i : G)⁻¹,
      (mem_normalizer_iff.mp (d.I_normalizes_VL i.property) v).mp v.property⟩ =
      Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 5)
        (d.model (d.IStarProjection hstar i)).val (d.coordinates v).toAdd) := by
  obtain ⟨l, hl⟩ := starProjection_surjective D (d.IStarProjection hstar i)
  have he : QuotientGroup.mk' (pCore 2 D.LT) (inclusion (d.I_le_LT) i) =
      QuotientGroup.mk' (pCore 2 D.LT) (inclusion (show D.L ≤ D.LT from le_sup_left) l) :=
    (congrArg Subtype.val hl).symm
  let k : D.LT := inclusion (d.I_le_LT) i *
    (inclusion (show D.L ≤ D.LT from le_sup_left) l)⁻¹
  have hk : k ∈ pCore 2 D.LT := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (pCore 2 D.LT) k = 1
    simp only [k, map_mul, map_inv, he, mul_inv_cancel]
  have hkc := d.LT_core_centralizes_VL (show (k : G) ∈ D.LT.pCoreIn 2 from ⟨k, hk, rfl⟩)
  have hvl : (l : G) * v * (l : G)⁻¹ ∈ D.VL :=
    (mem_normalizer_iff.mp (L_normalizes_VL D l.property) v).mp v.property
  have hc := hkc _ hvl
  have hc' : (k : G) * ((l : G) * v * (l : G)⁻¹) * (k : G)⁻¹ =
      (l : G) * v * (l : G)⁻¹ := by
    rw [← hc, mul_inv_cancel_right]
  have hconj : (i : G) * v * (i : G)⁻¹ = (l : G) * v * (l : G)⁻¹ := by
    calc
      _ = (k : G) * ((l : G) * v * (l : G)⁻¹) * (k : G)⁻¹ := by
        change _ = ((i : G) * (l : G)⁻¹) * ((l : G) * v * (l : G)⁻¹) *
          ((i : G) * (l : G)⁻¹)⁻¹
        group
      _ = _ := hc'
  have heq : (⟨(i : G) * v * (i : G)⁻¹,
      (mem_normalizer_iff.mp (d.I_normalizes_VL i.property) v).mp v.property⟩ : D.VL) =
      ⟨(l : G) * v * (l : G)⁻¹, hvl⟩ := Subtype.ext hconj
  rw [heq, ← hl]
  exact d.equivariant l v

/-- Generation supplies the only extra premise in the orthogonal-layer theorem. -/
theorem orthogonal_layers_of_star (hstar : D.star D.L ≤ D.star (D.I g)) :
    D.VL ≤ D.S g ⊓ centralizer (D.S g : Set G) ∧
    D.VL ≤ S₂ D g ∧ S₂ D g ≤ D.S g ∧
    (D.VL.subgroupOf (D.I g)).Normal ∧
    ((S₂ D g).subgroupOf (D.I g)).Normal ∧
    ⁅S₂ D g, D.I g⁆ ≤ D.VL ∧ IsElementaryAbelian 2 (S₂ D g) :=
  d.orthogonal_layers (d.L_le_I_of_star hstar)

/-- The counting consumer uses the cardinality of the actual starred U. -/
theorem W_index_four_of_star (hstar : D.star (D.I g) = D.star D.L)
    (hU : Nat.card (D.star D.U) = 4) : (D.W g).relIndex D.U = 4 :=
  (d.W_index_of_star hstar).trans hU

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.AlternatingFive
