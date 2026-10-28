module

public import Mathlib.GroupTheory.Index
public import Theory.Mathieu.M22.Properties.Identification
public import Theory.Mathieu.M22.Properties.Order

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

open Theory.GroupTheory

namespace Sporadic.Mathieu

open scoped Pointwise

private def m22OddPropertyBlockIndexArray : Array (Fin 77) := #[
  0, 1, 2, 4, 3, 5, 8, 7, 6, 11, 10, 9, 16, 18, 15, 14, 12,
  17, 13, 20, 19, 21, 24, 23, 22, 27, 26, 25, 33, 35, 30, 32,
  31, 28, 36, 29, 34, 37, 39, 38, 43, 47, 42, 40, 45, 44, 48,
  41, 46, 52, 57, 51, 49, 54, 53, 56, 55, 50, 65, 68, 71, 61,
  62, 73, 64, 58, 67, 66, 59, 70, 69, 60, 72, 63, 74, 75, 76]

private theorem m22OddPropertyBlockIndexArray_size :
    m22OddPropertyBlockIndexArray.size = 77 := by
  decide +kernel

private def m22OddPropertyBlockIndex (i : Fin 77) : Fin 77 :=
  m22OddPropertyBlockIndexArray[i.val]'(by
    rw [m22OddPropertyBlockIndexArray_size]
    exact i.isLt)

private theorem m22OddPropertyBlockIndex_image :
    Finset.univ.image m22OddPropertyBlockIndex = Finset.univ := by
  decide +kernel

private theorem m22OddProperty_blockAt (i : Fin 77) :
    m22OddPairSwap • m22BlockAt i =
      m22BlockAt (m22OddPropertyBlockIndex i) := by
  revert i
  decide +kernel

public theorem m22OddPairSwap_mem_designAut :
    m22OddPairSwap ∈ m22DesignAut := by
  rw [m22DesignAut, SteinerSystem.mem_aut_iff]
  have hFinset : m22OddPairSwap • m22Blocks = m22Blocks :=
    m22_blocks_smul_of_index
      m22OddPairSwap m22OddPropertyBlockIndex
      m22OddPropertyBlockIndex_image m22OddProperty_blockAt
  have hSet := congrArg
    (fun s : Finset (Finset (Fin 22)) => (s : Set (Finset (Fin 22)))) hFinset
  simpa only [m22WittDesign, SteinerSystem.ofPairwiseIntersection_blocks,
    Finset.coe_smul_finset] using hSet

/-- M22 is exactly the even part of the full hexad-design automorphism group. -/
public theorem M22_eq_m22DesignAut_inf_alternating :
    M22 = m22DesignAut ⊓ alternatingGroup (Fin 22) :=
  rfl

/-- M22 preserves the Steiner system S(3,6,22). -/
public theorem M22_le_hexadDesignAut :
    M22 ≤ m22WittDesign.aut := by
  simpa [m22DesignAut] using M22_le_m22DesignAut

/-- The standard odd design automorphism is an involution. -/
public theorem m22OddPairSwap_order :
    orderOf m22OddPairSwap = 2 := by
  apply orderOf_eq_prime
  · decide +kernel
  · decide +kernel

/-- The full hexad design admits an odd automorphism. -/
public theorem m22_exists_odd_design_automorphism :
    ∃ g : Equiv.Perm (Fin 22),
      g ∈ m22DesignAut ∧ g ∉ alternatingGroup (Fin 22) :=
  ⟨m22OddPairSwap, m22OddPairSwap_mem_designAut,
    m22OddPairSwap_not_alternating⟩

/-- The standard odd design automorphism does not belong to M22. -/
public theorem m22OddPairSwap_not_mem_M22 :
    m22OddPairSwap ∉ M22 := by
  intro h
  exact m22OddPairSwap_not_alternating h.2

/-- M22 is a proper subgroup of the full hexad-design automorphism group. -/
public theorem M22_lt_m22DesignAut :
    M22 < m22DesignAut := by
  refine lt_of_le_of_ne M22_le_m22DesignAut ?_
  intro h
  exact m22OddPairSwap_not_mem_M22 (h ▸ m22OddPairSwap_mem_designAut)

/-- The even subgroup inside the full hexad-design automorphism group. -/
@[expose] public noncomputable def m22EvenDesignAut : Subgroup m22DesignAut :=
  (alternatingGroup (Fin 22)).comap m22DesignAut.subtype

/-- The Steiner definition of M22 is canonically the even design-automorphism subgroup. -/
@[expose] public noncomputable def m22EquivM22EvenDesignAut :
    M22 ≃* m22EvenDesignAut where
  toFun g := ⟨⟨(g : Equiv.Perm (Fin 22)), g.property.1⟩, g.property.2⟩
  invFun g :=
    ⟨((g : m22DesignAut) : Equiv.Perm (Fin 22)),
      ⟨(g : m22DesignAut).property, g.property⟩⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_mul' _ _ := rfl

private noncomputable def m22OddDesignAut : m22DesignAut :=
  ⟨m22OddPairSwap, m22OddPairSwap_mem_designAut⟩

private theorem m22OddDesignAut_not_mem_even :
    m22OddDesignAut ∉ m22EvenDesignAut := by
  exact m22OddPairSwap_not_alternating

private theorem m22OddDesignAut_sq :
    m22OddDesignAut * m22OddDesignAut = 1 := by
  apply Subtype.ext
  decide +kernel

private theorem m22EvenDesignAut_index_le_two :
    m22EvenDesignAut.index ≤ 2 := by
  have hRel :
      (alternatingGroup (Fin 22)).relIndex m22DesignAut ≤ 2 := by
    have h := Subgroup.relIndex_le_of_le_right
      (H := alternatingGroup (Fin 22)) (K := m22DesignAut) (L := ⊤)
      le_top (by simp)
    simpa [Subgroup.relIndex_top_right] using h
  simpa [m22EvenDesignAut, Subgroup.relIndex] using hRel

/-- The even design-automorphism subgroup has index two. -/
public theorem m22EvenDesignAut_index :
    m22EvenDesignAut.index = 2 := by
  have hneTop : m22EvenDesignAut ≠ ⊤ := by
    intro htop
    apply m22OddDesignAut_not_mem_even
    rw [htop]
    exact Subgroup.mem_top _
  have hneOne : m22EvenDesignAut.index ≠ 1 := by
    intro h
    exact hneTop (Subgroup.index_eq_one.mp h)
  have hneZero : m22EvenDesignAut.index ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  have hle : m22EvenDesignAut.index ≤ 2 :=
    m22EvenDesignAut_index_le_two
  omega

private theorem m22DesignAut_mem_even_or_mul_odd (g : m22DesignAut) :
    g ∈ m22EvenDesignAut ∨ g * m22OddDesignAut ∈ m22EvenDesignAut := by
  rcases (Subgroup.index_eq_two_iff_exists_notMem_and.mp
    m22EvenDesignAut_index) with ⟨a, ha, hcoset⟩
  rcases hcoset g with hga | hg
  · right
    have hoddA : m22OddDesignAut * a ∈ m22EvenDesignAut :=
      (hcoset m22OddDesignAut).resolve_right m22OddDesignAut_not_mem_even
    have hmem :=
      m22EvenDesignAut.mul_mem hga (m22EvenDesignAut.inv_mem hoddA)
    have hOddInv : m22OddDesignAut⁻¹ = m22OddDesignAut :=
      inv_eq_of_mul_eq_one_right m22OddDesignAut_sq
    simpa [hOddInv, mul_assoc] using hmem
  · exact Or.inl hg

/-- Every full design automorphism is an M22 element, optionally followed by
the standard odd involution. -/
public theorem m22DesignAut_normalForm (g : m22DesignAut) :
    ∃ h : M22,
      (g : Equiv.Perm (Fin 22)) = (h : Equiv.Perm (Fin 22)) ∨
      (g : Equiv.Perm (Fin 22)) =
        (h : Equiv.Perm (Fin 22)) * m22OddPairSwap := by
  rcases m22DesignAut_mem_even_or_mul_odd g with hg | hg
  · refine ⟨⟨(g : Equiv.Perm (Fin 22)), g.property, hg⟩, Or.inl rfl⟩
  · let h : M22 :=
      ⟨((g * m22OddDesignAut : m22DesignAut) : Equiv.Perm (Fin 22)),
        (g * m22OddDesignAut : m22DesignAut).property, hg⟩
    refine ⟨h, Or.inr ?_⟩
    change (g : Equiv.Perm (Fin 22)) =
      ((g : Equiv.Perm (Fin 22)) * m22OddPairSwap) * m22OddPairSwap
    rw [mul_assoc]
    have hsq : m22OddPairSwap * m22OddPairSwap = 1 := by
      decide +kernel
    rw [hsq, mul_one]

/-- The full automorphism group of the hexad design has order 887040. -/
public theorem m22DesignAut_order :
    Nat.card m22DesignAut = 887040 := by
  have hCard :
      Nat.card M22 = Nat.card m22EvenDesignAut :=
    Nat.card_congr m22EquivM22EvenDesignAut.toEquiv
  calc
    Nat.card m22DesignAut =
        Nat.card m22EvenDesignAut * m22EvenDesignAut.index :=
      (Subgroup.card_mul_index m22EvenDesignAut).symm
    _ = Nat.card M22 * 2 := by
      rw [← hCard, m22EvenDesignAut_index]
    _ = 887040 := by
      rw [m22_order]

/-- M22 is normal in the full hexad-design automorphism group. -/
public theorem M22_normal_in_m22DesignAut :
    (M22.subgroupOf m22DesignAut).Normal := by
  have hEq :
      M22.subgroupOf m22DesignAut = m22EvenDesignAut := by
    ext g
    simp [M22, m22EvenDesignAut]
  rw [hEq]
  exact Subgroup.normal_of_index_eq_two m22EvenDesignAut_index

end Sporadic.Mathieu
