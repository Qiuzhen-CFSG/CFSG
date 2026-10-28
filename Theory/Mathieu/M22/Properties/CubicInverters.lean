module

public import Theory.Mathieu.M22.Properties.CubicInverters.Enumeration
public import Theory.Mathieu.M22.Properties.AutomorphismCoverage

/-!
# Cubic elements inverted by every involutory automorphism of M₂₂

Every design involution belongs to a Sylow two-subgroup. Sylow conjugacy moves
it to the subgroup exhausted in `CubicInverters.Enumeration`, where an explicit
word of order three is inverted. Conjugating that word back gives the required
witness. The faithful, surjective map from design automorphisms to `MulAut M22`
then covers every abstract involution, both inner and outer.

This proves the native M₂₂ input for the involution inversion step in
Aschbacher–Smith H.12.1, printed p.394 (PDF p.405), combined manuscript of
1 March 2004. Lifting to the genuine triple cover and its ambient extensions
belongs to the source consumer; no split extension is used here.
-/

public section
namespace Sporadic.Mathieu
open Subgroup
open scoped Pointwise

/-- Every involution of the full design group inverts a cubic element of M₂₂. -/
theorem m22DesignAut_exists_inverted_three (s : m22DesignAut) (hs : orderOf s = 2) :
    ∃ y : M22, orderOf y = 3 ∧ m22DesignAutToAut s y = y⁻¹ := by
  have hz : IsPGroup 2 (zpowers s) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hs, pow_one])
  obtain ⟨Q, hQ⟩ := hz.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq m22DesignAut Q M22CubicInverters.standardSylow
  let e : MulAut m22DesignAut := MulAut.conj g
  have hmem : e s ∈ M22CubicInverters.standardSylow := by
    rw [← hg]
    change e s ∈ (Q : Subgroup m22DesignAut).map e.toMonoidHom
    exact mem_map_of_mem e.toMonoidHom (hQ (mem_zpowers s))
  obtain ⟨y, hy, hinv⟩ := M22CubicInverters.exists_inverted_three_of_mem_standard
    (e s) ((e.orderOf_eq s).trans hs) hmem
  refine ⟨(m22DesignAutToAut g).symm y, (MulEquiv.orderOf_eq _ y).trans hy, ?_⟩
  apply (m22DesignAutToAut g).injective
  rw [map_inv, MulEquiv.apply_symm_apply]
  simpa only [e, MulAut.conj_apply, map_mul, map_inv, MulAut.mul_apply,
    MulAut.inv_apply] using hinv

/-- Every involutory automorphism of the actual M₂₂ inverts an element of order three. -/
theorem m22_exists_inverted_three (a : MulAut M22) (ha : orderOf a = 2) :
    ∃ y : M22, orderOf y = 3 ∧ a y = y⁻¹ := by
  obtain ⟨s, rfl⟩ := m22DesignAutToAut_surjective a
  apply m22DesignAut_exists_inverted_three
  rwa [orderOf_injective m22DesignAutToAut m22DesignAutToAut_injective] at ha

end Sporadic.Mathieu
