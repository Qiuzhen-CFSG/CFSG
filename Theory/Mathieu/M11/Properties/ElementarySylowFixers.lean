module

public import Theory.GroupAction.ElementarySylowFixerBound
public import Theory.Mathieu.M11.Properties.AutomorphismCentralizers
public import Theory.Mathieu.M11.Properties.SylowTwo

/-!
# Elementary abelian pointwise Sylow fixers of M₁₁

The actual Witt-design model has only inner automorphisms. Its semidihedral
Sylow subgroups have cyclic center, so the elementary abelian pointwise fixer
has order at most two. The argument uses the checked generator-rigidity and
Sylow constructions, and does not require any covering-group assertion.

Source: Aschbacher–Smith, E.6.8(5), printed p.248, and 1.1.5(3)(f), p.502.
-/

open Subgroup
namespace Sporadic.Mathieu
/-- Every Sylow two-subgroup of M₁₁ has cyclic center. -/
public theorem m11_sylow_center_isCyclic (S : Sylow 2 M11) : IsCyclic (center S) := by
  obtain ⟨P, a, b, ha, hb, hc, hg⟩ := m11_exists_semidihedral_sylow
  have hz : center P = zpowers (a ^ 4) := by
    exact Semidihedral.center_eq (n := 4) (by decide) a b ha hb hc hg
  have hcyc : IsCyclic (center P) := hz ▸ inferInstance
  exact (centerCongr (S.equiv P)).isCyclic.mpr hcyc

/-- An elementary abelian group of pointwise Sylow fixers of M₁₁ has order at most two. -/
public theorem m11_elementary_sylow_fixer_card_le_two (S : Sylow 2 M11)
    (A : Subgroup (MulAut M11)) [IsElementaryAbelian 2 A]
    (hfix : ∀ a ∈ A, ∀ x ∈ S, a x = x) : Nat.card A ≤ 2 := by
  let _ := m11_sylow_center_isCyclic S
  exact Theory.GroupAction.elementary_sylow_fixer_card_le_two_of_inner S m11_center_eq_bot
    (fun a _ _ => automorphism_inner_of_equiv_m11 (MulEquiv.refl _) a) A hfix
end Sporadic.Mathieu
