module
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Placement.TransitiveCoverage.TransversalChecks

/-!
# Exhaustive native M₂₄ Sylow double-coset coverage

The checked binary-partition keys give 239,085 distinct cosets of the marked
Sylow subgroup. This is its full index, by the certified orders of M₂₄ and
the subgroup. Finiteness makes the transversal surjective. Each transversal
entry is a native Sylow element times one of the 510 native representatives,
so a remaining right Sylow factor gives the required double-coset coverage.

Every element of the Witt-design group is covered, including elements in
sextet stabilizers. No maximal-subgroup classification or external enumeration
is assumed. Source context: Aschbacher–Smith, printed p.511 (PDF p.528);
Aschbacher, *Sporadic Groups*, Chapter 7, §20; GLS3 Table 5.3e.
-/

public section
namespace Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement.TransitiveCoverage
open SylowNormalizer

theorem transversalKey_strictMono :
    StrictMono (fun j : Fin 239085 => fastKey (transversalParameter j.val)) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  have h := keyBlock_checks ⟨i.val / 5313, by omega⟩
    ⟨i.val % 5313, Nat.mod_lt _ (by decide)⟩
  have he : i.val / 5313 * 5313 + i.val % 5313 = i.val := by omega
  dsimp only at h
  rw [he] at h
  exact h i.succ.isLt

theorem transversal_cosets_injective : Function.Injective
    (fun j : Fin 239085 => (QuotientGroup.mk (transversal j) : M24 ⧸ candidate)) := by
  intro i j h
  apply transversalKey_strictMono.injective
  change fastKey (transversalParameter i.val) = fastKey (transversalParameter j.val)
  rw [fastKey_eq, fastKey_eq]
  exact key_eq_of_coset_eq h

theorem card_sylowCosets : Nat.card (M24 ⧸ candidate) = 239085 := by
  have h := candidate.card_mul_index
  rw [candidate_card, m24_order, Subgroup.index_eq_card] at h
  omega

theorem transversal_cosets_surjective : Function.Surjective
    (fun j : Fin 239085 => (QuotientGroup.mk (transversal j) : M24 ⧸ candidate)) := by
  apply ((Nat.bijective_iff_injective_and_card _).mpr
    ⟨transversal_cosets_injective, ?_⟩).surjective
  rw [Nat.card_fin, card_sylowCosets]

/-- Every native M₂₄ element belongs to a certified Sylow double coset. -/
theorem covers : Covers := by
  intro g
  obtain ⟨j, hj⟩ := transversal_cosets_surjective (QuotientGroup.mk g)
  have ht : (transversal j)⁻¹ * g ∈ candidate := QuotientGroup.eq.mp hj
  refine ⟨(parameter (transversalParameter j.val)).1,
    OrderEnumeration.element (parameter (transversalParameter j.val)).2,
    ⟨(transversal j)⁻¹ * g, ht⟩, ?_⟩
  exact congrArg Subtype.val (mul_inv_cancel_left (transversal j) g)

end Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement.TransitiveCoverage
