module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Sylow

/-!
# Centralizer supplements from a central elementary commutator layer

Suppose W is normal, V is elementary abelian at 2, the ambient group
centralizes V, and [W,G] lies in V. Then every Sylow 2-subgroup supplements
C_G(W). These hypotheses do not require V to be contained in W.

For g in G and w in W, the commutator [g,w] belongs to V. It is fixed by g
and has square one, so the commutator identity gives [g²,w]=1. Consequently
G/C_G(W) has exponent two. The image of a Sylow subgroup is Sylow in this
quotient 2-group and therefore is the whole quotient.

This is the elementary centralizer-factorization step in Stellmacher (2.3),
Journal of Algebra 190 (1997), p. 20: an action fixing both V and ZV/V has
a 2-group image. Applied inside C_E(V), its Sylow subgroup O₂(E) supplements
C_E(ZV). The scanned source includes the quotient ZV/V at this point.
-/

open scoped commutatorElement

namespace Subgroup

/-- A central elementary commutator layer forces every Sylow 2-subgroup to supplement
 the centralizer of the normal subgroup. -/
public theorem centralizer_sup_sylow_eq_top_of_commutator_le
    {G : Type*} [Group G] [Finite G] (W V : Subgroup G)
    [W.Normal] [IsElementaryAbelian 2 V] (S : Sylow 2 G)
    (hV : (⊤ : Subgroup G) ≤ centralizer (V : Set G))
    (hcomm : ⁅W, (⊤ : Subgroup G)⁆ ≤ V) :
    centralizer (W : Set G) ⊔ (S : Subgroup G) = ⊤ := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C := centralizer (W : Set G)
  let q := QuotientGroup.mk' C
  have hsq (g : G) : g ^ 2 ∈ C := by
    rw [mem_centralizer_iff]
    intro w hw
    have hcw : ⁅g, w⁆ ∈ V := by
      rw [commutator_comm] at hcomm
      exact hcomm (commutator_mem_commutator (mem_top g) hw)
    have hfix : g * ⁅g, w⁆ * g⁻¹ = ⁅g, w⁆ := by
      have hh := (mem_centralizer_iff.mp (hV (mem_top g))) _ hcw
      rw [← hh]
      simp only [mul_assoc, mul_inv_cancel, mul_one]
    have hpow : ⁅g, w⁆ ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ hcw
    have hh : ⁅g ^ 2, w⁆ = 1 := by
      rw [pow_two, commutatorElement_mul_left_eq_conj_mul, hfix, ← pow_two, hpow]
    exact (commutatorElement_eq_one_iff_mul_comm.mp hh).symm
  have hquot : IsPGroup 2 (G ⧸ C) := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective C x
    refine ⟨1, ?_⟩
    rw [pow_one, ← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (hsq g)
  let T := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective C)
  have hT : (T : Subgroup (G ⧸ C)) = ⊤ :=
    (T.is_maximal' (hquot.of_injective (⊤ : Subgroup (G ⧸ C)).subtype
      (⊤ : Subgroup (G ⧸ C)).subtype_injective) le_top).symm
  have hmap : (S : Subgroup G).map q = ⊤ := hT
  have hh := congrArg (Subgroup.comap q) hmap
  rw [Subgroup.comap_map_eq, Subgroup.comap_top, QuotientGroup.ker_mk'] at hh
  exact (sup_comm C (S : Subgroup G)).trans hh

end Subgroup
