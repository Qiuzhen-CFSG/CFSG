module
public import Theory.ElementaryAbelian.Extraspecial
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Extraspecial structure is preserved by group equivalences

A multiplicative equivalence transports the extraspecial p-group predicate.
It carries the center to the center, giving the same center order and an
equivalence of the central quotients. Elementary abelianness and nontriviality
of that quotient therefore pass to the target group. No finiteness or prime
hypothesis beyond the original predicate is needed.

This generic transport supports literal action-image constructions: the
extraspecial subgroup of an action range can be included into the same
module's automorphism group without changing the module or action. The
argument generalizes the p=3 transport used by Stellmacher (1.3).
-/

open scoped IsMulCommutative

public theorem IsExtraspecial.of_mulEquiv
    {p : ℕ} {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : IsExtraspecial p A) : IsExtraspecial p B := by
  let _ : IsExtraspecial p A := h
  have hc : (Subgroup.center A).map e.toMonoidHom = Subgroup.center B := by
    ext b
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (Subgroup.centerCongr e ⟨a, ha⟩).property
    · intro hb
      exact ⟨e.symm b, (Subgroup.centerCongr e.symm ⟨b, hb⟩).property,
        e.apply_symm_apply b⟩
  let q := QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e hc
  let _ : IsElementaryAbelian p (A ⧸ Subgroup.center A) := h.quotient_elementary_abelian
  let _ : Nontrivial (A ⧸ Subgroup.center A) := h.quotient_nontrivial
  refine ⟨?_, ?_, q.symm.toEquiv.nontrivial⟩
  · exact (Nat.card_congr (Subgroup.centerCongr e).toEquiv).symm.trans h.center_order_p
  · refine
      { toIsMulCommutative := ⟨⟨fun a b => q.symm.injective (by
          simp only [map_mul]
          exact mul_comm _ _)⟩⟩
        exponent_dvd_p := ?_ }
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro b
    apply q.symm.injective
    rw [map_pow, map_one]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p (A ⧸ Subgroup.center A)) (q.symm b)


