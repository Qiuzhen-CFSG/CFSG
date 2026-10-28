module

public import Mathlib.GroupTheory.Complement

/-!
# Recovering two projections from a complement in a common quotient

Suppose two surjections from a group have kernels disjoint from the kernel
of a third quotient map. If their images in that quotient coincide and have
a complement, the inverse image of the complement projects isomorphically
to both targets. In particular the targets are isomorphic.

The application to conjugation fiber products retains the normal diagonal
core until after the complement has been lifted.
-/

public section
noncomputable section
namespace QuotientKernelComplement
open Subgroup

variable {F Q A B : Type*} [Group F] [Group Q] [Group A] [Group B]

/-- Pulling back a complement preserves it when the original subgroup meets
the quotient kernel trivially. -/
theorem complement_comap (q : F →* Q) (K : Subgroup F) (U : Subgroup Q)
    (hd : Disjoint K q.ker) (hc : (K.map q).IsComplement' U) :
    K.IsComplement' (U.comap q) := by
  apply isComplement'_of_disjoint_and_mul_eq_univ
  · rw [Subgroup.disjoint_def]
    intro k hk hu
    have hq : q k = 1 := hc.disjoint.le_bot ⟨⟨k,hk,rfl⟩,hu⟩
    exact hd.le_bot ⟨hk,hq⟩
  · apply Set.eq_univ_iff_forall.mpr
    intro x
    obtain ⟨⟨k,u⟩,hku⟩ := hc.2 (q x)
    obtain ⟨a,ha,hea⟩ := k.property
    have hu : a⁻¹*x ∈ U.comap q := by
      change q (a⁻¹*x) ∈ U
      rw [map_mul,map_inv,hea,← hku,inv_mul_cancel_left]
      exact u.property
    exact ⟨a,ha,a⁻¹*x,hu,mul_inv_cancel_left a x⟩

/-- A common complement of the two kernels identifies the actual targets. -/
def equivOfComplement (f : F →* A) (g : F →* B)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (L : Subgroup F) (hL : f.ker.IsComplement' L) (hL' : g.ker.IsComplement' L) : A ≃* B :=
  (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
    (hL.symm.QuotientMulEquiv.trans
      (hL'.symm.QuotientMulEquiv.symm.trans
        (QuotientGroup.quotientKerEquivOfSurjective g hg)))

/-- Lift the quotient complement and recover the groups without discarding
either central kernel. -/
theorem nonempty_equiv (f : F →* A) (g : F →* B) (q : F →* Q)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hdf : Disjoint f.ker q.ker) (hdg : Disjoint g.ker q.ker)
    (he : f.ker.map q = g.ker.map q)
    (hc : ∃ U : Subgroup Q, (f.ker.map q).IsComplement' U) : Nonempty (A ≃* B) := by
  obtain ⟨U,hU⟩ := hc
  exact ⟨equivOfComplement f g hf hg (U.comap q)
    (complement_comap q f.ker U hdf hU)
    (complement_comap q g.ker U hdg (he ▸ hU))⟩

end QuotientKernelComplement
