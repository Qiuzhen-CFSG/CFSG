module

public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.Algebra.Group.Subgroup.MulOpposite
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Moved spaces modulo global fixed vectors

Suppose a finite normal subgroup N has order invertible in the coefficient
field and its fixed vectors are already fixed by the whole group. The norm
over N commutes with the ambient action. It annihilates all displacements
and acts as multiplication by |N| on globally fixed vectors. Consequently
every moved space is disjoint from the global fixed space, and projection
to its quotient preserves its dimension.

This is the standard coprime averaging argument, with the original quotient
map retained. It does not assume complete reducibility of the whole group.
-/

@[expose] public section

open Subgroup Representation
namespace Representation
variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (N : Subgroup G) [N.Normal] [Fintype N]

/-- The norm over a normal subgroup commutes with the ambient group. -/
lemma normal_norm_commutes (g : G) (v : V) :
    norm (ρ.comp N.subtype) (ρ g v) = ρ g (norm (ρ.comp N.subtype) v) := by
  classical
  simp only [norm, LinearMap.sum_apply, map_sum]
  let e : N ≃* N := MulAut.conjNormal g
  apply (Fintype.sum_equiv e.toEquiv _ _ ?_).symm
  intro n
  change ρ g (ρ (n : G) v) = ρ (g * (n : G) * g⁻¹) (ρ g v)
  simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel, mul_one]

/-- No moved space meets the fixed space under the coprime fixed-space hypothesis. -/
lemma disjoint_moved_invariants_of_normal_coprime
    (hc : (Fintype.card N : k) ≠ 0)
    (hf : invariants (ρ.comp N.subtype) ≤ ρ.invariants) (A : Subgroup G) :
    Disjoint (Coinvariants.ker (ρ.comp A.subtype)) ρ.invariants := by
  let P := norm (ρ.comp N.subtype)
  have hP (v : V) : P v ∈ ρ.invariants :=
    hf (fun n => self_norm_apply (ρ.comp N.subtype) n v)
  have hzero : Coinvariants.ker (ρ.comp A.subtype) ≤ LinearMap.ker P := by
    rw [Coinvariants.ker, Submodule.span_le]
    rintro _ ⟨⟨a, v⟩, rfl⟩
    change P (ρ a v - v) = 0
    rw [map_sub, normal_norm_commutes, hP v a, sub_self]
  rw [Submodule.disjoint_def]
  intro v hv hi
  have hz := hzero hv
  change P v = 0 at hz
  change ∀ g, ρ g v = v at hi
  have hpv : P v = (Fintype.card N : k) • v := by
    simp only [P, norm, LinearMap.sum_apply, MonoidHom.comp_apply, hi,
      Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  rw [hpv] at hz
  exact (smul_eq_zero.mp hz).resolve_left hc

/-- Projection modulo global invariants preserves every subgroup moved-space rank. -/
lemma finrank_moved_eq_quotient_image_of_normal_coprime
    (hc : (Fintype.card N : k) ≠ 0)
    (hf : invariants (ρ.comp N.subtype) ≤ ρ.invariants) (A : Subgroup G) :
    Module.finrank k (Coinvariants.ker (ρ.comp A.subtype)) =
      Module.finrank k ((Coinvariants.ker (ρ.comp A.subtype)).map ρ.invariants.mkQ) := by
  let U := Coinvariants.ker (ρ.comp A.subtype)
  let f := ρ.invariants.mkQ.comp U.subtype
  have hd := disjoint_moved_invariants_of_normal_coprime ρ N hc hf A
  have hi : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro v hv
    apply Subtype.ext
    exact Submodule.disjoint_def.mp hd v v.property
      ((Submodule.Quotient.mk_eq_zero _).mp hv)
  have hr : f.range = U.map ρ.invariants.mkQ := by
    change (ρ.invariants.mkQ.comp U.subtype).range = _
    rw [LinearMap.range_comp, Submodule.range_subtype]
  rw [← hr]
  exact (LinearEquiv.ofInjective f hi).finrank_eq

end Representation
