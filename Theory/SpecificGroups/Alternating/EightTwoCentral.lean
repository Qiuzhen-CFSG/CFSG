module
public import Theory.SpecificGroups.SymmetricEight.CentralPair
public import Theory.GroupAction.InnerInvolutionGeometry

/-!
# Two-central involutions in the natural action of A₈

An involution centralizing a Sylow 2-subgroup belongs to that Sylow subgroup:
it is a 2-element in its normalizer. The proved central conjugacy calculation
`SymmetricEight.CentralPair.central_in_sylow_conjugate` then identifies it with
the product of four disjoint pair swaps. Conjugation preserves the absence of
fixed points, giving the literal eight-point action used by the marked A₈ row.

The underlying central conjugacy calculation is the Sylow geometry of
Aschbacher--Smith, *The Classification of Quasithin Groups*, 13.5.21,
printed p.924; this extension only transports its fixed-point conclusion.
-/

@[expose] public section
namespace AlternatingEight
open Subgroup Equiv.Perm
open Theory.SpecificGroups.SymmetricEight.CentralPair

/-- An involution centralizing a Sylow 2-subgroup of A₈ has no fixed points. -/
theorem twoCentral_fixedPointFree
    (P : Sylow 2 (alternatingGroup (Fin 8))) (z : alternatingGroup (Fin 8))
    (hz : orderOf z = 2)
    (hc : ∀ p : P, (z : Equiv.Perm (Fin 8)) * (p.val : Equiv.Perm (Fin 8)) =
      (p.val : Equiv.Perm (Fin 8)) * (z : Equiv.Perm (Fin 8))) :
    ∀ i : Fin 8, (z : Equiv.Perm (Fin 8)) i ≠ i := by
  have hcomm (p : alternatingGroup (Fin 8)) (hp : p ∈ P) : z * p = p * z :=
    Subtype.ext (hc ⟨p,hp⟩)
  have hzP : z ∈ P := (MulAut.involution_mem_sylow_of_centralizes P z
    (hz ▸ pow_orderOf_eq_one z) (by
      intro p hp
      rw [MulAut.conj_apply, hcomm p hp, mul_inv_cancel_right])).1
  have hzn : z ≠ 1 := by intro he; simp [he] at hz
  have hPC : (P : Subgroup (alternatingGroup (Fin 8))) ≤ centralizer {z} := by
    intro p hp
    exact mem_centralizer_singleton_iff.mpr (hcomm p hp).symm
  obtain ⟨g,hg⟩ := central_in_sylow_conjugate P z hzP hzn hPC
  have hm : ∀ i : Fin 8, mate i ≠ i := by decide +kernel
  intro i hi
  have he : (z : Equiv.Perm (Fin 8)) =
      (g : Equiv.Perm (Fin 8)) * mate * (g : Equiv.Perm (Fin 8))⁻¹ :=
    (congrArg Subtype.val hg).symm
  rw [he] at hi
  apply hm ((g : Equiv.Perm (Fin 8))⁻¹ i)
  have hh := congrArg (fun j => (g : Equiv.Perm (Fin 8))⁻¹ j) hi
  simpa only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply] using hh

/-- The same conclusion with the source's subgroup-centralizer membership. -/
theorem twoCentral_fixedPointFree_of_mem_centralizer
    (P : Sylow 2 (alternatingGroup (Fin 8))) (z : alternatingGroup (Fin 8))
    (hz : orderOf z = 2)
    (hc : z ∈ centralizer (P : Set (alternatingGroup (Fin 8)))) :
    ∀ i : Fin 8, (z : Equiv.Perm (Fin 8)) i ≠ i := by
  apply twoCentral_fixedPointFree P z hz
  intro p
  exact congrArg Subtype.val ((mem_centralizer_iff.mp hc p.val p.property).symm)

end AlternatingEight
