module

public import Mathlib.Algebra.Group.ConjFinite
public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Counting conjugacy classes under a surjective homomorphism

The cardinality of an image class divides the cardinality of its source class:
conjugation by a lifted conjugator identifies all fibers. The sum of the sizes
of all source classes over a target class is the kernel order times the target
class size, by counting the full preimage in two ways.

These elementary class-counting identities supply the class-sum comparison in
ordinary block inflation (Feit, *The Representation Theory of Finite Groups*,
III.2.13). No coprimality assertion about individual class fibers is needed.
-/

public section

open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite Classical.propDecidable

namespace ConjClasses
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

omit [Finite G] in
private theorem mk_conj (g x : G) :
    ConjClasses.mk (MulAut.conj g x) = ConjClasses.mk x :=
  mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨g, rfl⟩).symm

private def mapCarrier (f : G →* H) (c : ConjClasses G) :
    c.carrier → (map f c).carrier := fun x =>
  ⟨f x, mem_carrier_iff_mk_eq.mpr (congrArg (map f)
    (mem_carrier_iff_mk_eq.mp x.property))⟩

omit [Finite G] [Finite H] in
private theorem fiber_card_eq (f : G →* H) (hf : Function.Surjective f)
    (c : ConjClasses G) (y z : (map f c).carrier) :
    Nat.card {x : c.carrier // mapCarrier f c x = y} =
      Nat.card {x : c.carrier // mapCarrier f c x = z} := by
  have hyz : IsConj y.val z.val := mk_eq_mk_iff_isConj.mp
    ((mem_carrier_iff_mk_eq.mp y.property).trans
      (mem_carrier_iff_mk_eq.mp z.property).symm)
  obtain ⟨h, hh⟩ := isConj_iff.mp hyz
  obtain ⟨g, rfl⟩ := hf h
  let e : c.carrier ≃ c.carrier := Equiv.subtypeEquiv (MulAut.conj g).toEquiv
    (fun x => by
      simp only [mem_carrier_iff_mk_eq]
      change ConjClasses.mk x = c ↔ ConjClasses.mk (MulAut.conj g x) = c
      rw [mk_conj])
  apply Nat.card_congr (Equiv.subtypeEquiv e _)
  intro x
  change mapCarrier f c x = y ↔ mapCarrier f c (e x) = z
  rw [Subtype.ext_iff, Subtype.ext_iff]
  change f x.val = y.val ↔ f (g * x.val * g⁻¹) = z.val
  rw [map_mul, map_mul, map_inv, ← hh]
  change f x.val = y.val ↔ MulAut.conj (f g) (f x.val) = MulAut.conj (f g) y.val
  exact (MulAut.conj (f g)).injective.eq_iff.symm

/-- The size of an image conjugacy class divides the size of its source class. -/
theorem card_map_carrier_dvd (f : G →* H) (hf : Function.Surjective f)
    (c : ConjClasses G) : Nat.card (map f c).carrier ∣ Nat.card c.carrier := by
  obtain ⟨y, hy⟩ := exists_rep (map f c)
  let y' : (map f c).carrier := ⟨y, mem_carrier_iff_mk_eq.mpr hy⟩
  refine ⟨Nat.card {x : c.carrier // mapCarrier f c x = y'}, ?_⟩
  have h := Nat.card_congr (Equiv.sigmaFiberEquiv (mapCarrier f c))
  rw [Nat.card_sigma] at h
  simp only [fiber_card_eq f hf c _ y', Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Nat.card_eq_fintype_card] at h
  exact h.symm

private theorem sum_card_mul (v : ConjClasses G → ℕ) :
    ∑ c : ConjClasses G, Nat.card c.carrier * v c =
      ∑ x : G, v (ConjClasses.mk x) := by
  classical
  have hfiber (c : ConjClasses G) :
      Fintype.card {x : G // ConjClasses.mk x = c} = Nat.card c.carrier := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight
      (fun _ => mem_carrier_iff_mk_eq.symm))
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hfiber, Nat.cast_id] using
    (Fintype.sum_fiberwise' ConjClasses.mk v)

/-- The full preimage of a class has kernel order times the class size. -/
theorem sum_card_map_fiber (f : G →* H) (hf : Function.Surjective f)
    (k : ConjClasses H) :
    ∑ c : ConjClasses G, (if map f c = k then Nat.card c.carrier else 0) =
      Nat.card f.ker * Nat.card k.carrier := by
  classical
  have hsource := sum_card_mul (G := G) (fun c => if map f c = k then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero] at hsource
  rw [hsource]
  change (∑ x : G, if ConjClasses.mk (f x) = k then 1 else 0) = _
  have hfiber (y : H) : Fintype.card {x : G // f x = y} = Nat.card f.ker := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (MonoidHom.fiberEquivKerOfSurjective hf y)
  have h := Fintype.sum_fiberwise' f (fun y => if ConjClasses.mk y = k then 1 else 0)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hfiber, Nat.cast_id] at h
  rw [← h, ← Finset.mul_sum]
  have htarget := sum_card_mul (G := H) (fun c => if c = k then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at htarget
  rw [← htarget]
end ConjClasses
