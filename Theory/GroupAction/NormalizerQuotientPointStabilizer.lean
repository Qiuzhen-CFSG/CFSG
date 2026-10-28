module

public import Theory.GroupTheory.NormalizerAction
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Point stabilizers in a normalizer quotient

For z in A, the stabilizer of z in the faithful action of N(A)/C(A)
 is exactly the image of N(A) ∩ C(z). Consequently its order divides
 |C(z)|. The same divisibility holds after restricting to any faithfully
 embedded actor. Orbit–stabilizer then bounds the product of two coprime
 prime divisors of that actor which do not divide |C(z)| by |A|.

This is the quotient-lifting step in Aschbacher–Smith, combined manuscript
of 1 March 2004, proof of 14.4.4, printed p.1007. The calculation uses
actual conjugation and the literal normalizer/centralizer quotient.
-/

open Subgroup
namespace Subgroup.NormalizerAction
variable {G : Type*} [Group G] (A : Subgroup G)

@[expose] public def pointStabilizer (z : A) : Subgroup (Star A) :=
  (MulAction.stabilizer (MulAut A) z).comap (action A)

/-- Membership is literal fixation under conjugation. -/
public theorem mem_pointStabilizer (z : A) (x : Star A) :
    x ∈ pointStabilizer A z ↔ action A x z = z := Iff.rfl

/-- A representative fixes z exactly when it centralizes z in the ambient group. -/
public theorem quotient_mem_pointStabilizer (z : A) (x : normalizer (A : Set G)) :
    quotient A x ∈ pointStabilizer A z ↔
      (x : G) ∈ centralizer ({(z : G)} : Set G) := by
  rw [mem_pointStabilizer, action_quotient]
  change (⟨x.val * z.val * x.val⁻¹, _⟩ : A) = z ↔ _
  rw [Subtype.ext_iff, mem_centralizer_singleton_iff]
  exact mul_inv_eq_iff_eq_mul

/-- The full point stabilizer is the image of the relative centralizer. -/
public theorem pointStabilizer_eq_map (z : A) :
    pointStabilizer A z =
      ((centralizer ({(z : G)} : Set G)).subgroupOf
        (normalizer (A : Set G))).map (quotient A) := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (C A) x
    exact ⟨n, (quotient_mem_pointStabilizer A z n).mp hx, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact (quotient_mem_pointStabilizer A z n).mpr hn

/-- The quotient stabilizer cannot acquire new prime divisors. -/
public theorem pointStabilizer_card_dvd [Finite G] (z : A) :
    Nat.card (pointStabilizer A z) ∣
      Nat.card (centralizer ({(z : G)} : Set G)) := by
  let D := (centralizer ({(z : G)} : Set G)).subgroupOf
    (normalizer (A : Set G))
  let f : D →* centralizer ({(z : G)} : Set G) :=
    { toFun := fun x => ⟨x.val.val, x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro x y h
    have he : x.val.val = y.val.val := congrArg (fun t : centralizer ({(z : G)} : Set G) => (t : G)) h
    exact Subtype.ext (Subtype.ext he)
  rw [pointStabilizer_eq_map]
  exact (Subgroup.card_map_dvd D (quotient A)).trans
    (Subgroup.card_dvd_of_injective f hf)

end Subgroup.NormalizerAction

namespace Subgroup.NormalizerAction
variable {G : Type*} [Group G] [Finite G] (A : Subgroup G)

/-- Restricting to an embedded actor retains the ambient centralizer bound. -/
public theorem acting_stabilizer_card_dvd
    {X : Type*} [Group X] (f : X →* Star A) (hf : Function.Injective f) (z : A) :
    letI := MulAction.compHom A ((action A).comp f)
    Nat.card (MulAction.stabilizer X z) ∣
      Nat.card (centralizer ({(z : G)} : Set G)) := by
  let _ := MulAction.compHom A ((action A).comp f)
  let g : MulAction.stabilizer X z →* pointStabilizer A z :=
    { toFun := fun x => ⟨f x, x.property⟩
      map_one' := Subtype.ext f.map_one
      map_mul' := fun x y => Subtype.ext (f.map_mul x y) }
  have hg : Function.Injective g := by
    intro x y h
    exact Subtype.ext (hf (congrArg (fun t : pointStabilizer A z => (t : Star A)) h))
  exact (Subgroup.card_dvd_of_injective g hg).trans (pointStabilizer_card_dvd A z)

/-- Two coprime prime divisors absent from the point centralizer must both
divide the orbit length. -/
public theorem prime_pair_le_card
    {X : Type*} [Group X] [Finite X]
    (f : X →* Star A) (hf : Function.Injective f) (z : A)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p.Coprime q)
    (hpX : p ∣ Nat.card X) (hqX : q ∣ Nat.card X)
    (hpC : ¬ p ∣ Nat.card (centralizer ({(z : G)} : Set G)))
    (hqC : ¬ q ∣ Nat.card (centralizer ({(z : G)} : Set G))) :
    p * q ≤ Nat.card A := by
  let _ := MulAction.compHom A ((action A).comp f)
  let S := MulAction.stabilizer X z
  have hSC : Nat.card S ∣ Nat.card (centralizer ({(z : G)} : Set G)) :=
    acting_stabilizer_card_dvd A f hf z
  have hprod := S.card_mul_index
  have hpS : ¬ p ∣ Nat.card S := fun h => hpC (h.trans hSC)
  have hqS : ¬ q ∣ Nat.card S := fun h => hqC (h.trans hSC)
  have hpI : p ∣ S.index := (hp.dvd_mul.mp (hprod.symm ▸ hpX)).resolve_left hpS
  have hqI : q ∣ S.index := (hq.dvd_mul.mp (hprod.symm ▸ hqX)).resolve_left hqS
  have hI : p * q ≤ S.index := Nat.le_of_dvd (Nat.pos_of_ne_zero S.index_ne_zero_of_finite)
    (hpq.mul_dvd_of_dvd_of_dvd hpI hqI)
  exact hI.trans (by rw [MulAction.index_stabilizer]; exact Set.ncard_le_card _)

end Subgroup.NormalizerAction

