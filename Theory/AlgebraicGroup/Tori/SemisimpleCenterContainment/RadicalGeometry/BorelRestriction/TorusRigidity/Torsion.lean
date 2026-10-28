module

public import Theory.AlgebraicGroup.Tori.Character.Classification
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Finite-order points detect torus homomorphisms

Bounded-order points of a torus form a finite set. Two algebraic characters
agree if they agree on finite-order points: Laurent classification reduces
this to detecting a nonzero integer exponent by a root of unity of larger
order prime to the characteristic. Coordinate characters then give the same
conclusion for homomorphisms between tori. This is the torsion-detection step
in Borel, *Linear Algebraic Groups*, §8.10, without a separate density premise.
-/

open scoped BigOperators
namespace Theory.AlgebraicGroup
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem exists_torsion_unit_zpow_ne_one {z : ℤ} (hz : z ≠ 0) :
    ∃ a : kˣ, IsOfFinOrder a ∧ a ^ z ≠ 1 := by
  have hn : ∃ n : ℕ, z.natAbs < n ∧ (n : k) ≠ 0 := by
    by_cases h : ((z.natAbs + 1 : ℕ) : k) = 0
    · refine ⟨z.natAbs + 2, by omega, ?_⟩
      rw [show z.natAbs + 2 = (z.natAbs + 1) + 1 by omega,
        Nat.cast_add, h, Nat.cast_one, zero_add]
      exact one_ne_zero
    · exact ⟨z.natAbs + 1, by omega, h⟩
  obtain ⟨n, hn, hnk⟩ := hn
  let : NeZero (n : k) := ⟨hnk⟩
  obtain ⟨a, ha⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k n
  have hn0 : n ≠ 0 := by omega
  let b : kˣ := (ha.isUnit hn0).unit
  have hb : IsPrimitiveRoot b n := ha.isUnit_unit hn0
  refine ⟨b, hb.isOfFinOrder hn0, ?_⟩
  intro he
  have hd : n ∣ z.natAbs := Int.natCast_dvd.mp ((hb.zpow_eq_one_iff_dvd z).mp he)
  have habs : 0 < z.natAbs := Int.natAbs_pos.mpr hz
  exact (not_le_of_gt hn) (Nat.le_of_dvd habs hd)

public theorem torusCharacter_eq_of_torsion {T : Variety k} [AlgebraicGroup T]
    (hT : IsTorus T) (χ ψ : TorusCharacter T)
    (h : ∀ x : Variety.Point T, IsOfFinOrder x → χ.onPoints x = ψ.onPoints x) : χ = ψ := by
  classical
  obtain ⟨n, ⟨e⟩⟩ := hT
  obtain ⟨z, hz⟩ := dLaurentCharacter_surjective n (χ.comp e.hom)
  obtain ⟨w, hw⟩ := dLaurentCharacter_surjective n (ψ.comp e.hom)
  have hzw : z = w := by
    funext j
    by_contra hj
    obtain ⟨a, ha, haz⟩ := exists_torsion_unit_zpow_ne_one (k := k) (sub_ne_zero.mpr hj)
    let x : Variety.Point (dVariety k n) := (dPointEquiv n).symm (Pi.mulSingle j a)
    have hx : dPointEquiv n x = Pi.mulSingle j a := (dPointEquiv n).apply_symm_apply _
    obtain ⟨m, hm, ham⟩ := ha.exists_pow_eq_one
    have hxm : x ^ m = 1 := by
      apply (dPointEquiv n).injective
      rw [dPointEquiv_pow, hx, dPointEquiv_one]
      funext i
      by_cases hij : i = j
      · subst i
        simpa using ham
      · simp [hij]
    have hfin : IsOfFinOrder (e.hom.onPoints x) :=
      isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, by rw [← map_pow, hxm, map_one]⟩
    have hval := congrArg (fun t : Variety.Point (KMult k) => dPointEquiv 1 t 0)
      (h (e.hom.onPoints x) hfin)
    change dPointEquiv 1 ((χ.comp e.hom).onPoints x) 0 =
      dPointEquiv 1 ((ψ.comp e.hom).onPoints x) 0 at hval
    rw [← hz, ← hw, dLaurentCharacter_apply, dLaurentCharacter_apply, hx] at hval
    have hzprod : (∏ i, ((Pi.mulSingle j a : Fin n → kˣ) i) ^ z i) = a ^ z j := by
      simpa using Fintype.prod_eq_single j (f := fun i =>
        ((Pi.mulSingle j a : Fin n → kˣ) i) ^ z i) (by intro i hij; simp [hij])
    have hwprod : (∏ i, ((Pi.mulSingle j a : Fin n → kˣ) i) ^ w i) = a ^ w j := by
      simpa using Fintype.prod_eq_single j (f := fun i =>
        ((Pi.mulSingle j a : Fin n → kˣ) i) ^ w i) (by intro i hij; simp [hij])
    rw [hzprod, hwprod] at hval
    exact haz (by rw [zpow_sub, hval, mul_inv_cancel])
  have hc : χ.comp e.hom = ψ.comp e.hom := by rw [← hz, ← hw, hzw]
  apply AlgebraicGroup.Morphism.ext
  funext x
  have hx := congrArg (fun f : TorusCharacter (dVariety k n) => f.onPoints (e.inv.onPoints x)) hc
  change χ.onPoints (e.hom.onPoints (e.inv.onPoints x)) =
    ψ.onPoints (e.hom.onPoints (e.inv.onPoints x)) at hx
  rw [e.inv_hom_id] at hx
  exact hx

public theorem torus_morphism_eq_of_torsion {T Q : Variety k} [AlgebraicGroup T] [AlgebraicGroup Q]
    (hT : IsTorus T) (hQ : IsTorus Q) (f g : AlgebraicGroup.Morphism T Q)
    (h : ∀ x : Variety.Point T, IsOfFinOrder x → f.onPoints x = g.onPoints x) : f = g := by
  obtain ⟨n, ⟨e⟩⟩ := hQ
  apply AlgebraicGroup.Morphism.ext
  funext x
  apply Function.LeftInverse.injective (fun y => e.inv_hom_id y)
  apply (dPointEquiv n).injective
  funext i
  let χ : TorusCharacter Q := (dCoordinateCharacter n i).comp e.inv
  have hc := torusCharacter_eq_of_torsion hT (χ.comp f) (χ.comp g)
    (fun y hy => congrArg χ.onPoints (h y hy))
  exact congrFun (congrArg (dPointEquiv 1)
    (congrArg (fun t : TorusCharacter T => t.onPoints x) hc)) 0

omit [IsAlgClosed k] in
public theorem torus_bounded_torsion_finite {T : Variety k} [AlgebraicGroup T]
    (hT : IsTorus T) {m : ℕ} (hm : 0 < m) :
    {t : Variety.Point T | t ^ m = 1}.Finite := by
  classical
  obtain ⟨n, ⟨e⟩⟩ := hT
  let : NeZero m := ⟨hm.ne'⟩
  let f : {t : Variety.Point T | t ^ m = 1} → (Fin n → rootsOfUnity m k) :=
    fun t i => ⟨dPointEquiv n (e.inv.onPoints t.1) i, by
      change (dPointEquiv n (e.inv.onPoints t.1) i) ^ m = 1
      have h := congrFun (congrArg (dPointEquiv n) (congrArg e.inv.onPoints t.2)) i
      simpa only [map_pow, map_one, dPointEquiv_pow, dPointEquiv_one, Pi.pow_apply, Pi.one_apply] using h⟩
  have hfi : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Function.LeftInverse.injective (fun y => e.inv_hom_id y)
    apply (dPointEquiv n).injective
    funext i
    exact congrArg Subtype.val (congrFun hab i)
  let : Finite {t : Variety.Point T | t ^ m = 1} := Finite.of_injective f hfi
  exact Set.toFinite _
end Theory.AlgebraicGroup
