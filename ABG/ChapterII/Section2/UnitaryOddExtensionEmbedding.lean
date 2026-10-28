module
public import ABG.Basic
public import Mathlib.Algebra.Ring.Parity

/-!
# Unitary coefficient embeddings for odd-degree extensions

For n = k*d with d odd, every field embedding from GF(p^(2k)) to
GF(p^(2n)) induces an injective homomorphism between the original standard
GU2 groups. The public exposed map is the restriction of the actual GL
coefficient map; its underlying GL value and each matrix entry are recorded.
No assumption that p is odd is needed.

The source Hermitian form stores an involutive p^k-power Frobenius. Its dth
iterate is therefore the same involution, so the p^n-power Frobenius in the
larger field commutes with the coefficient embedding on the smaller field.
Mapping the original identity-Gram Hermitian equation proves membership;
field injectivity then proves injectivity entry by entry. All forms and
involution instances remain those of `ABG.unitaryForm`.
The stored-involution compatibility is also public for transporting
unitary coordinates through an odd fixed-field embedding.

This supplies the coefficient subgroup used to find a fixed Sylow subgroup
for odd field automorphisms in Alperin–Brauer–Gorenstein II.3 Proposition 3(iv),
article pp.27–28. It is independent of the subsequent odd-index and fixed-field
cardinality arguments.
-/

namespace ABG
open Matrix.GeneralLinearGroup

public theorem unitary_conj_odd_extension
    (p k n : ℕ) [Fact p.Prime] (hk : k ≠ 0) (hn : n ≠ 0)
    (d : ℕ) (hd : Odd d) (hnk : n = k * d)
    (e : GaloisField p (2 * k) →+* GaloisField p (2 * n))
    (x : GaloisField p (2 * k)) :
    (unitaryForm 2 p n hn).conj (e x) = e ((unitaryForm 2 p k hk).conj x) := by
  have hp : x ^ (p ^ n) = (unitaryForm 2 p k hk).conj x := by
    rw [hnk]
    change iterateFrobenius (GaloisField p (2 * k)) p (k * d) x = _
    rw [iterateFrobenius_mul_apply]
    exact congrFun ((unitaryForm 2 p k hk).conj_involutive.iterate_odd hd) x
  change (e x) ^ (p ^ n) = e ((unitaryForm 2 p k hk).conj x)
  rw [← map_pow, hp]

private theorem oddExtensionMap_mem_GU2
    (p k n : ℕ) [Fact p.Prime] (hk : k ≠ 0) (hn : n ≠ 0)
    (d : ℕ) (hd : Odd d) (hnk : n = k * d)
    (e : GaloisField p (2 * k) →+* GaloisField p (2 * n))
    (A : GU2 p k hk) :
    map e A.val ∈ (unitaryForm 2 p n hn).unitarySubgroup := by
  let Jk := unitaryForm 2 p k hk
  let Jn := unitaryForm 2 p n hn
  have hA := Jk.mem_unitarySubgroup_iff A.val |>.mp A.property
  apply Jn.mem_unitarySubgroup_iff (map e A.val) |>.mpr
  have hct : Jn.conjTranspose (map e A.val).val = e.mapMatrix (Jk.conjTranspose A.val.val) := by
    ext i j
    exact unitary_conj_odd_extension p k n hk hn d hd hnk e (A.val j i)
  change Jn.conjTranspose (map e A.val).val * 1 * (map e A.val).val = 1
  rw [hct]
  change Jk.conjTranspose A.val.val * 1 * A.val.val = 1 at hA
  have hm := congrArg e.mapMatrix hA
  have hmap : (map e A.val).val = e.mapMatrix A.val.val := by ext i j; rfl
  simpa only [map_mul, map_one, mul_one, hmap] using hm

/-- Entrywise field embedding restricted to the standard unitary groups
when the extension degree of the fixed fields is odd. -/
@[expose] public noncomputable def GU2OddExtensionHom
    (p k n : ℕ) [Fact p.Prime] (hk : k ≠ 0) (hn : n ≠ 0)
    (d : ℕ) (hd : Odd d) (hnk : n = k * d)
    (e : GaloisField p (2 * k) →+* GaloisField p (2 * n)) :
    GU2 p k hk →* GU2 p n hn where
  toFun A := ⟨map e A.val, by exact oddExtensionMap_mem_GU2 p k n hk hn d hd hnk e A⟩
  map_one' := Subtype.ext ((map e).map_one)
  map_mul' A B := Subtype.ext ((map e).map_mul A.val B.val)

@[simp] public theorem GU2OddExtensionHom_apply_val
    (p k n : ℕ) [Fact p.Prime] (hk : k ≠ 0) (hn : n ≠ 0)
    (d : ℕ) (hd : Odd d) (hnk : n = k * d)
    (e : GaloisField p (2 * k) →+* GaloisField p (2 * n)) (A : GU2 p k hk) :
    (GU2OddExtensionHom p k n hk hn d hd hnk e A).val = map e A.val := rfl

@[simp] public theorem GU2OddExtensionHom_apply_entry
    (p k n : ℕ) [Fact p.Prime] (hk : k ≠ 0) (hn : n ≠ 0)
    (d : ℕ) (hd : Odd d) (hnk : n = k * d)
    (e : GaloisField p (2 * k) →+* GaloisField p (2 * n))
    (A : GU2 p k hk) (i j : Fin 2) :
    (GU2OddExtensionHom p k n hk hn d hd hnk e A).val i j = e (A.val i j) := rfl

/-- The odd-extension unitary coefficient map is injective. -/
public theorem GU2OddExtensionHom_injective
    (p k n : ℕ) [Fact p.Prime] (hk : k ≠ 0) (hn : n ≠ 0)
    (d : ℕ) (hd : Odd d) (hnk : n = k * d)
    (e : GaloisField p (2 * k) →+* GaloisField p (2 * n)) :
    Function.Injective (GU2OddExtensionHom p k n hk hn d hd hnk e) := by
  intro A B h
  apply Subtype.ext
  ext i j
  apply e.injective
  exact congrArg (fun C : GU2 p n hn => C.val i j) h

end ABG
