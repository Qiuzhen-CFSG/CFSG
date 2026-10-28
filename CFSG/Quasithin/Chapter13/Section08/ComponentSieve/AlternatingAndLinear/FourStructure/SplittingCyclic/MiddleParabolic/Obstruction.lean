module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.MiddleParabolic.Coordinates

/-!
# No normal four-group in the standard middle parabolic

The displayed nine-entry block calculation is checked by kernel reduction.
For each involution outside the two-element central subgroup, eight explicit
conjugators produce at least four nonidentity conjugates. A normalized
subgroup of order four cannot contain such an element, and the remaining
central elements are determined by a single binary entry.

The equations below connect every finite calculation to the actual action
in GL₄(2). Normality is relative to the line--hyperplane stabilizer.
Reference: Aschbacher--Smith 13.8.25, printed p.962 (PDF p.979).
-/

public section

namespace BinaryLinear.MiddleParabolic

private def identity : Params := ![0,0,0,1,0,0,0,1,0]
private def square (p : Params) : Params :=
 ![p 0 + p 0*p 3 + p 1*p 6, p 1 + p 0*p 4 + p 1*p 7,
 p 0*p 5 + p 1*p 8, p 3*p 3 + p 4*p 6, p 3*p 4 + p 4*p 7,
 p 3*p 5 + p 4*p 8 + p 5, p 6*p 3 + p 7*p 6, p 6*p 4 + p 7*p 7,
 p 6*p 5 + p 7*p 8 + p 8]
private def conjugate (k : Fin 8) (p : Params) : Params :=
 match k with
 | 0 => p
 | 1 => ![p 0+p 3+1,p 1+p 4,p 2+p 5,p 3,p 4,p 5,p 6,p 7,p 8]
 | 2 => ![p 0+p 6,p 1+p 7+1,p 2+p 8,p 3,p 4,p 5,p 6,p 7,p 8]
 | 3 => ![p 0,p 1,p 2+p 0,p 3,p 4,p 5+p 3+1,p 6,p 7,p 8+p 6]
 | 4 => ![p 0,p 1,p 2+p 1,p 3,p 4,p 5+p 4,p 6,p 7,p 8+p 7+1]
 | 5 => ![p 0,p 1+p 0,p 2,p 3+p 6,p 4+p 3+p 7+p 6,p 5+p 8,p 6,p 7+p 6,p 8]
 | 6 => ![p 1,p 0,p 2,p 7,p 6,p 8,p 4,p 3,p 5]
 | 7 => ![p 0+p 1,p 1,p 2,p 3+p 4,p 4,p 5,p 6+p 3+p 7+p 4,p 7+p 4,p 8+p 5]

private def orbit (p : Params) : Finset Params := Finset.univ.image (fun k => conjugate k p)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
private theorem orbit_bound : ∀ p : Params, square p = identity →
    (5 ≤ (insert identity (orbit p)).card ∨
      p = ![0,0,p 2,1,0,0,0,1,0]) := by
  decide +kernel


private theorem block_square (p : Params) (v : V) :
    block p (block p v) = block (square p) v := by
  ext i
  fin_cases i <;> simp [block, square] <;> ring_nf
  simp [show (2 : ZMod 2) = 0 by decide]

private theorem block_conjugate (p : Params) (k : Fin 8) (v : V) :
    actorFun k (block p (actorFun k v)) = block (conjugate k p) v := by
  fin_cases k <;> ext i <;> fin_cases i <;> simp [block, conjugate, actorFun] <;> ring

private theorem coordinates_of_apply {g : BinaryLinear.GL V} {p : Params}
    (h : ∀ v, g v = block p v) : coordinates g = p := by
  ext i
  fin_cases i <;> simp [coordinates, h, block]

@[simp] private theorem coordinates_one : coordinates (1 : BinaryLinear.GL V) = identity := by
  decide +kernel

private theorem coordinates_square {g : BinaryLinear.GL V}
    (hg : g ∈ parabolic line ⊓ parabolic hyperplane) :
    coordinates (g * g) = square (coordinates g) := by
  apply coordinates_of_apply
  intro v
  change g (g v) = _
  rw [apply_eq_block hg, apply_eq_block hg, block_square]

private theorem coordinates_conjugate (k : Fin 8) {g : BinaryLinear.GL V}
    (hg : g ∈ parabolic line ⊓ parabolic hyperplane) :
    coordinates (actor k * g * (actor k)⁻¹) = conjugate k (coordinates g) := by
  apply coordinates_of_apply
  intro v
  change actorFun k (g (actorFun k v)) = _
  rw [apply_eq_block hg, block_conjugate]


/-- No subgroup of order four and exponent two is normal in the standard middle parabolic. -/
theorem standard_no_normal_four (E : Subgroup (BinaryLinear.GL V))
    (hE : ∀ x ∈ E, x ^ 2 = 1) (hcard : Nat.card E = 4)
    (hEH : E ≤ parabolic line ⊓ parabolic hyperplane)
    (hHE : parabolic line ⊓ parabolic hyperplane ≤ Subgroup.normalizer E) : False := by
  classical
  let : Finite E := Nat.finite_of_card_ne_zero (by omega)
  let : Fintype E := Fintype.ofFinite E
  let C : Finset Params := Finset.univ.image (fun x : E => coordinates x.val)
  have hC : C.card ≤ 4 := by
    calc
      C.card ≤ Fintype.card E := Finset.card_image_le
      _ = 4 := by rwa [← Nat.card_eq_fintype_card]
  have hp (x : E) : coordinates x.val = ![0,0,coordinates x.val 2,1,0,0,0,1,0] := by
    have hs : square (coordinates x.val) = identity := by
      rw [← coordinates_square (hEH x.property), ← pow_two, hE x.val x.property,
        coordinates_one]
    rcases orbit_bound (coordinates x.val) hs with hlarge | hcentral
    · have hsubset : insert identity (orbit (coordinates x.val)) ⊆ C := by
        intro p hp
        rcases Finset.mem_insert.mp hp with rfl | hp
        · apply Finset.mem_image.mpr
          exact ⟨1, Finset.mem_univ _, coordinates_one⟩
        · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hp
          let y : E := ⟨actor k * x.val * (actor k)⁻¹,
            (hHE (actor_mem k) x.val).mp x.property⟩
          exact Finset.mem_image.mpr ⟨y, Finset.mem_univ _,
            coordinates_conjugate k (hEH x.property)⟩
      have := Finset.card_le_card hsubset
      omega
    · exact hcentral
  have hinj : Function.Injective (fun x : E => coordinates x.val 2) := by
    intro x y hxy
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    rw [apply_eq_block (hEH x.property), apply_eq_block (hEH y.property), hp x, hp y]
    change coordinates x.val 2 = coordinates y.val 2 at hxy
    rw [hxy]
  have hb := Nat.card_le_card_of_injective _ hinj
  have : Nat.card E ≤ 2 := by simpa using hb
  omega

end BinaryLinear.MiddleParabolic

end
