module

public import Stellmacher.Recognition.Parrott.NormalizerRootWordData

/-!
# Finite square arithmetic for Parrott's normalizer words

The code `(h,r,c)` records `x^i c^j b^k a^A u^U v^V t^T z^Z`,
where `h = i + 4*j + 16*k`, `r = A + 2*U + 4*V`, and `c = T + 2*Z`.
The proposed square is affine in the three noncentral elementary bits.
Its finite fibers are checked by kernel reduction: each relevant square has
sixteen roots in all coordinates and eight in each fixed-head coset.

The arithmetic is independent of the ambient group. The ambient square and
omega-action identities are separate obligations; this module does not assume
or assert that the proposed arithmetic already evaluates correctly in G.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed p.682, the sixteen-root paragraph, equations (1)–(19).
-/

@[expose] public section
namespace Stellmacher.Recognition.ParrottNormalizerRootSquare
abbrev Code := Fin 32 × Fin 8 × Fin 4

def row (h : Fin 32) : Fin 32 × Fin 32 × Fin 32 × Fin 32 × Fin 32 :=
  match h.val with
  | 0 => ⟨0, 0, 0, 0, 0⟩
  | 1 => ⟨2, 0, 0, 4, 8⟩
  | 2 => ⟨0, 0, 0, 8, 0⟩
  | 3 => ⟨2, 0, 0, 12, 8⟩
  | 4 => ⟨8, 0, 12, 0, 16⟩
  | 5 => ⟨26, 25, 12, 20, 24⟩
  | 6 => ⟨8, 21, 12, 8, 16⟩
  | 7 => ⟨26, 12, 12, 28, 24⟩
  | 8 => ⟨0, 0, 16, 0, 0⟩
  | 9 => ⟨2, 6, 16, 4, 8⟩
  | 10 => ⟨0, 12, 16, 8, 0⟩
  | 11 => ⟨2, 2, 16, 12, 8⟩
  | 12 => ⟨8, 0, 28, 0, 16⟩
  | 13 => ⟨26, 15, 28, 20, 24⟩
  | 14 => ⟨8, 9, 28, 8, 16⟩
  | 15 => ⟨26, 14, 28, 28, 24⟩
  | 16 => ⟨0, 4, 8, 16, 0⟩
  | 17 => ⟨2, 13, 8, 20, 8⟩
  | 18 => ⟨0, 4, 8, 24, 0⟩
  | 19 => ⟨2, 13, 8, 28, 8⟩
  | 20 => ⟨8, 18, 4, 16, 16⟩
  | 21 => ⟨26, 14, 4, 4, 24⟩
  | 22 => ⟨8, 7, 4, 24, 16⟩
  | 23 => ⟨26, 27, 4, 12, 24⟩
  | 24 => ⟨0, 20, 24, 16, 0⟩
  | 25 => ⟨2, 11, 24, 20, 8⟩
  | 26 => ⟨0, 24, 24, 24, 0⟩
  | 27 => ⟨2, 15, 24, 28, 8⟩
  | 28 => ⟨8, 2, 20, 16, 16⟩
  | 29 => ⟨26, 24, 20, 4, 24⟩
  | 30 => ⟨8, 11, 20, 24, 16⟩
  | _ => ⟨26, 25, 20, 12, 24⟩

def tailSquare (h : Fin 32) (r : Fin 8) : Nat :=
  (row h).2.1.val ^^^
    (if r.val % 2 = 1 then (row h).2.2.1.val else 0) ^^^
    (if r.val / 2 % 2 = 1 then (row h).2.2.2.1.val else 0) ^^^
    (if r.val / 4 = 1 then (row h).2.2.2.2.val else 0)

def smallSquare (p : Fin 32 × Fin 8) : Code :=
  ((row p.1).1, Fin.ofNat 8 (tailSquare p.1 p.2),
    Fin.ofNat 4 (tailSquare p.1 p.2 / 8))

def square (p : Code) : Code := smallSquare (p.1, p.2.1)

def outside (h : Fin 32) : Prop := h.val % 2 = 1 ∨ h.val / 4 % 2 = 1
instance (h : Fin 32) : Decidable (outside h) := inferInstanceAs (Decidable (_ ∨ _))

def selected (h : Fin 32) : Prop :=
  h = 1 ∨ h = 3 ∨ h = 4 ∨ h = 5 ∨ h = 12 ∨ h = 15 ∨
  h = 17 ∨ h = 19 ∨ h = 20 ∨ h = 21 ∨ h = 28 ∨ h = 31
instance (h : Fin 32) : Decidable (selected h) := inferInstanceAs (Decidable (_ ∨ _))

set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem selected_of_fourth_power : ∀ p : Fin 32 × Fin 8,
    outside p.1 → square (smallSquare p) = (0, 0, 0) → selected p.1 := by
  decide +kernel

theorem small_fiber_counts : ∀ p : Fin 32 × Fin 8, selected p.1 →
    (smallSquare p).1 ≠ 0 ∧
    Fintype.card {q : Fin 8 // smallSquare (p.1, q) = smallSquare p} = 2 ∧
    Fintype.card {q : Fin 32 × Fin 8 // smallSquare q = smallSquare p} = 4 := by
  decide +kernel

/-- Four choices of the central bits multiply the small root fiber by four. -/
theorem root_card (p : Code) (hp : selected p.1) :
    Nat.card {q : Code // square q = square p} = 16 := by
  let e : {q : Code // square q = square p} ≃
      {q : Fin 32 × Fin 8 // smallSquare q = square p} × Fin 4 := {
    toFun := fun q => (⟨(q.val.1, q.val.2.1), q.property⟩, q.val.2.2)
    invFun := fun q => ⟨(q.1.val.1, q.1.val.2, q.2), q.1.property⟩
    left_inv := by rintro ⟨⟨h,r,c⟩,hh⟩; rfl
    right_inv := by rintro ⟨⟨⟨h,r⟩,hh⟩,c⟩; rfl }
  have hc : Nat.card {q : Fin 32 × Fin 8 // smallSquare q = square p} = 4 := by
    rw [Nat.card_eq_fintype_card]
    exact (small_fiber_counts (p.1,p.2.1) hp).2.2
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_fin, hc]

/-- The fixed-head root fiber has eight elements. -/
theorem coset_root_card (p : Code) (hp : selected p.1) :
    Nat.card {q : Fin 8 × Fin 4 // square (p.1, q) = square p} = 8 := by
  let e : {q : Fin 8 × Fin 4 // square (p.1, q) = square p} ≃
      {q : Fin 8 // smallSquare (p.1, q) = square p} × Fin 4 := {
    toFun := fun q => (⟨q.val.1, q.property⟩, q.val.2)
    invFun := fun q => ⟨(q.1.val, q.2), q.1.property⟩
    left_inv := by rintro ⟨⟨r,c⟩,hh⟩; rfl
    right_inv := by rintro ⟨⟨r,hh⟩,c⟩; rfl }
  have hc : Nat.card {q : Fin 8 // smallSquare (p.1,q) = square p} = 2 := by
    rw [Nat.card_eq_fintype_card]
    exact (small_fiber_counts (p.1,p.2.1) hp).2.1
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_fin, hc]


section AmbientWords
open Subgroup
variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

/-- The elementary tail, with its three noncentral and two central bits. -/
def tailWord (f : ParrottSylowGeneratorData n) (q : Fin 8 × Fin 4) : G :=
  f.a ^ (q.1.val % 2) * f.u ^ (q.1.val / 2 % 2) * n.v ^ (q.1.val / 4) *
    n.t ^ (q.2.val % 2) * z ^ (q.2.val / 2)

/-- The ambient word represented by the finite square code. -/
def word (f : ParrottSylowGeneratorData n) (p : Code) : G :=
  f.x ^ (p.1.val % 4) * f.c ^ (p.1.val / 4 % 4) * f.b ^ (p.1.val / 16) *
    tailWord f p.2

theorem tailWord_mem (f : ParrottSylowGeneratorData n) (q : Fin 8 × Fin 4) :
    tailWord f q ∈ e.F := by
  have ha : f.a ∈ e.F := f.elementary_basis ▸ subset_closure (by simp)
  have hu : f.u ∈ e.F := f.elementary_basis ▸ subset_closure (by simp)
  exact e.F.mul_mem (e.F.mul_mem (e.F.mul_mem (e.F.mul_mem
    (e.F.pow_mem ha _) (e.F.pow_mem hu _)) (e.F.pow_mem n.v_mem_inf.2 _))
      (e.F.pow_mem n.t_mem_inf.2 _)) (e.F.pow_mem e.z_mem_inf.2 _)

theorem word_zero (f : ParrottSylowGeneratorData n) : word f (0,0,0) = 1 := by
  simp [word, tailWord]


/-- The binary encoding refines the existing F-valued word coordinates.
This package records coordinate geometry, independently of squaring. -/
structure CoordinateLaws (f : ParrottSylowGeneratorData n) : Prop where
  injective : Function.Injective (word f)
  range_eq_words : Set.range (word f) = Set.range f.normalizerRootWord
  elementary : ∀ p : Code, word f p ∈ e.F ↔ p.1 = 0
  coset : ∀ p q : Code, (word f p)⁻¹ * word f q ∈ e.F ↔ p.1 = q.1

/-- The two ambient identities needed by the checked finite calculation.
Both concern the supplied generators, not an abstract group model. -/
structure SquareLaws (f : ParrottSylowGeneratorData n) : Prop where
  square_eval : ∀ p : Code, word f (square p) = (word f p) ^ 2
  outside_omega : ∀ p : Code,
    word f p ∉ (omega₁ (pCore 2 (normalizer (e.F : Set G))) (p := 2)).map
      ((normalizer (e.F : Set G)).subtype.comp
        (pCore 2 (normalizer (e.F : Set G))).subtype) → outside p.1

end AmbientWords

end Stellmacher.Recognition.ParrottNormalizerRootSquare

