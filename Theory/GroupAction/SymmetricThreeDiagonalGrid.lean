module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic.NormNum

/-!
# Symmetric-three orbits on a three-by-three grid

Two homomorphisms from an actual copy of S₃ to its natural permutation group,
each with a cubic in its image, give a three-point orbit and a six-point orbit
on the product of the natural sets. Each homomorphism is inner after identifying
its domain with S₃. Conjugating the coordinates therefore identifies the action
with the diagonal action, whose two orbits are the diagonal and its complement.

The small certificates inspect the six generator words, 36 pairs of generator
images, and 81 pairs of grid points. They never enumerate a space of functions
on S₃. Every computation is checked by the kernel.

This is the singular-coset orbit calculation used in M. Aschbacher,
“A 2-local characterization of M12”, Illinois J. Math. 47 (2003), 31–47,
Lemma 2.3(2)(b). The application to the literal local action is separate.
-/

namespace Theory.GroupAction.SymmetricThreeDiagonalGrid

/-- The natural symmetric group on three letters. -/
public abbrev S3 := Equiv.Perm (Fin 3)

private def s : S3 := Equiv.swap 0 1
private def t : S3 := Equiv.swap 1 2
private theorem six_words (p : S3) :
    p = 1 ∨ p = s ∨ p = t ∨ p = s * t ∨ p = t * s ∨ p = s * t * s := by
  revert p
  decide +kernel

private theorem generators_ext {B : Type*} [Monoid B] (f g : S3 →* B)
    (hs : f s = g s) (ht : f t = g t) : f = g := by
  ext p
  rcases six_words p with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [map_one, map_mul, hs, ht]

set_option synthInstance.maxSize 256 in
private theorem generator_pairs : ∀ x y : S3,
    x * x = 1 → y * y = 1 → (x * y) ^ 3 = 1 →
    x = y ∨ ∃ c : S3, x = c * s * c⁻¹ ∧ y = c * t * c⁻¹ := by
  decide +kernel

/-- An endomorphism of S₃ whose image contains a cubic is inner. -/
public theorem endomorphism_inner (f : S3 →* S3) (hf : ∃ a, orderOf (f a) = 3) :
    ∃ c : S3, ∀ p, f p = c * p * c⁻¹ := by
  have hs : s * s = 1 := by decide
  have ht : t * t = 1 := by decide
  have hst : (s * t) ^ 3 = 1 := by decide
  have hx : f s * f s = 1 := by rw [← map_mul, hs, map_one]
  have hy : f t * f t = 1 := by rw [← map_mul, ht, map_one]
  have hxy : (f s * f t) ^ 3 = 1 := by rw [← map_mul, ← map_pow, hst, map_one]
  rcases generator_pairs (f s) (f t) hx hy hxy with he | ⟨c, hc, hd⟩
  · obtain ⟨a, ha⟩ := hf
    have hsq : (f a) ^ 2 = 1 := by
      rcases six_words a with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [map_one, map_mul, ← he, pow_two, hx, one_mul, mul_one]
    have := orderOf_dvd_of_pow_eq_one hsq
    rw [ha] at this
    norm_num at this
  · have he : f = (MulAut.conj c).toMonoidHom := generators_ext f _ hc hd
    exact ⟨c, fun p => DFunLike.congr_fun he p⟩

private theorem pair_orbits : ∀ v w : Fin 3 × Fin 3,
    (∃ p : S3, (p v.1, p v.2) = w) ↔ (v.1 = v.2 ↔ w.1 = w.2) := by
  decide +kernel

private abbrev diagonal : Set (Fin 3 × Fin 3) := {v | v.1 = v.2}

private theorem diagonal_card : diagonal.ncard = 3 := by
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  decide

private theorem off_diagonal_card : diagonalᶜ.ncard = 6 := by
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  decide

private theorem diagonal_orbit (v : Fin 3 × Fin 3) :
    Set.range (fun p : S3 => (p v.1, p v.2)) =
      if v ∈ diagonal then diagonal else diagonalᶜ := by
  ext w
  change (∃ p : S3, (p v.1, p v.2) = w) ↔ _
  rw [pair_orbits]
  by_cases h : v ∈ diagonal <;> simp_all [diagonal]

variable {A : Type*} [Group A]

/-- The orbit for the simultaneous actions on the two coordinates. -/
@[expose] public def orbit (l r : A →* S3) (v : Fin 3 × Fin 3) : Set (Fin 3 × Fin 3) :=
  Set.range (fun a => (l a v.1, r a v.2))

/-- Two degree-three representations of S₃ with cubic images have one orbit
of length three and one orbit of length six on their product. -/
public theorem exists_profile (e : A ≃* S3) (l r : A →* S3)
    (hl : ∃ a, orderOf (l a) = 3) (hr : ∃ a, orderOf (r a) = 3) :
    ∃ T : Set (Fin 3 × Fin 3), T.ncard = 3 ∧
      (∀ v ∈ T, orbit l r v = T) ∧
      (∀ v ∉ T, (orbit l r v).ncard = 6) := by
  obtain ⟨c, hc⟩ := endomorphism_inner (l.comp e.symm.toMonoidHom)
    (by obtain ⟨a, ha⟩ := hl; exact ⟨e a, by simpa using ha⟩)
  obtain ⟨d, hd⟩ := endomorphism_inner (r.comp e.symm.toMonoidHom)
    (by obtain ⟨a, ha⟩ := hr; exact ⟨e a, by simpa using ha⟩)
  have hlc (a : A) : l a = c * e a * c⁻¹ := by simpa using hc (e a)
  have hrd (a : A) : r a = d * e a * d⁻¹ := by simpa using hd (e a)
  let E : (Fin 3 × Fin 3) ≃ (Fin 3 × Fin 3) := c.prodCongr d
  have hact (a : A) (v : Fin 3 × Fin 3) :
      (l a v.1, r a v.2) = E (e a (E.symm v).1, e a (E.symm v).2) := by
    rw [hlc, hrd]
    rfl
  have horbit (v : Fin 3 × Fin 3) :
      orbit l r v = E '' Set.range (fun p : S3 => (p (E.symm v).1, p (E.symm v).2)) := by
    ext w
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨_, ⟨e a, rfl⟩, (hact a v).symm⟩
    · rintro ⟨_, ⟨p, rfl⟩, rfl⟩
      exact ⟨e.symm p, by simpa using hact (e.symm p) v⟩
  refine ⟨E '' diagonal, ?_, ?_, ?_⟩
  · rw [Set.ncard_image_of_injective _ E.injective, diagonal_card]
  · intro v hv
    have hv' : E.symm v ∈ diagonal := by simpa using hv
    rw [horbit, diagonal_orbit, if_pos hv']
  · intro v hv
    have hv' : E.symm v ∉ diagonal := by simpa using hv
    rw [horbit, diagonal_orbit, if_neg hv',
      Set.ncard_image_of_injective _ E.injective, off_diagonal_card]

end Theory.GroupAction.SymmetricThreeDiagonalGrid
