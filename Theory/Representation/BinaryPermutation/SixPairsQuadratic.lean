module

public import Theory.Representation.BinaryPermutation
public import Theory.Representation.BinaryOffender.Defs
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Quadratic four-groups on the fifteen-pair permutation module

Let a group act on six letters with image containing A₆. On a quotient of
its binary permutation module on unordered pairs, suppose the two double
transpositions (01)(23) and (02)(13) act quadratically. Their second
displacement on the edge {0,4} kills the four-edge star at 4 omitting 5.
Even permutations give all such stars. Subtracting stars at the same vertex
identifies incident edges, hence all basis images. The quotient action is trivial.

This supplies a possible replacement section in Aschbacher–Smith 13.8.21(2),
printed p.956: 13.8.4(5),(6) give a noncentral quadratic permutation quotient
on V_H/U_H. Identifying its actual parabolic cosets with these pairs and its
two-core with this four-group remains a separate, necessary model calculation.
No claim of nonquadraticity on the six-dimensional hexacode is used.
-/

@[expose] public section
namespace BinaryPermutation.SixPairsQuadratic
open Representation.BinaryOffender

/-- The fifteen unordered pairs of six letters. -/
abbrev Pair := {s : Finset (Fin 6) // s.card = 2}

/-- Relabeling the actual two-element subsets. -/
def pairPerm (g : Equiv.Perm (Fin 6)) : Equiv.Perm Pair where
  toFun s := ⟨s.val.map g.toEmbedding, by simp [s.property]⟩
  invFun s := ⟨s.val.map g.symm.toEmbedding, by simp [s.property]⟩
  left_inv s := by
    apply Subtype.ext
    dsimp only
    rw [Finset.map_map]
    convert (Finset.map_refl (s := s.val)) using 1
    congr 1
    ext x
    simp
  right_inv s := by
    apply Subtype.ext
    dsimp only
    rw [Finset.map_map]
    convert (Finset.map_refl (s := s.val)) using 1
    congr 1
    ext x
    simp

/-- The induced permutation homomorphism on pairs. -/
def pairHom : Equiv.Perm (Fin 6) →* Equiv.Perm Pair where
  toFun := pairPerm
  map_one' := by
    apply Equiv.ext
    intro s
    apply Subtype.ext
    exact Finset.map_refl
  map_mul' g h := by
    apply Equiv.ext
    intro s
    apply Subtype.ext
    change s.val.map _ = (s.val.map _).map _
    rw [Finset.map_map]
    rfl

/-- The binary permutation action on the fifteen pairs. -/
abbrev action : Representation (ZMod 2) (Equiv.Perm (Fin 6)) (BinaryPermutation.Full Pair) :=
  (BinaryPermutation.representation Pair).comp pairHom

private def edge (i j : Fin 6) : BinaryPermutation.Full Pair :=
  fun p => if p.val = {i,j} then 1 else 0

private def star (i j : Fin 6) : BinaryPermutation.Full Pair :=
  fun p => if i ∈ p.val ∧ j ∉ p.val then 1 else 0

/-- The first generator of the four-group fixing the last two letters. -/
abbrev first : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 2 3
/-- The second generator of the same four-group. -/
abbrev second : Equiv.Perm (Fin 6) := Equiv.swap 0 2 * Equiv.swap 1 3

private theorem displacement :
    action first (action second (edge 0 4) - edge 0 4) - (action second (edge 0 4) - edge 0 4) =
      star 4 5 := by decide +kernel

private def transporter (i j : Fin 6) : Equiv.Perm (Fin 6) :=
  let t := Equiv.swap 4 i
  let u := Equiv.swap (t 5) j * t
  if Equiv.Perm.sign u = 1 then u else u * Equiv.swap 0 1

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
private theorem transport_check : ∀ i j : Fin 6, i ≠ j →
    Equiv.Perm.sign (transporter i j) = 1 ∧
    action (transporter i j) (star 4 5) = star i j := by decide +kernel

private theorem star_difference : ∀ i j k : Fin 6, i ≠ j → i ≠ k → j ≠ k →
    star i j - star i k = edge i j - edge i k := by decide +kernel

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem basis_images_equal (f : BinaryPermutation.Full Pair →ₗ[ZMod 2] V)
    (hs : ∀ i j : Fin 6, i ≠ j → f (star i j) = 0) :
    ∀ p : Pair, f (Pi.single p 1) = f (edge 0 1) := by
  have he (i j k : Fin 6) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      f (edge i j) = f (edge i k) := by
    have h := congrArg f (star_difference i j k hij hik hjk)
    rw [map_sub, map_sub, hs i j hij, hs i k hik, sub_self] at h
    exact sub_eq_zero.mp h.symm
  have hsym (i j : Fin 6) : edge i j = edge j i := by
    funext p
    unfold edge
    rw [Finset.pair_comm]
  have h0 (j : Fin 6) (hj : j ≠ 0) : f (edge 0 j) = f (edge 0 1) := by
    by_cases h : j = 1
    · rw [h]
    · exact he 0 j 1 hj.symm (by decide +kernel) h
  have hall (i j : Fin 6) (hij : i ≠ j) : f (edge i j) = f (edge 0 1) := by
    by_cases hi : i = 0
    · subst i
      exact h0 j hij.symm
    by_cases hj : j = 0
    · subst j
      rw [hsym]
      exact h0 i hi
    exact (he i j 0 hij hi hj).trans ((congrArg f (hsym i 0)).trans (h0 i hi))
  intro p
  obtain ⟨i, j, hij, hp⟩ := Finset.card_eq_two.mp p.property
  have hsingle : ∀ (p : Pair) (i j : Fin 6), p.val = {i,j} → Pi.single p 1 = edge i j := by
    intro p i j hp
    ext q
    simp only [Pi.single_apply, edge, ← hp, ← Subtype.ext_iff]
  rw [hsingle p i j hp]
  exact hall i j hij

private theorem action_single (g : Equiv.Perm (Fin 6)) (p : Pair) :
    action g (Pi.single p 1) = Pi.single (pairPerm g p) 1 := by
  ext q
  change (Pi.single p (1 : ZMod 2) : BinaryPermutation.Full Pair) ((pairPerm g).symm q) =
    (Pi.single (pairPerm g p) (1 : ZMod 2) : BinaryPermutation.Full Pair) q
  simp only [Pi.single_apply, Equiv.symm_apply_eq]

/-- Quadraticity of the marked four-group forces every equivariant quotient
to have trivial action. -/
theorem quotient_action_trivial {H : Type*} [Group H]
    (φ : H →* Equiv.Perm (Fin 6))
    (heven : ∀ g : alternatingGroup (Fin 6), ∃ h : H, φ h = g.val)
    (ρ : Representation (ZMod 2) H V)
    (f : BinaryPermutation.Full Pair →ₗ[ZMod 2] V) (hf : Function.Surjective f)
    (heq : ∀ h v, f (action (φ h) v) = ρ h (f v))
    (x y : H) (hx : φ x = first) (hy : φ y = second)
    (hquad : ∀ v, ρ x (ρ y v - v) = ρ y v - v) : ∀ h v, ρ h v = v := by
  have hw : f (star 4 5) = 0 := by
    rw [← displacement, ← hx, ← hy, map_sub, heq, map_sub, heq]
    exact sub_eq_zero.mpr (hquad _)
  have hs (i j : Fin 6) (hij : i ≠ j) : f (star i j) = 0 := by
    obtain ⟨hg, ht⟩ := transport_check i j hij
    obtain ⟨h, hh⟩ := heven ⟨transporter i j, hg⟩
    change φ h = transporter i j at hh
    rw [← ht, ← hh, heq, hw, map_zero]
  have hsingle := basis_images_equal f hs
  have hinv (h : H) : f.comp (action (φ h)) = f := by
    apply LinearMap.pi_ext
    intro p c
    have hc : Pi.single p c = c • Pi.single p (1 : ZMod 2) := by
      simpa using Pi.single_smul (f := fun _ : Pair => ZMod 2) p c (1 : ZMod 2)
    rw [hc, map_smul, map_smul]
    congr 1
    change f (action (φ h) (Pi.single p 1)) = f (Pi.single p 1)
    rw [action_single, hsingle, hsingle]
  intro h v
  obtain ⟨u, rfl⟩ := hf v
  rw [← heq]
  exact LinearMap.congr_fun (hinv h) u
/-- A subgroup containing the two specified double transpositions cannot act
quadratically on a noncentral quotient of the pair permutation module.
Surjectivity onto the symmetric group is unnecessary: the image need only
contain the alternating group. -/
theorem not_quadratic_of_noncentral_quotient {H : Type*} [Group H]
    (φ : H →* Equiv.Perm (Fin 6))
    (heven : ∀ g : alternatingGroup (Fin 6), ∃ h : H, φ h = g.val)
    (ρ : Representation (ZMod 2) H V)
    (f : BinaryPermutation.Full Pair →ₗ[ZMod 2] V) (hf : Function.Surjective f)
    (heq : ∀ h v, f (action (φ h) v) = ρ h (f v))
    (hnoncentral : ∃ h v, ρ h v ≠ v)
    (A : Subgroup H) (x y : H) (hxA : x ∈ A) (hyA : y ∈ A)
    (hx : φ x = first) (hy : φ y = second) : ¬ IsQuadratic ρ A := by
  intro hquad
  have ht := quotient_action_trivial φ heven ρ f hf heq x y hx hy
    (fun v => hquad x hxA y hyA v)
  obtain ⟨h,v,hv⟩ := hnoncentral
  exact hv (ht h v)

end BinaryPermutation.SixPairsQuadratic
