module
public import Theory.SpecificGroups.Alternating.FiveLocalGeometry.CubicNormalizer
public import Mathlib.Data.Fintype.Perm

/-!
# Extending a prescribed cubic-normalizer map across A₅

Every automorphism of S₃ is inner: its two standard transpositions map to
a distinct pair of transpositions, and simultaneous conjugation matches
them. Cubic Sylow conjugacy first identifies the two normalizers in A₅;
an inner adjustment in the target normalizer then matches any prescribed
isomorphism on the entire S₃.

The J₂ source comparison applies this to the literal intersections of its
vertex normalizer with the local A₅ centralizer.
Source: Aschbacher, *Sporadic Groups* (1994), 47.10, p.266, citing the
extension exercise for A₅. This theorem does not additionally prescribe
an edge or a second cubic subgroup.
-/

public section
namespace SymmetricThreeInner
abbrev S3 := Equiv.Perm (Fin 3)
private def a : S3 := Equiv.swap 0 1
private def b : S3 := Equiv.swap 1 2
private theorem pairs (x y : S3) (hx : x ^ 2 = 1) (hy : y ^ 2 = 1)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hne : x ≠ y) :
    ∃ g : S3, g * a * g⁻¹ = x ∧ g * b * g⁻¹ = y := by
  have h : ∀ x y : S3, (x ^ 2 = 1 ∧ y ^ 2 = 1 ∧ x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y) →
      ∃ g : S3, g * a * g⁻¹ = x ∧ g * b * g⁻¹ = y := by decide +kernel
  exact h x y ⟨hx, hy, hx1, hy1, hne⟩
private theorem generated (x : S3) :
    x = 1 ∨ x = a ∨ x = b ∨ x = a * b ∨ x = b * a ∨ x = a * b * a := by
  have h : ∀ x : S3,
      x = 1 ∨ x = a ∨ x = b ∨ x = a * b ∨ x = b * a ∨ x = a * b * a := by
    decide +kernel
  exact h x

/-- All automorphisms of the symmetric group on three letters are inner. -/
theorem exists_conjugator (f : MulAut S3) : ∃ g : S3, f = MulAut.conj g := by
  obtain ⟨g, ha, hb⟩ := pairs (f a) (f b)
    (by rw [← map_pow, show a ^ 2 = 1 by decide +kernel, map_one])
    (by rw [← map_pow, show b ^ 2 = 1 by decide +kernel, map_one])
    (fun h => (show a ≠ 1 by decide +kernel) (f.injective (h.trans (map_one f).symm)))
    (fun h => (show b ≠ 1 by decide +kernel) (f.injective (h.trans (map_one f).symm)))
    (fun h => (show a ≠ b by decide +kernel) (f.injective h))
  refine ⟨g, ?_⟩
  apply MulEquiv.ext
  intro x
  have ha' : f a = MulAut.conj g a := ha.symm
  have hb' : f b = MulAut.conj g b := hb.symm
  rcases generated x with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [map_one, map_mul, ha', hb']
end SymmetricThreeInner

open Subgroup
namespace alternatingGroup.FiveLocalGeometry
variable {H J : Type*} [Group H] [Finite H] [Group J] [Finite J]

omit [Finite H] in
/-- A prescribed isomorphism of cubic normalizers extends to the two A₅ groups. -/
theorem extend_cubic_normalizer (eH : H ≃* A5) (eJ : J ≃* A5)
    (P : Subgroup H) (Q : Subgroup J) (hP : Nat.card P = 3) (hQ : Nat.card Q = 3)
    (f : normalizer (P : Set H) ≃* normalizer (Q : Set J)) :
    ∃ e : H ≃* J, P.map e.toMonoidHom = Q ∧
      ∀ n : normalizer (P : Set H), e n = (f n : J) := by
  let a0 := eH.trans eJ.symm
  obtain ⟨t, ht⟩ := cubic_conjugate eJ (P.map a0.toMonoidHom) Q
    (by rw [card_map_of_injective a0.injective, hP]) hQ
  let a := a0.trans (MulAut.conj t)
  have ha : P.map a.toMonoidHom = Q := by
    rw [map_map] at ht
    exact ht
  let aN : normalizer (P : Set H) ≃* normalizer (Q : Set J) :=
    (MulEquiv.subgroupMap a (normalizer (P : Set H))).trans
      (MulEquiv.subgroupCongr ((map_equiv_normalizer_eq P a).trans (congrArg (fun R : Subgroup J => normalizer (R : Set J)) ha)))
  obtain ⟨eN⟩ := cubic_normalizer_equiv eJ Q hQ
  let d := aN.symm.trans f
  obtain ⟨g, hg⟩ := SymmetricThreeInner.exists_conjugator (MulAut.congr eN d)
  let u := eN.symm g
  have hd : d = MulAut.conj u := by
    apply (MulAut.congr eN).injective
    rw [hg]
    apply MulEquiv.ext
    intro x
    change g * x * g⁻¹ = eN (eN.symm g * eN.symm x * (eN.symm g)⁻¹)
    rw [map_mul, map_mul, map_inv, eN.apply_symm_apply, eN.apply_symm_apply]
  let e := a.trans (MulAut.conj (u : J))
  refine ⟨e, ?_, ?_⟩
  · change P.map ((MulAut.conj (u : J)).toMonoidHom.comp a.toMonoidHom) = Q
    rw [← map_map]
    rw [ha]
    exact mem_normalizer_iff_map_conj_eq.mp u.property
  · intro n
    have he := congrArg (fun b : MulAut (normalizer (Q : Set J)) => b (aN n)) hd
    change f (aN.symm (aN n)) = u * aN n * u⁻¹ at he
    rw [aN.symm_apply_apply] at he
    exact (congrArg Subtype.val he).symm
end alternatingGroup.FiveLocalGeometry
