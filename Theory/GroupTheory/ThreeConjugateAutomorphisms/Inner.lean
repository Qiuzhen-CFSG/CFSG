module

public import Theory.GroupTheory.ThreeConjugateAutomorphisms

/-!
# Passing three-conjugate generation from elements to inner automorphisms

In a centerless group, an inner automorphism has order two exactly when its
representing element does. Mapping the three cyclic subgroups along the
literal conjugation homomorphism gives the inner automorphism subgroup.
Thus element generation, together with innerness of involutory automorphisms,
gives the automorphism condition used in the sporadic degree argument.

Source application: Revin–Zavarnitsine, *Conjugate generation of sporadic almost
simple groups*, arXiv:2505.05173v2, Theorem 1, and Aschbacher–Smith G.7, K.4.
-/

public section
namespace Theory.GroupTheory
open Subgroup

/-- Three specified conjugates of `x` generate the original group. -/
@[expose] def ThreeConjugatesGenerate {S : Type*} [Group S] (x : S) : Prop :=
  ∃ g h : S, zpowers x ⊔ zpowers (g * x * g⁻¹) ⊔
    zpowers (h * x * h⁻¹) = ⊤

/-- An isomorphism transports both the generators and their conjugators. -/
theorem ThreeConjugatesGenerate.map {S T : Type*} [Group S] [Group T]
    {x : S} (hx : ThreeConjugatesGenerate x) (e : S ≃* T) :
    ThreeConjugatesGenerate (e x) := by
  obtain ⟨g, h, hgen⟩ := hx
  refine ⟨e g, e h, ?_⟩
  have hm := congrArg (Subgroup.map e.toMonoidHom) hgen
  simpa only [Subgroup.map_sup, MonoidHom.map_zpowers, map_mul, map_inv,
    MulEquiv.coe_toMonoidHom,
    Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] using hm

/-- One triple suffices for an entire conjugacy class. -/
theorem ThreeConjugatesGenerate.of_isConj {S : Type*} [Group S]
    {x y : S} (hx : ThreeConjugatesGenerate x) (hxy : IsConj x y) :
    ThreeConjugatesGenerate y := by
  obtain ⟨k, hk⟩ := isConj_iff.mp hxy
  have h := hx.map (MulAut.conj k)
  simpa only [MulAut.conj_apply, hk] using h

/-- Element generation supplies the automorphism condition whenever conjugation
is faithful and all involutory automorphisms are inner. -/
theorem threeConjugateAutomorphisms_of_inner
    {S : Type*} [Group S]
    (hconj : Function.Injective (MulAut.conj : S →* MulAut S))
    (hinner : ∀ t : MulAut S, t ^ 2 = 1 → ∃ x : S, MulAut.conj x = t)
    (hgen : ∀ x : S, orderOf x = 2 → ∃ g h : S,
      zpowers x ⊔ zpowers (g * x * g⁻¹) ⊔ zpowers (h * x * h⁻¹) = ⊤) :
    ThreeConjugateAutomorphisms S := by
  intro t ht ht2
  obtain ⟨x, rfl⟩ := hinner t ht2
  have hx : x ≠ 1 := by
    intro h
    exact ht (h ▸ map_one MulAut.conj)
  have hx2 : x ^ 2 = 1 := by
    apply hconj
    simpa only [map_pow, map_one] using ht2
  obtain ⟨g, h, hgh⟩ := hgen x (orderOf_eq_prime hx2 hx)
  refine ⟨g, h, ?_⟩
  have he := congrArg (fun H : Subgroup S => H.map MulAut.conj) hgh
  rw [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers,
    MonoidHom.map_zpowers, MonoidHom.map_zpowers, ← MonoidHom.range_eq_map] at he
  simpa only [map_mul, map_inv] using he.ge

end Theory.GroupTheory
