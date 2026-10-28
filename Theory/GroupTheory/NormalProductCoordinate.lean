module

public import Theory.GroupTheory.PCoreProduct
public import Theory.GroupTheory.NormalCenterQuotient
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Coordinate rigidity for center-free direct products

A normal homomorphism from a group whose every nontrivial normal quotient
is a 2-group into a center-free direct product has at most one nontrivial
coordinate. Applying this to the two coordinate inclusions of a product
automorphism shows that the automorphism preserves the factors or swaps them.
The proof is purely group-theoretic and retains the literal coordinate maps.
It is used for the two-factor branch of the normalized cubic G.6 source route.
-/

public section

open Subgroup
namespace Theory.GroupTheory
variable {H A B : Type*} [Group H] [Group A] [Group B]

theorem normal_hom_injective_or_trivial
    (hH : ∀ (N : Subgroup H) [N.Normal], N ≠ ⊥ → IsPGroup 2 (H ⧸ N))
    (hA : pCore 2 A = ⊥) (f : H →* A) [f.range.Normal] :
    Function.Injective f ∨ f = 1 := by
  by_cases hk : f.ker = ⊥
  · exact Or.inl ((MonoidHom.ker_eq_bot_iff f).mp hk)
  · right
    have hf : IsPGroup 2 f.range := (hH f.ker hk).of_surjective
      (QuotientGroup.quotientKerEquivRange f).toMonoidHom
      (QuotientGroup.quotientKerEquivRange f).surjective
    have he : f.range = ⊥ := le_bot_iff.mp (hA ▸ (show f.range ≤ pCore 2 A from
      le_sSup ⟨inferInstance, hf⟩))
    ext h
    exact he.le (show f h ∈ f.range from ⟨h,rfl⟩)

theorem normal_product_embedding_coordinate
    (hH : ∀ (N : Subgroup H) [N.Normal], N ≠ ⊥ → IsPGroup 2 (H ⧸ N))
    (hA : pCore 2 A = ⊥) (hB : center B = ⊥)
    (f : H →* A × B) [f.range.Normal] :
    (∀ h, (f h).2 = 1) ∨ (∀ h, (f h).1 = 1) := by
  let p : H →* A := (MonoidHom.fst A B).comp f
  let : p.range.Normal := by
    rw [MonoidHom.range_comp]
    exact (inferInstance : f.range.Normal).map _ (fun a => ⟨(a,1),rfl⟩)
  rcases normal_hom_injective_or_trivial hH hA p with hp | hp
  · left
    intro h
    have hc : (f h).2 ∈ center B := by
      apply mem_center_iff.mpr
      intro b
      obtain ⟨k,hk⟩ := (inferInstance : f.range.Normal).conj_mem
        (f h) ⟨h,rfl⟩ (1,b)
      have he : k = h := hp (by
        change (f k).1 = (f h).1
        simpa using congrArg Prod.fst hk)
      subst k
      have he' : (f h).2 = b * (f h).2 * b⁻¹ := congrArg Prod.snd hk
      exact (mul_inv_eq_iff_eq_mul.mp he'.symm)
    exact hB.le hc
  · right
    intro h
    exact congrArg (fun q : H →* A => q h) hp

theorem automorphism_product_coordinates [Nontrivial A] [Nontrivial B]
    (hA : ∀ (N : Subgroup A) [N.Normal], N ≠ ⊥ → IsPGroup 2 (A ⧸ N))
    (hB : ∀ (N : Subgroup B) [N.Normal], N ≠ ⊥ → IsPGroup 2 (B ⧸ N))
    (hcore : pCore 2 A = ⊥) (hz : center B = ⊥) (e : MulAut (A × B)) :
    ((∀ a, (e (a,1)).2 = 1) ∧ (∀ b, (e (1,b)).1 = 1)) ∨
      ((∀ a, (e (a,1)).1 = 1) ∧ (∀ b, (e (1,b)).2 = 1)) := by
  let f := e.toMonoidHom.comp (MonoidHom.inl A B)
  let g := e.toMonoidHom.comp (MonoidHom.inr A B)
  have hnL : (MonoidHom.inl A B).range = (MonoidHom.snd A B).ker := by
    ext x
    constructor
    · rintro ⟨a,rfl⟩; rfl
    · intro hx; exact ⟨x.1, Prod.ext rfl hx.symm⟩
  have hnR : (MonoidHom.inr A B).range = (MonoidHom.fst A B).ker := by
    ext x
    constructor
    · rintro ⟨b,rfl⟩; rfl
    · intro hx; exact ⟨x.2, Prod.ext hx.symm rfl⟩
  let : f.range.Normal := by
    rw [MonoidHom.range_comp, hnL]
    exact (inferInstance : (MonoidHom.snd A B).ker.Normal).map _ e.surjective
  let : g.range.Normal := by
    rw [MonoidHom.range_comp, hnR]
    exact (inferInstance : (MonoidHom.fst A B).ker.Normal).map _ e.surjective
  have hzero := normal_product_embedding_coordinate hA hcore hz f
  have hzero' := normal_product_embedding_coordinate hB hcore hz g
  rcases hzero with ha | ha <;> rcases hzero' with hb | hb
  · obtain ⟨b,hbne⟩ := exists_ne (1 : B)
    obtain ⟨⟨x,y⟩,he⟩ := e.surjective (1,b)
    have hh : (e (x,y)).2 = 1 := by
      have hxy : (x,y) = (x,1) * (1,y) := by simp
      rw [hxy, map_mul]
      change (f x).2 * (g y).2 = 1
      rw [ha, hb, one_mul]
    exact (hbne (by simpa only [he] using hh)).elim
  · exact Or.inl ⟨ha,hb⟩
  · exact Or.inr ⟨ha,hb⟩
  · obtain ⟨a,hane⟩ := exists_ne (1 : A)
    obtain ⟨⟨x,y⟩,he⟩ := e.surjective (a,1)
    have hh : (e (x,y)).1 = 1 := by
      have hxy : (x,y) = (x,1) * (1,y) := by simp
      rw [hxy, map_mul]
      change (f x).1 * (g y).1 = 1
      rw [ha, hb, one_mul]
    exact (hane (by simpa only [he] using hh)).elim
end Theory.GroupTheory
