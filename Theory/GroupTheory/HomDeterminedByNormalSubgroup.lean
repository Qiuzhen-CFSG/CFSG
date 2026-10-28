module
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic.Group

/-!
# A homomorphism determined by its restriction to a normal subgroup

If two group homomorphisms agree on a normal subgroup and its image has
trivial centralizer, they agree on the whole group. Neither finiteness nor
injectivity or surjectivity of the homomorphisms is required.

For any ambient element, normality shows that its two images induce the same
conjugation on the subgroup image. Their multiplicative discrepancy therefore
centralizes that image and must be one. This proves pointwise agreement.

This is the map-compatibility transfer needed in Alperin--Brauer--Gorenstein
II.3 Proposition 3, article pp26–28: preserving the prescribed normal SL2
core determines the entire PGL projection, since the PSL image has trivial
centralizer. It is stated for arbitrary groups at the reusable Theory layer.
-/

namespace MonoidHom
public theorem eq_of_agree_on_normal_of_centralizer_eq_bot
    {G H : Type*} [Group G] [Group H]
    (f g : G →* H) (N : Subgroup G) [N.Normal]
    (agree : ∀ n : N, f n = g n)
    (centralizer : Subgroup.centralizer (N.map f : Set H) = ⊥) : f = g := by
  apply DFunLike.ext
  intro x
  have hconj (n : G) (hn : n ∈ N) :
      f x * f n * (f x)⁻¹ = g x * f n * (g x)⁻¹ := by
    calc
      _ = f (x * n * x⁻¹) := by simp
      _ = g (x * n * x⁻¹) := agree ⟨_, Subgroup.Normal.conj_mem inferInstance n hn x⟩
      _ = g x * f n * (g x)⁻¹ := by rw [map_mul, map_mul, map_inv, agree ⟨n,hn⟩]
  have hmem : (f x)⁻¹ * g x ∈ Subgroup.centralizer (N.map f : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨n, hn, rfl⟩
    calc
      f n * ((f x)⁻¹ * g x) = (f x)⁻¹ * (f x * f n * (f x)⁻¹) * g x := by group
      _ = (f x)⁻¹ * (g x * f n * (g x)⁻¹) * g x := by rw [hconj n hn]
      _ = ((f x)⁻¹ * g x) * f n := by group
  rw [centralizer, Subgroup.mem_bot] at hmem
  exact (inv_mul_eq_one.mp hmem)
end MonoidHom
