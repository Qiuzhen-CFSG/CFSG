module
public import Theory.GroupTheory.CoprimeNormalizerAutomorphisms
public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# Centralizers of prime subgroups through coprime kernels

A surjection with kernel of order prime to p maps the centralizer of any
p-subgroup onto the centralizer of its image. The Frattini argument first
lifts a centralizing element into the subgroup normalizer; injectivity on
the p-subgroup then makes that lift centralize it. The p-subgroup need not
be normal in the whole domain.

This supplies centralizer divisibility for the actual symmetric-linear
subgroup of J4, used in Aschbacher--Smith 12.1.1, printed p.788.
-/

public section
namespace Subgroup
variable {G H : Type*} [Group G] [Finite G] [Group H]

/-- Coprime kernels preserve centralizers of arbitrary p-subgroups. -/
theorem map_centralizer_eq_of_isPGroup_of_surjective_coprime (p : ℕ) [Fact p.Prime]
    (A : Subgroup G) (hA : IsPGroup p A) (f : G →* H)
    (hf : Function.Surjective f) (hk : Nat.Coprime p (Nat.card f.ker)) :
    (centralizer (A : Set G)).map f = centralizer (A.map f : Set H) := by
  let : Fact (IsPGroup p A) := ⟨hA⟩
  apply le_antisymm (map_centralizer_le_centralizer_image _ f)
  intro y hy
  have hn := (centralizer_le_normalizer (A.map f : Set H)) hy
  rw [normalizer_map_eq_of_coprime_kernel p A f hf hk] at hn
  obtain ⟨x,hx,rfl⟩ := hn
  refine ⟨x,?_,rfl⟩
  intro a ha
  have hm : x*a*x⁻¹ ∈ A := (mem_normalizer_iff.mp hx a).mp ha
  have he : (⟨x*a*x⁻¹,hm⟩ : A) = ⟨a,ha⟩ := by
    apply injective_comp_subtype_of_coprime_ker f hk A hA
    change f (x*a*x⁻¹) = f a
    rw [map_mul,map_mul,map_inv,←hy (f a) (mem_map_of_mem f ha)]
    simp only [mul_inv_cancel_right]
  exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he)).symm


end Subgroup
