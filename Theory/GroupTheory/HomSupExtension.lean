module
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Extending a quotient homomorphism across a normalizing product

If `A` normalizes `N`, an onto map from `A` whose kernel contains
`A ∩ N` extends across `A ⊔ N`, killing the second factor. The construction
uses the literal quotient map and preserves the exact kernel. This is the
quotient bridge needed to extend the core commutator row across the second
hat layer.
-/
public section
open Subgroup
open scoped Pointwise
namespace MonoidHom
variable {G T : Type*} [Group G] [Group T]

theorem exists_sup_extension {A N : Subgroup G} (hn : A ≤ normalizer N)
    (f : A →* T) (hf : Function.Surjective f) (hk : f.ker = N.subgroupOf A) :
    ∃ q : (A ⊔ N : Subgroup G) →* T, Function.Surjective q ∧
      q.ker = N.subgroupOf (A ⊔ N) ∧
      ∀ a : A, q (inclusion le_sup_left a) = f a := by
  let := normal_subgroupOf_sup_of_le_normalizer hn
  let mk := QuotientGroup.mk' (N.subgroupOf (A ⊔ N))
  let phi : A →* _ := mk.comp (inclusion le_sup_left)
  have hphi : Function.Surjective phi := by
    intro v
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf (A ⊔ N)) v
    have hx : (x : G) ∈ (A : Set G) * (N : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right A N hn]
      exact x.property
    obtain ⟨a,ha,n,hn',han⟩ := hx
    refine ⟨⟨a,ha⟩,?_⟩
    have hnq : mk (⟨n,mem_sup_right hn'⟩ : (A ⊔ N : Subgroup G)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hn'
    have hx' : x = (⟨a,mem_sup_left ha⟩ : (A ⊔ N : Subgroup G)) * ⟨n,mem_sup_right hn'⟩ :=
      Subtype.ext han.symm
    change mk ⟨a,mem_sup_left ha⟩ = mk x
    rw [hx',map_mul,hnq,mul_one]
  have hker : phi.ker ≤ f.ker := by
    intro a ha
    rw [hk]
    change inclusion (show A ≤ A ⊔ N from le_sup_left) a ∈ N.subgroupOf (A ⊔ N)
    exact (QuotientGroup.eq_one_iff (inclusion le_sup_left a)).mp
      (show mk (inclusion le_sup_left a) = 1 from ha)
  let d := phi.liftOfSurjective hphi ⟨f,hker⟩
  let q := d.comp mk
  have happly (a : A) : q (inclusion le_sup_left a) = f a := by
    exact phi.liftOfRightInverse_comp_apply _ (Function.rightInverse_surjInv hphi) ⟨f,hker⟩ a
  refine ⟨q,?_,?_,happly⟩
  · intro t
    obtain ⟨a,rfl⟩ := hf t
    exact ⟨inclusion le_sup_left a,happly a⟩
  · ext x
    have hx : (x : G) ∈ (A : Set G) * (N : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right A N hn]
      exact x.property
    obtain ⟨a,ha,n,hn',han⟩ := hx
    have hnq : q (⟨n,mem_sup_right hn'⟩ : (A ⊔ N : Subgroup G)) = 1 := by
      change d (mk _) = 1
      rw [show mk (⟨n,mem_sup_right hn'⟩ : (A ⊔ N : Subgroup G)) = 1 from
        (QuotientGroup.eq_one_iff _).mpr hn',map_one]
    have hx' : x = (⟨a,mem_sup_left ha⟩ : (A ⊔ N : Subgroup G)) * ⟨n,mem_sup_right hn'⟩ :=
      Subtype.ext han.symm
    change q x = 1 ↔ (x : G) ∈ N
    rw [hx',map_mul,hnq,mul_one,show (⟨a,mem_sup_left ha⟩ : (A ⊔ N : Subgroup G)) =
      inclusion le_sup_left ⟨a,ha⟩ from rfl,happly]
    change f ⟨a,ha⟩ = 1 ↔ a*n ∈ N
    rw [← mem_ker,hk]
    exact ⟨fun h => N.mul_mem h hn',fun h => (N.mul_mem_cancel_right hn').mp h⟩
end MonoidHom
