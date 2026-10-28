module

public import Theory.GroupTheory.RelativeComplementProjection
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Equivariant projections in normal products

For disjoint normal subgroups L and X, the canonical projection LX → X
commutes with ambient conjugation. If G = LM, its restriction to M ∩ LX
is surjective. A p-subgroup normalized by M therefore centralizes X when
X is a q-group and p and q are coprime: its intersection with LX has trivial
projection, and hence all its commutators with X vanish.

Only the actual subgroup inclusions and relative kernel L inside LX enter
the construction. The Dedekind intersection identity is also recorded for
normal products whose second factor need not be normal.

Source: the projection argument in Aschbacher–Smith, *The Classification of
Quasithin Groups*, Lemma A.1.10, printed p.21 (PDF p.32).
-/

public section

open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G] (L X : Subgroup G) [L.Normal]

/-- Projection onto the complementary normal factor inside its actual product. -/
noncomputable abbrev normalProductProjection (hd : Disjoint L X) :
    (L ⊔ X : Subgroup G) →* X :=
  relativeComplementProjection le_sup_left le_sup_right rfl hd

/-- The projection is the identity on the retained factor. -/
theorem normalProductProjection_inclusion (hd : Disjoint L X) (x : X) :
    normalProductProjection L X hd (inclusion le_sup_right x) = x :=
  relativeComplementProjection_inclusion le_sup_left le_sup_right rfl hd x

/-- Its kernel is exactly the discarded factor, as a subgroup of the product. -/
theorem normalProductProjection_ker (hd : Disjoint L X) :
    (normalProductProjection L X hd).ker = L.subgroupOf (L ⊔ X) :=
  relativeComplementProjection_ker le_sup_left le_sup_right rfl hd

/-- Every element differs from its projection by an element of the kernel. -/
theorem normalProductProjection_error (hd : Disjoint L X) (g : (L ⊔ X : Subgroup G)) :
    (g : G) * (normalProductProjection L X hd g : G)⁻¹ ∈ L := by
  let c : (L ⊔ X : Subgroup G) := inclusion le_sup_right (normalProductProjection L X hd g)
  have hc : normalProductProjection L X hd c = normalProductProjection L X hd g :=
    normalProductProjection_inclusion L X hd _
  have hk : g * c⁻¹ ∈ (normalProductProjection L X hd).ker := by
    change normalProductProjection L X hd (g * c⁻¹) = 1
    rw [map_mul, map_inv, hc, mul_inv_cancel]
  rw [normalProductProjection_ker] at hk
  exact hk

/-- Normality of both factors makes the projection equivariant for ambient conjugation. -/
theorem normalProductProjection_conj [X.Normal] (hd : Disjoint L X)
    (a : G) (g : (L ⊔ X : Subgroup G)) :
    normalProductProjection L X hd
      ⟨a * g * a⁻¹, (inferInstance : (L ⊔ X).Normal).conj_mem _ g.property a⟩ =
      ⟨a * (normalProductProjection L X hd g : G) * a⁻¹,
        (inferInstance : X.Normal).conj_mem _ (normalProductProjection L X hd g).property a⟩ := by
  let g' : (L ⊔ X : Subgroup G) :=
    ⟨a * g * a⁻¹, (inferInstance : (L ⊔ X).Normal).conj_mem _ g.property a⟩
  let x' : X := ⟨a * (normalProductProjection L X hd g : G) * a⁻¹,
    (inferInstance : X.Normal).conj_mem _ (normalProductProjection L X hd g).property a⟩
  have he : (g' : G) * (x' : G)⁻¹ ∈ L := by
    have hh := (inferInstance : L.Normal).conj_mem _
      (normalProductProjection_error L X hd g) a
    simpa only [g', x', mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left] using hh
  have hk : g' * (inclusion le_sup_right x')⁻¹ ∈ (normalProductProjection L X hd).ker := by
    rw [normalProductProjection_ker]
    exact he
  change normalProductProjection L X hd (g' * (inclusion le_sup_right x')⁻¹) = 1 at hk
  rw [map_mul, map_inv, normalProductProjection_inclusion] at hk
  exact mul_inv_eq_one.mp hk

/-- If G = LM, restriction to M ∩ LX still surjects onto X. -/
theorem normalProductProjection_restrict_surjective (M : Subgroup G)
    (hd : Disjoint L X) (hgen : L ⊔ M = ⊤) :
    Function.Surjective ((normalProductProjection L X hd).comp
      (inclusion (show M ⊓ (L ⊔ X) ≤ L ⊔ X from inf_le_right))) := by
  intro x
  obtain ⟨l, hl, m, hm, he⟩ := mem_sup_of_normal_left.mp
    (show (x : G) ∈ L ⊔ M by rw [hgen]; trivial)
  have hmH : m ∈ L ⊔ X := by
    have hh := (L ⊔ X).mul_mem ((L ⊔ X).inv_mem (mem_sup_left hl))
      (mem_sup_right x.property)
    rw [← he] at hh
    simpa only [inv_mul_cancel_left] using hh
  refine ⟨⟨m, hm, hmH⟩, ?_⟩
  let l' : (L ⊔ X : Subgroup G) := ⟨l, mem_sup_left hl⟩
  let m' : (L ⊔ X : Subgroup G) := ⟨m, hmH⟩
  have hlπ : normalProductProjection L X hd l' = 1 := by
    change l' ∈ (normalProductProjection L X hd).ker
    rw [normalProductProjection_ker]
    exact hl
  have hprod : l' * m' = inclusion le_sup_right x := Subtype.ext he
  have hh := congrArg (normalProductProjection L X hd) hprod
  rw [map_mul, hlπ, one_mul, normalProductProjection_inclusion] at hh
  exact hh

/-- The actual projection carries displacement by an ambient element to displacement in X. -/
theorem normalProductProjection_commutator [X.Normal] (hd : Disjoint L X)
    (a : G) (y : (L ⊔ X : Subgroup G)) :
    (normalProductProjection L X hd
      ⟨⁅a, (y : G)⁆, (L ⊔ X).mul_mem
        ((inferInstance : (L ⊔ X).Normal).conj_mem _ y.property a)
        ((L ⊔ X).inv_mem y.property)⟩ : G) =
      ⁅a, (normalProductProjection L X hd y : G)⁆ := by
  let ay : (L ⊔ X : Subgroup G) :=
    ⟨a * y * a⁻¹, (inferInstance : (L ⊔ X).Normal).conj_mem _ y.property a⟩
  change (normalProductProjection L X hd (ay * y⁻¹) : G) = _
  rw [map_mul, map_inv]
  have hh := normalProductProjection_conj L X hd a y
  change normalProductProjection L X hd ay = _ at hh
  rw [hh]
  rfl
end Subgroup

namespace Subgroup
variable {G : Type*} [Group G]

/-- The Dedekind intersection identity inside a normal product G = LM. -/
theorem normal_product_intersection (L M X : Subgroup G) [L.Normal]
    (hgen : L ⊔ M = ⊤) : L ⊔ (M ⊓ (L ⊔ X)) = L ⊔ X := by
  apply le_antisymm (sup_le le_sup_left inf_le_right)
  intro x hx
  obtain ⟨l, hl, m, hm, rfl⟩ := mem_sup_of_normal_left.mp
    (show x ∈ L ⊔ M by rw [hgen]; trivial)
  have hmLX : m ∈ L ⊔ X := by
    have := (L ⊔ X).mul_mem ((L ⊔ X).inv_mem (mem_sup_left hl)) hx
    simpa only [inv_mul_cancel_left] using this
  exact mul_mem (mem_sup_left hl) (mem_sup_right ⟨hm, hmLX⟩)

/-- In G = LM, a p-subgroup normalized by M centralizes a disjoint normal q-factor X
when p and q are coprime. The projection of its intersection with LX is both a
p-group and a q-group, so equivariance and surjectivity kill all displacement. -/
theorem centralizes_coprime_normal_factor_of_product
    {p q : ℕ} (L M X P : Subgroup G) [L.Normal] [X.Normal]
    (hgen : L ⊔ M = ⊤) (hd : Disjoint L X)
    (hP : IsPGroup p P) (hX : IsPGroup q X) (hpq : Nat.Coprime p q)
    (hn : M ≤ normalizer (P : Set G)) : P ≤ centralizer (X : Set G) := by
  let H := L ⊔ X
  let π := normalProductProjection L X hd
  let D := P.subgroupOf H
  have hDb : D.map π = ⊥ := by
    have hDp : IsPGroup p D := hP.comap_subtype
    have hh := (hDp.map π).disjoint_of_coprime
      (hX.to_subgroup (D.map π)) hpq
    simpa only [inf_idem] using hh.eq_bot
  intro a ha
  apply mem_centralizer_iff.mpr
  intro x hx
  obtain ⟨y, hy⟩ := normalProductProjection_restrict_surjective L X M hd hgen ⟨x, hx⟩
  let yH : H := inclusion inf_le_right y
  have hyπ : π yH = (⟨x, hx⟩ : X) := hy
  have hcP : ⁅a, (y : G)⁆ ∈ P :=
    (le_normalizer_iff_commutator_le_left.mp hn)
      (commutator_mem_commutator ha y.property.1)
  have hcH : ⁅a, (y : G)⁆ ∈ H := H.mul_mem
    ((inferInstance : H.Normal).conj_mem _ y.property.2 a) (H.inv_mem y.property.2)
  have hcπ : π ⟨⁅a, (y : G)⁆, hcH⟩ = 1 := by
    have hh : π ⟨⁅a, (y : G)⁆, hcH⟩ ∈ D.map π := mem_map_of_mem π hcP
    rwa [hDb, mem_bot] at hh
  have hh := normalProductProjection_commutator L X hd a yH
  change (π ⟨⁅a, (y : G)⁆, hcH⟩ : G) = ⁅a, (π yH : G)⁆ at hh
  rw [hcπ, hyπ] at hh
  exact (commutatorElement_eq_one_iff_mul_comm.mp hh.symm).symm
end Subgroup
