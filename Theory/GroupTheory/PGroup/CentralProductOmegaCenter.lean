module

public import Theory.GroupTheory.PGroup.CentralProductCore
public import Theory.GroupTheory.PGroup.OmegaImage
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# A noncyclic center of omega in a commuting product

Suppose `G = EM` is a commuting product, the intersection has exponent dividing
two, `Ω₂(M)` is abelian, and `Ω₁(M)` is noncyclic. Then the center of `Ω₁(G)`
is a noncyclic characteristic abelian subgroup of `G`.

For an involution `em`, commutation gives `e² = m⁻²`. Thus `m²` lies in the
intersection and `m⁴ = 1`. Every element of `Ω₁(M)` commutes with `e` and
with `m ∈ Ω₂(M)`, hence with every generator of `Ω₁(G)`. Consequently
`Ω₁(M)` embeds in its center.

This is the final omega argument in Gorenstein, *Finite Groups*, Section 5.4,
Theorem 4.9. The hypotheses separate this general argument from the modular
presentation calculation.
-/

open Subgroup
open scoped IsMulCommutative

/-- An abelian second omega in a commuting factor makes its first omega
central in the first omega of the whole product. -/
public theorem Subgroup.omega_one_map_le_center_omega_one_of_commuting_product
    {G : Type*} [Group G] (E M : Subgroup G)
    (hgen : E ⊔ M = ⊤) (hc : M ≤ centralizer (E : Set G))
    (hinter : ∀ x ∈ E ⊓ M, x ^ 2 = 1)
    [IsMulCommutative (omega M (p := 2) 2)] :
    (omega₁ M (p := 2)).map M.subtype ≤
      (center (omega₁ G (p := 2))).map (omega₁ G (p := 2)).subtype := by
  let O := omega₁ G (p := 2)
  let U := (omega₁ M (p := 2)).map M.subtype
  have hUO : U ≤ O := by
    apply map_le_iff_le_comap.mpr
    change closure {x : M | x ^ (2 ^ 1) = 1} ≤ O.comap M.subtype
    apply (closure_le _).mpr
    intro x hx
    apply subset_closure
    exact congrArg M.subtype hx
  have h12 : omega₁ M (p := 2) ≤ omega M (p := 2) 2 := by
    apply (closure_le _).mpr
    intro x hx
    apply subset_closure
    have hx2 : x ^ 2 = 1 := by simpa using hx
    change x ^ 4 = 1
    rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, hx2, one_pow]
  let : M.Normal := normal_of_centralizing_sup_eq_top M E
    (sup_comm E M ▸ hgen) (le_centralizer_iff.mp hc)
  have hUC : U ≤ centralizer (O : Set G) := by
    rintro u ⟨v, hv, rfl⟩
    change (v : G) ∈ centralizer (closure {x : G | x ^ (2 ^ 1) = 1} : Set G)
    rw [centralizer_closure]
    intro x hx
    have hx2 : x ^ 2 = 1 := by simpa using hx
    obtain ⟨e, he, m, hm, rfl⟩ := mem_sup_of_normal_right.mp
      (show x ∈ E ⊔ M by rw [hgen]; trivial)
    have hem : Commute e m := hc hm e he
    have hem2 : e ^ 2 * m ^ 2 = 1 := by rw [← hem.mul_pow, hx2]
    have hm2E : m ^ 2 ∈ E := by
      rw [eq_inv_of_mul_eq_one_right hem2]
      exact E.inv_mem (E.pow_mem he 2)
    have hm4 : m ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul]
      exact hinter (m ^ 2) ⟨hm2E, M.pow_mem hm 2⟩
    have hmW : (⟨m, hm⟩ : M) ∈ omega M (p := 2) 2 := by
      apply subset_closure
      apply Subtype.ext
      exact hm4
    have hmv : m * (v : G) = (v : G) * m := by
      exact congrArg (fun t : M => (t : G))
        ((omega M (p := 2) 2).le_centralizer (h12 hv) ⟨m, hm⟩ hmW)
    have hev : e * (v : G) = (v : G) * e := hc v.property e he
    calc
      (e * m) * (v : G) = e * ((v : G) * m) := by rw [mul_assoc, hmv]
      _ = (v : G) * (e * m) := by rw [← mul_assoc, hev, mul_assoc]
  intro u hu
  refine ⟨⟨u, hUO hu⟩, ?_, rfl⟩
  apply mem_center_iff.mpr
  intro x
  exact Subtype.ext (hUC hu x x.property)

/-- The center of first omega is the required characteristic abelian
obstruction whenever the modular factor's first omega is noncyclic. -/
public theorem Subgroup.exists_noncyclic_characteristic_abelian_of_commuting_product_omega
    {G : Type*} [Group G] (E M : Subgroup G)
    (hgen : E ⊔ M = ⊤) (hc : M ≤ centralizer (E : Set G))
    (hinter : ∀ x ∈ E ⊓ M, x ^ 2 = 1)
    [IsMulCommutative (omega M (p := 2) 2)]
    (hncyc : ¬ IsCyclic (omega₁ M (p := 2))) :
    ∃ A : Subgroup G, A.Characteristic ∧ IsMulCommutative A ∧ ¬ IsCyclic A := by
  let O := omega₁ G (p := 2)
  let A := (center O).map O.subtype
  let : O.Characteristic := omega₁_characteristic G
  have hle : (omega₁ M (p := 2)).map M.subtype ≤ A :=
    omega_one_map_le_center_omega_one_of_commuting_product E M hgen hc hinter
  refine ⟨A, inferInstance, inferInstance, ?_⟩
  intro hA
  let : IsCyclic A := hA
  let j : omega₁ M (p := 2) →* A := {
    toFun := fun x => ⟨(x : M), hle (mem_map_of_mem M.subtype x.property)⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  apply hncyc
  apply isCyclic_of_injective j
  intro x y h
  exact Subtype.ext (Subtype.ext (congrArg (fun z : A => (z : G)) h))

/-- A characteristic subgroup's noncyclic characteristic abelian subgroup
remains such a subgroup in the original ambient group. -/
public theorem Subgroup.exists_noncyclic_characteristic_abelian_of_characteristic
    {G : Type*} [Group G] (K : Subgroup G) [K.Characteristic]
    (h : ∃ A : Subgroup K,
      A.Characteristic ∧ IsMulCommutative A ∧ ¬ IsCyclic A) :
    ∃ A : Subgroup G, A.Characteristic ∧ IsMulCommutative A ∧ ¬ IsCyclic A := by
  obtain ⟨A, hchar, hcomm, hncyc⟩ := h
  let : A.Characteristic := hchar
  let : IsMulCommutative A := hcomm
  refine ⟨A.map K.subtype, inferInstance, inferInstance, ?_⟩
  intro hcyc
  exact hncyc ((A.equivMapOfInjective K.subtype K.subtype_injective).isCyclic.mpr hcyc)

/-- It suffices that the commuting product is characteristic in the ambient
group; neither factor is required to be characteristic. -/
public theorem Subgroup.exists_noncyclic_characteristic_abelian_of_characteristic_product_omega
    {G : Type*} [Group G] (E M : Subgroup G)
    [(E ⊔ M).Characteristic]
    (hc : M ≤ centralizer (E : Set G))
    (hinter : ∀ x ∈ E ⊓ M, x ^ 2 = 1)
    [IsMulCommutative (omega M (p := 2) 2)]
    (hncyc : ¬ IsCyclic (omega₁ M (p := 2))) :
    ∃ A : Subgroup G, A.Characteristic ∧ IsMulCommutative A ∧ ¬ IsCyclic A := by
  let K := E ⊔ M
  let E' := E.subgroupOf K
  let M' := M.subgroupOf K
  let e : M' ≃* M := subgroupOfEquivOfLe le_sup_right
  have hgen : E' ⊔ M' = ⊤ := by
    apply (map_injective K.subtype_injective)
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left,
      map_subgroupOf_eq_of_le le_sup_right]
    rw [← MonoidHom.range_eq_map, range_subtype]
  have hc' : M' ≤ centralizer (E' : Set K) := by
    intro m hm x hx
    exact Subtype.ext (hc hm x hx)
  have hinter' : ∀ x ∈ E' ⊓ M', x ^ 2 = 1 := by
    intro x hx
    exact Subtype.ext (hinter x hx)
  let e2 := e.omega 2 2
  let : IsMulCommutative (omega M' (p := 2) 2) := by
    apply IsMulCommutative.of_comm
    intro x y
    apply e2.injective
    simp only [map_mul]
    exact mul_comm _ _
  have hncyc' : ¬ IsCyclic (omega₁ M' (p := 2)) := by
    intro h
    exact hncyc ((e.omega 2 1).isCyclic.mp h)
  apply exists_noncyclic_characteristic_abelian_of_characteristic K
  exact exists_noncyclic_characteristic_abelian_of_commuting_product_omega
    E' M' hgen hc' hinter' hncyc'
