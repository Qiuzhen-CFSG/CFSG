module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.Group
public import Theory.GroupTheory.RelativeComplementProjection
public import Theory.GroupTheory.DisjointCommutingProduct


/-!
# Splitting a centralizer by averaging over Sylow cosets

A cocycle in an abelian group of exponent two which vanishes on a Sylow
2-subgroup is a coboundary: multiply its values over the odd number of cosets.
For conjugation this gives a fixed representative in each coset Vd. If D fixes
V and the Sylow, and C_V(P) lies in D, that representative lies in D itself.
If C_V(A)=1, the result is a literal relative complement and a multiplication
isomorphism V × C_D(A) ≃ DV.

This proves directly the splitting consequence used after the Gaschütz citation
in Aschbacher--Smith, combined manuscript of 1 March 2004, 14.4.7, p.1009.
It does not assume Gaschütz's theorem or a source-specific splitting certificate.
The coset product is the multiplicative counterpart of the averaging argument in
Theory.Representation.BinarySylowFixedSpace.fixed_lift_mod_trivial_quotient.
-/

public section
namespace Subgroup

/-- Averaging over the odd number of Sylow cosets trivializes a binary cocycle. -/
theorem binary_cocycle_trivial_of_sylow {A E : Type*} [Group A] [Finite A] [CommGroup E]
    (ρ : A →* MulAut E) (c : A → E)
    (hc : ∀ a b, c (a * b) = c a * ρ a (c b))
    (he : ∀ e : E, e ^ 2 = 1) (P : Sylow 2 A)
    (hP : ∀ a ∈ P, c a = 1) :
    ∃ v : E, ∀ a, ρ a v * c a = v := by
  classical
  let _ := Fintype.ofFinite (A ⧸ (P : Subgroup A))
  let f : A ⧸ (P : Subgroup A) → E := Quotient.lift c (by
    intro a b hab
    have hp : a⁻¹ * b ∈ P := QuotientGroup.leftRel_apply.mp hab
    have h := hc a (a⁻¹ * b)
    simpa only [mul_inv_cancel_left, hP _ hp, map_one, mul_one] using h.symm)
  have hf (a : A) (q : A ⧸ (P : Subgroup A)) :
      f (a • q) = c a * ρ a (f q) := by
    induction q using Quotient.inductionOn with
    | h b => exact hc a b
  let v : E := ∏ q, f q
  refine ⟨v, fun a => ?_⟩
  have hv : v = c a ^ Fintype.card (A ⧸ (P : Subgroup A)) * ρ a v := by
    calc
      v = ∏ q, f (a • q) := (Equiv.prod_comp (MulAction.toPerm a) f).symm
      _ = _ := by simp only [hf, Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, map_prod, v]
  have hn : Odd (Fintype.card (A ⧸ (P : Subgroup A))) := by
    have h := P.not_dvd_index
    rw [Subgroup.index, Nat.card_eq_fintype_card] at h
    exact Nat.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using h)
  obtain ⟨k, hk⟩ := hn
  have hp : c a ^ Fintype.card (A ⧸ (P : Subgroup A)) = c a := by
    rw [hk, pow_add, pow_mul, he, one_pow, pow_one, one_mul]
  rw [hp, mul_comm] at hv
  exact hv.symm

open scoped IsMulCommutative commutatorElement

/-- A Sylow-fixed element whose displacement lies in a binary abelian layer
has a globally fixed representative in its actual coset. -/
theorem fixed_coset_of_sylow {G : Type*} [Group G]
    (A V : Subgroup G) [Finite A] [IsMulCommutative V]
    (hAV : A ≤ normalizer (V : Set G)) (he : ∀ v ∈ V, v ^ 2 = 1)
    (P : Sylow 2 A) (d : G)
    (hd : ∀ a ∈ A, ⁅a, d⁆ ∈ V)
    (hP : ∀ a : A, a ∈ P → Commute (a : G) d) :
    ∃ v ∈ V, v * d ∈ centralizer (A : Set G) := by
  let ρ : A →* MulAut V := V.normalizerMonoidHom.comp (inclusion hAV)
  let c : A → V := fun a => ⟨⁅(a : G), d⁆, hd a a.property⟩
  have hc (a b : A) : c (a * b) = c a * ρ a (c b) := by
    apply Subtype.ext
    have hcV := mul_comm (c a) (ρ a (c b))
    rw [hcV]
    change (a : G) * b * d * ((a : G) * b)⁻¹ * d⁻¹ =
      ((a : G) * ((b : G) * d * (b : G)⁻¹ * d⁻¹) * (a : G)⁻¹) *
        ((a : G) * d * (a : G)⁻¹ * d⁻¹)
    group
  have heV (v : V) : v ^ 2 = 1 := Subtype.ext (he v v.property)
  have hcP (a : A) (ha : a ∈ P) : c a = 1 := by
    apply Subtype.ext
    exact (commutatorElement_eq_one_iff_mul_comm).mpr (hP a ha).eq
  obtain ⟨v, hv⟩ := binary_cocycle_trivial_of_sylow ρ c hc heV P hcP
  refine ⟨v, v.property, mem_centralizer_iff.mpr ?_⟩
  intro a ha
  have h := congrArg Subtype.val (hv ⟨a, ha⟩)
  change (a * (v : G) * a⁻¹) * (a * d * a⁻¹ * d⁻¹) = (v : G) at h
  have hh : a * ((v : G) * d) * a⁻¹ = (v : G) * d := by
    calc
      _ = ((a * (v : G) * a⁻¹) * (a * d * a⁻¹ * d⁻¹)) * d := by group
      _ = _ := by rw [h]
  exact (mul_inv_eq_iff_eq_mul.mp hh)

/-- The fixed representatives lie in D when the Sylow fixed subgroup of V
lies in D. Vanishing global fixed points gives a literal relative complement. -/
theorem centralizer_complement_of_sylow {G : Type*} [Group G]
    (A V D : Subgroup G) [Finite A] [IsMulCommutative V]
    (hAV : A ≤ normalizer (V : Set G)) (he : ∀ v ∈ V, v ^ 2 = 1)
    (P : Sylow 2 A)
    (hcomm : ⁅A, D⁆ ≤ V)
    (hDP : D ≤ centralizer ((P : Subgroup A).map A.subtype : Set G))
    (hfix : V ⊓ centralizer ((P : Subgroup A).map A.subtype : Set G) ≤ D)
    (hVA : V ⊓ centralizer (A : Set G) = ⊥)
    (hDV : D ≤ centralizer (V : Set G)) :
    D = (D ⊓ V) ⊔ (D ⊓ centralizer (A : Set G)) ∧
    Disjoint V (D ⊓ centralizer (A : Set G)) ∧
    ((D ⊓ centralizer (A : Set G)).subgroupOf D).IsComplement'
      ((D ⊓ V).subgroupOf D) := by
  have hgen : D = (D ⊓ V) ⊔ (D ⊓ centralizer (A : Set G)) := by
    apply le_antisymm ?_ (sup_le inf_le_left inf_le_left)
    intro d hd
    obtain ⟨v, hv, hvc⟩ := fixed_coset_of_sylow A V hAV he P d
      (fun a ha => commutator_le.mp hcomm a ha d hd)
      (fun a ha => hDP hd a (mem_map_of_mem A.subtype ha))
    have hdc := hDP hd
    have hvPc : v * d ∈ centralizer ((P : Subgroup A).map A.subtype : Set G) :=
      centralizer_le ((map_le_range A.subtype (P : Subgroup A)).trans_eq A.range_subtype) hvc
    have hvP : v ∈ centralizer ((P : Subgroup A).map A.subtype : Set G) := by
      have hh := (centralizer ((P : Subgroup A).map A.subtype : Set G)).mul_mem hvPc
        ((centralizer _).inv_mem hdc)
      simpa only [mul_inv_cancel_right] using hh
    have hvD := hfix ⟨hv, hvP⟩
    have hm := mul_mem_sup
      (show v⁻¹ ∈ D ⊓ V from ⟨D.inv_mem hvD, V.inv_mem hv⟩)
      (show v * d ∈ D ⊓ centralizer (A : Set G) from ⟨D.mul_mem hvD hd, hvc⟩)
    simpa only [inv_mul_cancel_left] using hm
  have hdis : Disjoint V (D ⊓ centralizer (A : Set G)) := by
    apply disjoint_def.mpr
    intro x hx hxc
    exact (show x ∈ (⊥ : Subgroup G) from hVA ▸ ⟨hx, hxc.2⟩)
  have hn : D ≤ normalizer ((D ⊓ V : Subgroup G) : Set G) := by
    apply le_normalizer_iff.mpr
    intro d hd x hx
    refine ⟨D.mul_mem (D.mul_mem hd hx.1) (D.inv_mem hd), ?_⟩
    have hh := hDV hd x hx.2
    have heq : d * x * d⁻¹ = x := by
      rw [← hh, mul_inv_cancel_right]
    exact heq.symm ▸ hx.2
  have : ((D ⊓ V).subgroupOf D).Normal :=
    (normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hn
  exact ⟨hgen, hdis, relative_isComplement inf_le_left inf_le_left hgen.symm
    (hdis.mono_left inf_le_right)⟩

/-- The decomposition retains the multiplication map of the two actual factors. -/
theorem centralizer_directProduct_of_sylow {G : Type*} [Group G]
    (A V D : Subgroup G) [Finite A] [IsMulCommutative V]
    (hAV : A ≤ normalizer (V : Set G)) (he : ∀ v ∈ V, v ^ 2 = 1)
    (P : Sylow 2 A)
    (hcomm : ⁅A, D⁆ ≤ V)
    (hDP : D ≤ centralizer ((P : Subgroup A).map A.subtype : Set G))
    (hfix : V ⊓ centralizer ((P : Subgroup A).map A.subtype : Set G) ≤ D)
    (hVA : V ⊓ centralizer (A : Set G) = ⊥)
    (hDV : D ≤ centralizer (V : Set G)) :
    ∃ e : V × ↥(D ⊓ centralizer (A : Set G)) ≃* ↥(D ⊔ V),
      ∀ v c, (e (v, c) : G) = (v : G) * (c : G) := by
  obtain ⟨hgen, hdis, _⟩ := centralizer_complement_of_sylow A V D hAV he P
    hcomm hDP hfix hVA hDV
  have heq : V ⊔ (D ⊓ centralizer (A : Set G)) = D ⊔ V := by
    apply le_antisymm (sup_le le_sup_right (inf_le_left.trans le_sup_left))
    refine sup_le ?_ le_sup_left
    conv_lhs => rw [hgen]
    exact sup_le (inf_le_right.trans le_sup_left) le_sup_right
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting V
    (D ⊓ centralizer (A : Set G)) hdis
    (le_centralizer_iff.mp (inf_le_left.trans hDV))
  exact ⟨e.trans (MulEquiv.subgroupCongr heq), he⟩

end Subgroup
