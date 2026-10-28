module

public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.GeneralizedFitting.ComponentCenterPrimeCore
public import Theory.GroupTheory.SetStrongClosure
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Theory.GroupTheory.SylowNormalizerCentralQuotient
public import Mathlib.GroupTheory.Transfer

/-!
# Abelian strongly closed subgroups normalize components

An abelian strongly closed subgroup U of a Sylow p-subgroup normalizes
any component whose order is divisible by p. If a member a of U moves L,
its commutator with an element x of the component Sylow lies in U.
Conjugating that commutator by N_L(P) and using strong closure shows that
the resulting fusion difference lies in U intersect L. It is fixed by a,
hence central in L because distinct components commute. Burnside transfer
on L/Z(L), and then on L, forces the component Sylow to be trivial.

This preserves nontrivial intersections of components in their centers.
When the ambient prime-complement core is trivial, subnormal core
inheritance supplies the required divisibility with no classification input.

Source: the component-normalization step in Aschbacher--Smith,
Proposition 2.2.2, printed pp.519--520 (combined manuscript, 1 March 2004).
-/

public section
open Subgroup
open scoped IsMulCommutative

namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

private theorem perfect_sylow_eq_bot_of_normalizer_centralizes
    {H : Type*} [Group H] [Finite H] [Group.IsPerfect H]
    {p : ℕ} [Fact p.Prime] (P : Sylow p H)
    (hn : normalizer (P : Set H) ≤ centralizer (P : Set H)) :
    (P : Subgroup H) = ⊥ := by
  let : IsMulCommutative P := ⟨⟨fun a b =>
    Subtype.ext (hn (le_normalizer b.property) a a.property)⟩⟩
  let f := MonoidHom.transferSylow P hn
  have hb : Function.Bijective (f.domRestrict (P : Subgroup H)) :=
    (MonoidHom.transferSylow_domRestrict_eq_pow P hn).symm ▸
      (P.isPGroup'.powEquiv' P.not_dvd_index).bijective
  have hf : Function.Surjective f := fun y => by
    obtain ⟨x, hx⟩ := hb.surjective y
    exact ⟨x, hx⟩
  let : Group.IsPerfect P := Group.IsPerfect.ofSurjective hf
  apply bot_unique
  intro x hx
  exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : P) 1)

omit [Finite G] in
private theorem swapped_normalizer_difference_central
    (S U L : Subgroup G) [IsMulCommutative U]
    (hU : IsStronglyClosedSet (U : Set G) S ⊤)
    (hL : IsComponent G L) (a : G) (ha : a ∈ U)
    (hm : L.map (MulAut.conj a).toMonoidHom ≠ L)
    (P : Subgroup L) (hPS : P.map L.subtype ≤ S)
    (x : L) (hx : x ∈ P) (n : L) (hn : n ∈ normalizer (P : Set L)) :
    n⁻¹ * x⁻¹ * n * x ∈ center L := by
  let d : G := (x : G)⁻¹ * a * x * a⁻¹
  have haS : a ∈ S := hU.1 ha
  have hxS : (x : G) ∈ S := hPS (mem_map_of_mem _ hx)
  have hconjU : (x : G)⁻¹ * a * x ∈ U :=
    hU.2 a ha x (mem_top _) (mul_mem (mul_mem (inv_mem hxS) haS) hxS)
  have hdU : d ∈ U := mul_mem hconjU (inv_mem ha)
  have htC : a * (x : G) * a⁻¹ ∈ centralizer (L : Set G) :=
    (commutator_eq_bot_iff_le_centralizer.mp
      ((hL.map_conj a).commutator_eq_bot_of_ne hL hm))
      (mem_map_of_mem _ x.property)
  have hnt : (a * (x : G) * a⁻¹) * n = (n : G) * (a * x * a⁻¹) :=
    (mem_centralizer_iff.mp htC n n.property).symm
  have hdn : (n : G)⁻¹ * d * n =
      ((n : G)⁻¹ * (x : G)⁻¹ * n) * (a * x * a⁻¹) := by
    dsimp only [d]
    calc
      _ = (n : G)⁻¹ * (x : G)⁻¹ * ((a * x * a⁻¹) * n) := by group
      _ = (n : G)⁻¹ * (x : G)⁻¹ * ((n : G) * (a * x * a⁻¹)) := by rw [hnt]
      _ = _ := by group
  have hnx : n⁻¹ * x⁻¹ * n ∈ P := by
    have hh := (mem_normalizer_iff.mp (inv_mem hn) x⁻¹).mp (inv_mem hx)
    simpa only [inv_inv] using hh
  have hdnS : (n : G)⁻¹ * d * n ∈ S := by
    rw [hdn]
    exact mul_mem (hPS (mem_map_of_mem _ hnx))
      (mul_mem (mul_mem haS hxS) (inv_mem haS))
  have hdnU : (n : G)⁻¹ * d * n ∈ U := hU.2 d hdU n (mem_top _) hdnS
  have hdk : (n : G)⁻¹ * d * n * d⁻¹ =
      (n : G)⁻¹ * (x : G)⁻¹ * n * x := by
    rw [hdn]
    dsimp only [d]
    group
  let k : L := n⁻¹ * x⁻¹ * n * x
  have hkU : (k : G) ∈ U := by
    change (n : G)⁻¹ * (x : G)⁻¹ * n * x ∈ U
    rw [← hdk]
    exact mul_mem hdnU (inv_mem hdU)
  have hak : a * (k : G) * a⁻¹ = k := by
    have hc : a * (k : G) = (k : G) * a :=
      congrArg Subtype.val (mul_comm (⟨a, ha⟩ : U) ⟨k, hkU⟩)
    rw [hc, mul_inv_cancel_right]
  have hkC : (k : G) ∈ centralizer (L : Set G) := by
    have hh := (commutator_eq_bot_iff_le_centralizer.mp
      ((hL.map_conj a).commutator_eq_bot_of_ne hL hm))
      (mem_map_of_mem (MulAut.conj a).toMonoidHom k.property)
    change a * (k : G) * a⁻¹ ∈ centralizer (L : Set G) at hh
    rwa [hak] at hh
  exact mem_center_iff.mpr fun y => Subtype.ext (mem_centralizer_iff.mp hkC y y.property)

/-- Strong closure and abelianness prevent a component with nontrivial
p-part from being permuted. Components need not be centerless. -/
theorem IsComponent.normalized_by_abelian_stronglyClosed_of_dvd
    {p : ℕ} [Fact p.Prime] (S : Sylow p G) (U L : Subgroup G)
    [IsMulCommutative U] (hU : IsStronglyClosedSet (U : Set G) (S : Subgroup G) ⊤)
    (hL : IsComponent G L) (hp : p ∣ Nat.card L) :
    U ≤ normalizer (L : Set G) := by
  intro a ha
  by_contra han
  have hm : L.map (MulAut.conj a).toMonoidHom ≠ L :=
    fun he => han (mem_normalizer_iff_map_conj_eq.mpr he)
  obtain ⟨P, hP⟩ := S.exists_subgroupOf_eq_of_subnormal L hL.1
  have hPS : (P : Subgroup L).map L.subtype ≤ (S : Subgroup G) := by
    rw [hP]
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  let := hL.2
  let q := QuotientGroup.mk' (center L)
  let Q := P.mapSurjective (f := q) (QuotientGroup.mk'_surjective (center L))
  have hNQ : normalizer (Q : Set (L ⧸ center L)) ≤
      centralizer (Q : Set (L ⧸ center L)) := by
    change normalizer ((P : Subgroup L).map q : Set _) ≤
      centralizer (Q : Set (L ⧸ center L))
    rw [← P.normalizer_map_surjective q (QuotientGroup.mk'_surjective (center L))]
    rintro _ ⟨n, hn, rfl⟩ _ ⟨x, hx, rfl⟩
    have hk := swapped_normalizer_difference_central (S : Subgroup G) U L hU hL
      a ha hm (P : Subgroup L) hPS x hx n hn
    have he : q (n⁻¹ * x⁻¹ * n * x) = 1 := (QuotientGroup.eq_one_iff _).mpr hk
    have hc : Commute (q n)⁻¹ (q x)⁻¹ := by
      apply commutatorElement_eq_one_iff_commute.mp
      simpa only [map_mul, map_inv, commutatorElement_def, inv_inv] using he
    exact (Commute.inv_inv_iff.mp hc).eq.symm
  have hQ : (Q : Subgroup (L ⧸ center L)) = ⊥ :=
    perfect_sylow_eq_bot_of_normalizer_centralizes Q hNQ
  have hPZ : (P : Subgroup L) ≤ center L := by
    intro x hx
    apply (QuotientGroup.eq_one_iff _).mp
    exact mem_bot.mp (hQ ▸ (mem_map_of_mem q hx : q x ∈ (Q : Subgroup _)))
  have hNP : normalizer (P : Set L) ≤ centralizer (P : Set L) := by
    intro n _ x hx
    exact (mem_center_iff.mp (hPZ hx) n).symm
  have hPb := perfect_sylow_eq_bot_of_normalizer_centralizes P hNP
  have hcardP : Nat.card P = 1 := by
    rw [hPb, card_bot]
  have hi := (P : Subgroup L).card_mul_index
  rw [hcardP, one_mul] at hi
  exact P.not_dvd_index (hi ▸ hp)

/-- Trivial prime-complement core discharges the component divisibility
condition, so the abelian strongly closed subgroup normalizes every component. -/
theorem IsComponent.normalized_by_abelian_stronglyClosed_of_pPrimeCore_eq_bot
    {p : ℕ} [Fact p.Prime] (S : Sylow p G) (U L : Subgroup G)
    [IsMulCommutative U] (hU : IsStronglyClosedSet (U : Set G) (S : Subgroup G) ⊤)
    (hL : IsComponent G L) (hcore : pPrimeCore p G = ⊥) :
    U ≤ normalizer (L : Set G) := by
  apply hL.normalized_by_abelian_stronglyClosed_of_dvd S U L hU
  by_contra hp
  have hLc := hL.1.pPrimeCore_eq_bot hcore L
  have htop : (⊤ : Subgroup L) = ⊥ := (pPrimeCore_eq_bot_iff.mp hLc) ⊤ inferInstance
    (by simpa only [Nat.card_congr Subgroup.topEquiv.toEquiv] using
      (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hp)
  let := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  exact top_ne_bot htop

end Theory.GroupTheory
