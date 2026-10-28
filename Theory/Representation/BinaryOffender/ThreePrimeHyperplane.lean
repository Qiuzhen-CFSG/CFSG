module

public import Theory.Representation.BinaryOffender.OddOrderSmallCodimension
public import Theory.GroupTheory.Involution.OddRotation
public import Theory.Representation.NormalElementaryQuotient
public import Theory.ElementaryAbelian.Injective

/-!
# Hyperplane involutions in binary representations of 3-prime groups

In a faithful binary action of a finite 3-prime group, an involution fixing a
hyperplane lies in the two-core. Otherwise Baer–Suzuki supplies an inverted
odd-prime element; its commutator with the involution has displacement at most
two, forcing that odd prime to be three.

Applied to the faithful quotient action on a normal elementary subgroup V,
this puts an elementary actor A in I whenever A fixes a hyperplane in V,
C(V) lies in I, and the quotient by I has trivial two-core. The relative
version preserves the literal inclusions into an ambient subgroup N.

Source: GLS, Number 2, G.26.18(a), final binary representation obstruction,
printed pp.152–153; the proof here uses the proved odd-rotation and
small-displacement theorems.
-/

public section
open Subgroup
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem involution_mem_twoCore_of_three_prime_displacement
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (h3 : Nat.Coprime 3 (Nat.card G)) (t : G) (ht : t ^ 2 = 1)
    (hd : fixedCodim ρ (zpowers t) ≤ 1) : t ∈ pCore 2 G := by
  by_contra hn
  have ht1 : t ≠ 1 := fun he => hn (he ▸ one_mem _)
  have hti : BenderSuzuki.PFAppendixIII.IsInvolution t := ⟨ht1,ht⟩
  obtain ⟨p,hp,hp2,r,hr,hi⟩ :=
    BenderSuzuki.involution_outside_twoCore_inverts_odd_prime t hti hn
  have hodd : Odd (orderOf r) := hr ▸ (hp.odd_of_ne_two hp2)
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using ht)
  have hc : t * r * t⁻¹ * r⁻¹ = (r ^ 2)⁻¹ := by
    change t⁻¹ * r * t = r⁻¹ at hi
    rw [htinv] at hi ⊢
    rw [hi]
    group
  have horder : orderOf (t * r * t⁻¹ * r⁻¹) = p := by
    rw [hc,orderOf_inv,hodd.coprime_two_right.orderOf_pow,hr]
  have hsmall : fixedCodim ρ (zpowers (t * r * t⁻¹ * r⁻¹)) ≤ 2 :=
    (fixedCodim_commutator_le_twice ρ t r).trans (by omega)
  have hdiv := orderOf_dvd_three_of_odd_fixedCodim_le_two ρ hf
    (t * r * t⁻¹ * r⁻¹) (horder ▸ hp.odd_of_ne_two hp2) hsmall
  rw [horder] at hdiv
  have hp3 : p = 3 := (Nat.dvd_prime Nat.prime_three).mp hdiv |>.resolve_left hp.ne_one
  exact (Nat.prime_three.coprime_iff_not_dvd.mp h3)
    (hp3 ▸ hr ▸ orderOf_dvd_natCard r)
end Representation.BinaryOffender

namespace Representation.NormalElementaryQuotient
open scoped IsMulCommutative
open Subgroup BinaryOffender
variable {G : Type*} [Group G] [Finite G]

theorem elementary_le_of_three_prime_hyperplane
    (V I A : Subgroup G) [V.Normal] [I.Normal] [IsElementaryAbelian 2 V]
    [IsElementaryAbelian 2 A] (h3 : Nat.Coprime 3 (Nat.card G))
    (hCI : centralizer (V : Set G) ≤ I) (hcore : pCore 2 (G ⧸ I) = ⊥)
    (hi : (centralizer (A : Set G)).relIndex V ≤ 2) : A ≤ I := by
  let C := centralizer (V : Set G)
  let q := QuotientGroup.mk' C
  let ρ := representation V q (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  have hf : Function.Injective ρ := representation_injective V q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  have h3q : Nat.Coprime 3 (Nat.card (G ⧸ C)) :=
    h3.of_dvd_right (card_quotient_dvd_card C)
  have hd : fixedCodim ρ (A.map q) ≤ 1 := by
    have hc := relIndex_mul_relIndex (⊥ : Subgroup G) (V ⊓ centralizer (A : Set G)) V
      bot_le inf_le_left
    simp only [relIndex_bot_left,inf_relIndex_left] at hc
    have hcard : Nat.card V ≤ Nat.card (V ⊓ centralizer (A : Set G) : Subgroup G) * 2 := by
      rw [←hc]
      exact Nat.mul_le_mul_left _ hi
    rw [←Nat.card_congr (fixedSpaceEquiv V q (QuotientGroup.mk'_surjective C)
      (QuotientGroup.ker_mk' C) A)] at hcard
    change Nat.card (Additive V) ≤ _ at hcard
    have hV := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    have hF := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace ρ (A.map q))
    rw [Nat.card_zmod] at hV hF
    rw [hV,hF,←pow_succ] at hcard
    have hp := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hcard
    have he := fixedCodim_add_finrank ρ (A.map q)
    omega
  let f : (G ⧸ C) →* (G ⧸ I) := QuotientGroup.map C I (MonoidHom.id G) hCI
  have hfs : Function.Surjective f := by
    intro z
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective I z
    exact ⟨q g,rfl⟩
  have hm : (pCore 2 (G ⧸ C)).map f ≤ pCore 2 (G ⧸ I) :=
    le_sSup ⟨Normal.map inferInstance f hfs,pCore_isPGroup.map f⟩
  intro a ha
  have hda : fixedCodim ρ (zpowers (q a)) ≤ 1 := by
    have hfix : fixedSpace ρ (A.map q) ≤ fixedSpace ρ (zpowers (q a)) := by
      intro v hv b
      exact hv ⟨b,(zpowers_le.mpr (mem_map_of_mem q ha)) b.property⟩
    have hh := Submodule.finrank_mono hfix
    have h₁ := fixedCodim_add_finrank ρ (zpowers (q a))
    have h₂ := fixedCodim_add_finrank ρ (A.map q)
    omega
  have hqa : q a ∈ pCore 2 (G ⧸ C) :=
    involution_mem_twoCore_of_three_prime_displacement ρ hf h3q (q a)
      (by rw [←map_pow,elemPow_eq_one_of_isElementaryAbelian a ha,map_one]) hda
  have hh := hm (mem_map_of_mem f hqa)
  rw [hcore,mem_bot] at hh
  exact (QuotientGroup.eq_one_iff a).mp hh
end Representation.NormalElementaryQuotient

namespace Representation.NormalElementaryQuotient
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The hyperplane obstruction inside a literal ambient subgroup. -/
theorem elementary_le_of_relative_three_prime_hyperplane
    (N V I A : Subgroup G) [(I.subgroupOf N).Normal]
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 A]
    (hVN : V ≤ N) (hAN : A ≤ N) (hNV : N ≤ normalizer (V : Set G))
    (h3 : Nat.Coprime 3 (Nat.card N))
    (hCI : N ⊓ centralizer (V : Set G) ≤ I)
    (hcore : pCore 2 (N ⧸ I.subgroupOf N) = ⊥)
    (hi : (centralizer (A : Set G)).relIndex V ≤ 2) : A ≤ I := by
  let V' := V.subgroupOf N
  let A' := A.subgroupOf N
  let : V'.Normal := normal_subgroupOf_of_le_normalizer hNV
  let : IsElementaryAbelian 2 V' := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe hVN).toMonoidHom (subgroupOfEquivOfLe hVN).injective
  let : IsElementaryAbelian 2 A' := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe hAN).toMonoidHom (subgroupOfEquivOfLe hAN).injective
  have hC : centralizer (V' : Set N) ≤ I.subgroupOf N := by
    intro n hn
    apply hCI
    refine ⟨n.property,?_⟩
    intro v hv
    exact congrArg Subtype.val (hn ⟨v,hVN hv⟩ hv)
  have he : centralizer (A' : Set N) = (centralizer (A : Set G)).subgroupOf N := by
    ext n
    constructor
    · intro hn a ha
      exact congrArg Subtype.val (hn ⟨a,hAN ha⟩ ha)
    · intro hn a ha
      exact Subtype.ext (hn a ha)
  have hi' : (centralizer (A' : Set N)).relIndex V' ≤ 2 := by
    rw [he,relIndex_subgroupOf hVN]
    exact hi
  have hh := elementary_le_of_three_prime_hyperplane V' (I.subgroupOf N) A'
    h3 hC hcore hi'
  intro a ha
  exact hh (show (⟨a,hAN ha⟩ : N) ∈ A' from ha)
end Representation.NormalElementaryQuotient
