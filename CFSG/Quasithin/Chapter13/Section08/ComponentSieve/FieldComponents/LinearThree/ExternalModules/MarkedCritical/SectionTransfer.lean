module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.Models
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.FixedSpace

/-!
# Lifting the marked critical centralizer to a chief section

The equality case of the fixed-codimension inequality lifts every fixed vector
from a chief section. The second lift, from U_H/V₁ to the actual centralizer
in U_H, is justified separately. We give both the disjoint-commutator criterion
and the index-two critical-denominator criterion, reusing the checked group
calculation in `SolvableExclusion.FixedSpace` for the latter.

Consequently the conjugate centralizer bound of 13.7.3(7) gives a genuine
line-valued displacement on the chief section. The conjugation theorem retains
the actual conjugator, source conjugate spans, and reverse containment from
F.9.13(2). Only relative normalizers and normality in U_H are used.

These are partial steps toward the tensor exclusion in Aschbacher–Smith
13.8.21(1), printed p.957 (combined manuscript of 1 March 2004), using
13.7.3(7), 13.8.8 and F.9.13–16. They do not prove that Uγ* is properly
contained in Vγ*, identify a tensor chief section, or exclude the source case.
The index, moved-space noncontainment, and model facts remain explicit here.
-/

@[expose] public section
open Representation Representation.BinaryOffender

private theorem fixed_lift {G V W : Type*} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) G W)
    (f : V →ₗ[ZMod 2] W) (hs : Function.Surjective f)
    (he : ∀ a v, f (ρ a v) = σ a (f v)) (A : Subgroup G)
    (hc : fixedCodim ρ A = fixedCodim σ A) :
    (fixedSpace ρ A).map f = fixedSpace σ A := by
  have hle : (fixedSpace ρ A).map f ≤ fixedSpace σ A := by
    rintro w ⟨v, hv, rfl⟩ a
    change σ a (f v) = f v
    exact (he a v).symm.trans (congrArg f (hv a))
  apply Submodule.eq_of_le_of_finrank_eq hle
  let C := fixedSpace ρ A
  let fc := f.domRestrict C
  have hr : LinearMap.range fc = C.map f := by
    ext w
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨v, v.property, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨⟨v,hv⟩, rfl⟩
  have hk : Module.finrank (ZMod 2) (LinearMap.ker fc) ≤
      Module.finrank (ZMod 2) (LinearMap.ker f) := by
    apply LinearMap.finrank_le_finrank_of_injective (f :=
      (LinearMap.codRestrict (LinearMap.ker f)
        (C.subtype.comp (LinearMap.ker fc).subtype) (fun v => v.property)))
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : LinearMap.ker f => (z : V)) h))
  have hn := fc.finrank_range_add_finrank_ker
  have hf := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs, finrank_top] at hf
  rw [hr] at hn
  have hρ := fixedCodim_add_finrank ρ A
  have hσ := fixedCodim_add_finrank σ A
  have hm := Submodule.finrank_mono hle
  change Module.finrank (ZMod 2) (C.map f) = _
  change fixedCodim ρ A + Module.finrank (ZMod 2) C = _ at hρ
  dsimp only [C] at *
  omega


open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.MarkedCritical
variable {G : Type*} [Group G]
variable (H V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsMulCommutative (Source.Utilde H V₃ V₁)]
  [Module (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]
  (act : SourceAction H V₃ V₁)

/-- The actual quotient map, with additive notation on its target. -/
def quotientMap : Source.UH H V₃ →* Multiplicative (Additive (Source.Utilde H V₃ V₁)) where
  toFun u := Multiplicative.ofAdd (Additive.ofMul
    (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u))
  map_one' := by exact map_one (QuotientGroup.mk' _)
  map_mul' u v := by exact map_mul (QuotientGroup.mk' _) u v

/-- Image of an ambient subgroup, intersected with U_H before taking the quotient. -/
def image (A : Subgroup G) : Submodule (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) :=
  AddSubgroup.toZModSubmodule 2
    (((A.subgroupOf (Source.UH H V₃)).map (quotientMap H V₃ V₁)).toAddSubgroup')

private theorem displacement (a : H) (u : Source.UH H V₃) :
    act.representation (QuotientGroup.mk' (pCore 2 H) a)
        ((quotientMap H V₃ V₁ u).toAdd) - (quotientMap H V₃ V₁ u).toAdd =
      (quotientMap H V₃ V₁
        (conjugateUH H V₃ a u * u⁻¹)).toAdd := by
  rw [map_mul, map_inv]
  change _ = (quotientMap H V₃ V₁ (conjugateUH H V₃ a u)).toAdd +
    -(quotientMap H V₃ V₁ u).toAdd
  rw [← sub_eq_add_neg]
  exact congrArg (fun v => v - (quotientMap H V₃ V₁ u).toAdd) (act.conjugation a u)

omit [Module (ZMod 2) (Additive (Source.Utilde H V₃ V₁))] in
private theorem quotient_zero_iff (u : Source.UH H V₃) :
    (quotientMap H V₃ V₁ u).toAdd = 0 ↔ (u : G) ∈ V₁ :=
  QuotientGroup.eq_one_iff u

/-- With no intersection between V₁ and the actual commutator group, a
fixed coset has a genuinely centralizing representative. -/
theorem quotient_fixed_iff_centralizes (A : Subgroup G) (hAH : A ≤ H)
    (hdis : Disjoint V₁ ⁅Source.UH H V₃, A⁆) (u : Source.UH H V₃) :
    (quotientMap H V₃ V₁ u).toAdd ∈ fixedSpace act.representation (Source.starImage H A) ↔
      (u : G) ∈ centralizer (A : Set G) := by
  constructor
  · intro hu
    apply mem_centralizer_iff.mpr
    intro a ha
    let aH : H := ⟨a, hAH ha⟩
    have hfix := hu ⟨QuotientGroup.mk' (pCore 2 H) aH,
      mem_map_of_mem _ ha⟩
    have hzero := (displacement H V₃ V₁ act aH u).symm.trans (sub_eq_zero.mpr hfix)
    have hz := (quotient_zero_iff H V₃ V₁ _).mp hzero
    have hcomm : ⁅a, (u : G)⁆ ∈ ⁅Source.UH H V₃, A⁆ := by
      rw [commutator_comm]
      exact commutator_mem_commutator ha u.property
    have hone : ⁅a, (u : G)⁆ = 1 :=
      (disjoint_iff.mp hdis).le ⟨hz, hcomm⟩
    exact commutatorElement_eq_one_iff_mul_comm.mp hone
  · intro hu a
    obtain ⟨aH, ha, he⟩ := a.property
    have hc := mem_centralizer_iff.mp hu aH ha
    have hconj : conjugateUH H V₃ aH u = u := by
      apply Subtype.ext
      change (aH : G) * (u : G) * (aH : G)⁻¹ = u
      rw [hc, mul_inv_cancel_right]
    change act.representation (a : Source.Hstar H) ((quotientMap H V₃ V₁ u).toAdd) = _
    rw [← he]
    change act.representation (QuotientGroup.mk' (pCore 2 H) aH)
      (Additive.ofMul (QuotientGroup.mk' _ u)) = _
    rw [act.conjugation, hconj]
    rfl

variable [FiniteDimensional (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]

/-- Equality in the fixed-codimension inequality removes the obstruction
 to lifting fixed vectors from the literal chief section. -/
theorem section_fixed_lift (L N : Subrepresentation act.representation)
    (A : Subgroup G)
    (hc : fixedCodim (sectionRepresentation act.representation L N) (Source.starImage H A) =
      fixedCodim act.representation (Source.starImage H A))
    (w : N.toSubmodule ⧸ (sectionLower act.representation L N).toSubmodule)
    (hw : w ∈ fixedSpace (sectionRepresentation act.representation L N) (Source.starImage H A)) :
    ∃ v : N.toSubmodule,
      (v : Additive (Source.Utilde H V₃ V₁)) ∈ fixedSpace act.representation (Source.starImage H A) ∧
      (sectionLower act.representation L N).toSubmodule.mkQ v = w := by
  have hN := fixedCodim_subrepresentation_le act.representation N (Source.starImage H A)
  have hq := fixedCodim_quotient_add_subrepresentation_le N.toRepresentation
    (sectionLower act.representation L N) (Source.starImage H A)
  have heq : fixedCodim N.toRepresentation (Source.starImage H A) =
      fixedCodim (sectionRepresentation act.representation L N) (Source.starImage H A) := by
    change fixedCodim (sectionRepresentation act.representation L N) _ + _ ≤ _ at hq
    omega
  have he := fixed_lift N.toRepresentation (sectionRepresentation act.representation L N)
    (sectionLower act.representation L N).toSubmodule.mkQ
    (sectionLower act.representation L N).toSubmodule.mkQ_surjective
    (fun _ _ => rfl) (Source.starImage H A) heq
  rw [← he] at hw
  obtain ⟨v, hv, hvw⟩ := hw
  exact ⟨v, fun a => congrArg Subtype.val (hv a), hvw⟩

/-- A fixed vector in the chief section has a representative in the actual
centralizer once both lifting obstructions have been discharged. -/
theorem section_centralizer_lift (L N : Subrepresentation act.representation)
    (A : Subgroup G) (hAH : A ≤ H)
    (hdis : Disjoint V₁ ⁅Source.UH H V₃, A⁆)
    (hc : fixedCodim (sectionRepresentation act.representation L N) (Source.starImage H A) =
      fixedCodim act.representation (Source.starImage H A))
    (w : N.toSubmodule ⧸ (sectionLower act.representation L N).toSubmodule)
    (hw : w ∈ fixedSpace (sectionRepresentation act.representation L N) (Source.starImage H A)) :
    ∃ u : Source.UH H V₃, ∃ hu : (quotientMap H V₃ V₁ u).toAdd ∈ N.toSubmodule,
      (u : G) ∈ centralizer (A : Set G) ∧
      (sectionLower act.representation L N).toSubmodule.mkQ
        ⟨(quotientMap H V₃ V₁ u).toAdd, hu⟩ = w := by
  obtain ⟨v, hv, hvw⟩ := section_fixed_lift H V₃ V₁ act L N A hc w hw
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective
    (V₁.subgroupOf (Source.UH H V₃)) (v.val.toMul)
  have he : (quotientMap H V₃ V₁ u).toAdd = v.val := hu
  refine ⟨u, he.symm ▸ v.property, ?_, ?_⟩
  · apply (quotient_fixed_iff_centralizes H V₃ V₁ act A hAH hdis u).mp
    rwa [he]
  · convert hvw using 1
    exact congrArg (sectionLower act.representation L N).toSubmodule.mkQ (Subtype.ext he)

/-- Image in the chief section of the part of an ambient subgroup lying in
its upper space. This is a subspace, even when the subgroup is not H-invariant. -/
def sectionImage (L N : Subrepresentation act.representation) (A : Subgroup G) :
    Submodule (ZMod 2) (N.toSubmodule ⧸ (sectionLower act.representation L N).toSubmodule) :=
  ((image H V₃ V₁ A).comap N.toSubmodule.subtype).map
    (sectionLower act.representation L N).toSubmodule.mkQ

/-- The conjugate centralizer bound of 13.7.3(7) descends to a chief section
only after fixed vectors have been lifted through both quotients. -/
theorem fixed_section_displacement_mem
    (L N : Subrepresentation act.representation) (A B Z : Subgroup G)
    (hAH : A ≤ H) (hdis : Disjoint V₁ ⁅Source.UH H V₃, A⁆)
    (hc : fixedCodim (sectionRepresentation act.representation L N) (Source.starImage H A) =
      fixedCodim act.representation (Source.starImage H A))
    (hbound : ⁅Source.UH H V₃ ⊓ centralizer (A : Set G), B⁆ ≤ Z) :
    ∀ b ∈ Source.starImage H B, ∀ w ∈
      fixedSpace (sectionRepresentation act.representation L N) (Source.starImage H A),
      sectionRepresentation act.representation L N b w - w ∈
        sectionImage H V₃ V₁ act L N Z := by
  rintro _ ⟨b, hb, rfl⟩ w hw
  obtain ⟨u, hu, huc, huw⟩ := section_centralizer_lift H V₃ V₁ act L N A hAH hdis hc w hw
  let d : Source.UH H V₃ := conjugateUH H V₃ b u * u⁻¹
  have hdZ : (d : G) ∈ Z := by
    apply commutator_le.mp (show ⁅B, Source.UH H V₃ ⊓ centralizer (A : Set G)⁆ ≤ Z from ?_)
      b hb u ⟨u.property, huc⟩
    rwa [commutator_comm]
  have hd : (quotientMap H V₃ V₁ d).toAdd =
      act.representation (QuotientGroup.mk' (pCore 2 H) b)
        (quotientMap H V₃ V₁ u).toAdd - (quotientMap H V₃ V₁ u).toAdd :=
    (displacement H V₃ V₁ act b u).symm
  have hdN : (quotientMap H V₃ V₁ d).toAdd ∈ N.toSubmodule := by
    rw [hd]
    exact N.toSubmodule.sub_mem (N.apply_mem_toSubmodule _ hu) hu
  refine ⟨⟨(quotientMap H V₃ V₁ d).toAdd, hdN⟩, ⟨d, hdZ, rfl⟩, ?_⟩
  rw [← huw, sectionRepresentation_mk, ← map_sub]
  apply congrArg (sectionLower act.representation L N).toSubmodule.mkQ
  exact Subtype.ext hd

variable [Finite G]

/-- Passing an order-two subgroup to the source quotient cannot increase
its binary dimension. -/
theorem image_finrank_le_one (A : Subgroup G) (hA : Nat.card A = 2) :
    Module.finrank (ZMod 2) (image H V₃ V₁ A) ≤ 1 := by
  have hs : Function.Surjective
      (fun x : A.subgroupOf (Source.UH H V₃) =>
        (⟨(quotientMap H V₃ V₁ x.val).toAdd, ⟨x.val, x.property, rfl⟩⟩ : image H V₃ V₁ A)) := by
    rintro ⟨v, u, hu, he⟩
    exact ⟨⟨u, hu⟩, Subtype.ext he⟩
  have hi : Function.Injective
      (fun x : A.subgroupOf (Source.UH H V₃) => (⟨x.val.val, x.property⟩ : A)) := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : A => (z : G)) h))
  have hc := (Nat.card_le_card_of_surjective _ hs).trans
    (Nat.card_le_card_of_injective _ hi)
  rw [hA, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc
  have hh := Nat.log_monotone (b := 2) hc
  simpa only [Nat.log_pow (by decide : 1 < 2), show Nat.log 2 2 = 1 from by decide] using hh

/-- The same bound holds in the literal chief section, with its upper and
lower subspaces both retained. -/
theorem sectionImage_finrank_le_one (L N : Subrepresentation act.representation)
    (A : Subgroup G) (hA : Nat.card A = 2) :
    Module.finrank (ZMod 2) (sectionImage H V₃ V₁ act L N A) ≤ 1 := by
  have hle : Module.finrank (ZMod 2) ((image H V₃ V₁ A).comap N.toSubmodule.subtype) ≤
      Module.finrank (ZMod 2) (image H V₃ V₁ A) := by
    apply LinearMap.finrank_le_finrank_of_injective (f :=
      (LinearMap.codRestrict (image H V₃ V₁ A)
        (N.toSubmodule.subtype.comp ((image H V₃ V₁ A).comap N.toSubmodule.subtype).subtype)
        (fun v => v.property)))
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : image H V₃ V₁ A =>
      (z : Additive (Source.Utilde H V₃ V₁))) h))
  exact (Submodule.finrank_map_le _ _).trans (hle.trans (image_finrank_le_one H V₃ V₁ A hA))


omit [Finite G] [FiniteDimensional (ZMod 2) (Additive (Source.Utilde H V₃ V₁))] in
/-- Fixedness for the source star action gives the actual commutator-preimage
condition, without identifying a quotient fixed space with a centralizer. -/
theorem fixed_mem_commutatorPreimage (A : Subgroup G) (hAH : A ≤ H)
    (u : Source.UH H V₃)
    (hu : (quotientMap H V₃ V₁ u).toAdd ∈ fixedSpace act.representation (Source.starImage H A)) :
    (u : G) ∈ commutatorPreimage (Source.UH H V₃) A V₁ := by
  let F := (((fixedSpace act.representation (Source.starImage H A)).toAddSubgroup.toSubgroup).comap
    (quotientMap H V₃ V₁)).map (Source.UH H V₃).subtype
  have hFU : F ≤ Source.UH H V₃ := by
    rintro x ⟨v, _, rfl⟩
    exact v.property
  have hFA : ⁅F, A⁆ ≤ V₁ := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro a ha x hx
    obtain ⟨v, hv, rfl⟩ := hx
    let aH : H := ⟨a, hAH ha⟩
    have hf := hv ⟨QuotientGroup.mk' (pCore 2 H) aH, mem_map_of_mem _ ha⟩
    exact (quotient_zero_iff H V₃ V₁ _).mp
      ((displacement H V₃ V₁ act aH v).symm.trans (sub_eq_zero.mpr hf))
  exact le_commutatorPreimage hFU hFA (mem_map_of_mem _ hu)

omit [Finite G] in
/-- In the rank-one case, the source index-two denominator and the
non-line-valued moved space discharge the actual-centralizer lifting condition.
This reuses the independently proved group calculation from 13.8.13. -/
theorem section_centralizer_lift_of_index_two
    (L N : Subrepresentation act.representation) (A Z : Subgroup G) (hAH : A ≤ H)
    (hindex : (Source.DH (Source.UH H V₃) A Z).relIndex (Source.UH H V₃) = 2)
    (hnZ : Source.UH H V₃ ≤ normalizer (Z : Set G))
    (hnV : Source.UH H V₃ ≤ normalizer (V₁ : Set G))
    (hmoved : ¬ ⁅Source.UH H V₃, A⁆ ≤ Z ⊔ V₁) (hdis : Disjoint V₁ Z)
    (hc : fixedCodim (sectionRepresentation act.representation L N) (Source.starImage H A) =
      fixedCodim act.representation (Source.starImage H A))
    (w : N.toSubmodule ⧸ (sectionLower act.representation L N).toSubmodule)
    (hw : w ∈ fixedSpace (sectionRepresentation act.representation L N) (Source.starImage H A)) :
    ∃ u : Source.UH H V₃, ∃ hu : (quotientMap H V₃ V₁ u).toAdd ∈ N.toSubmodule,
      (u : G) ∈ centralizer (A : Set G) ∧
      (sectionLower act.representation L N).toSubmodule.mkQ
        ⟨(quotientMap H V₃ V₁ u).toAdd, hu⟩ = w := by
  obtain ⟨v, hv, hvw⟩ := section_fixed_lift H V₃ V₁ act L N A hc w hw
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective
    (V₁.subgroupOf (Source.UH H V₃)) v.val.toMul
  have he : (quotientMap H V₃ V₁ u).toAdd = v.val := hu
  have hfu := fixed_mem_commutatorPreimage H V₃ V₁ act A hAH u (he.symm ▸ hv)
  change (u : G) ∈ SolvableExclusion.fixedPreimage (Source.UH H V₃) A V₁ at hfu
  rw [SolvableExclusion.fixedPreimage_eq_centralizer _ _ Z _ hindex hnZ hnV hmoved hdis] at hfu
  refine ⟨u, he.symm ▸ v.property, hfu.2, ?_⟩
  exact (congrArg (sectionLower act.representation L N).toSubmodule.mkQ (Subtype.ext he)).trans hvw


omit [Finite G] in
/-- Rank-one version of the displacement transfer, using the genuine critical denominator. -/
theorem fixed_section_displacement_mem_of_index_two
    (L N : Subrepresentation act.representation) (A B Z : Subgroup G)
    (hAH : A ≤ H)
    (hindex : (Source.DH (Source.UH H V₃) A Z).relIndex (Source.UH H V₃) = 2)
    (hnZ : Source.UH H V₃ ≤ normalizer (Z : Set G))
    (hnV : Source.UH H V₃ ≤ normalizer (V₁ : Set G))
    (hmoved : ¬ ⁅Source.UH H V₃, A⁆ ≤ Z ⊔ V₁) (hdis : Disjoint V₁ Z)
    (hc : fixedCodim (sectionRepresentation act.representation L N) (Source.starImage H A) =
      fixedCodim act.representation (Source.starImage H A))
    (hbound : ⁅Source.UH H V₃ ⊓ centralizer (A : Set G), B⁆ ≤ Z) :
    ∀ b ∈ Source.starImage H B, ∀ w ∈
      fixedSpace (sectionRepresentation act.representation L N) (Source.starImage H A),
      sectionRepresentation act.representation L N b w - w ∈
        sectionImage H V₃ V₁ act L N Z := by
  rintro _ ⟨b, hb, rfl⟩ w hw
  obtain ⟨u, hu, huc, huw⟩ := section_centralizer_lift_of_index_two H V₃ V₁ act L N A Z
    hAH hindex hnZ hnV hmoved hdis hc w hw
  let d : Source.UH H V₃ := conjugateUH H V₃ b u * u⁻¹
  have hdZ : (d : G) ∈ Z := by
    apply commutator_le.mp (show ⁅B, Source.UH H V₃ ⊓ centralizer (A : Set G)⁆ ≤ Z from ?_)
      b hb u ⟨u.property, huc⟩
    rwa [commutator_comm]
  have hd : (quotientMap H V₃ V₁ d).toAdd =
      act.representation (QuotientGroup.mk' (pCore 2 H) b)
        (quotientMap H V₃ V₁ u).toAdd - (quotientMap H V₃ V₁ u).toAdd :=
    (displacement H V₃ V₁ act b u).symm
  have hdN : (quotientMap H V₃ V₁ d).toAdd ∈ N.toSubmodule := by
    rw [hd]
    exact N.toSubmodule.sub_mem (N.apply_mem_toSubmodule _ hu) hu
  refine ⟨⟨(quotientMap H V₃ V₁ d).toAdd, hdN⟩, ⟨d, hdZ, rfl⟩, ?_⟩
  rw [← huw, sectionRepresentation_mk, ← map_sub]
  apply congrArg (sectionLower act.representation L N).toSubmodule.mkQ
  exact Subtype.ext hd

/-- The critical bound and the tensor section's codimension two force equality,
so the conjugate of 13.7.3(7) confines the section displacement to a line. -/
theorem exists_section_displacement_line
    (L N : Subrepresentation act.representation) (A B Z : Subgroup G)
    (hAH : A ≤ H)
    (hindex : (Source.DH (Source.UH H V₃) A Z).relIndex (Source.UH H V₃) = 2)
    (hnZ : Source.UH H V₃ ≤ normalizer (Z : Set G))
    (hnV : Source.UH H V₃ ≤ normalizer (V₁ : Set G))
    (hmoved : ¬ ⁅Source.UH H V₃, A⁆ ≤ Z ⊔ V₁) (hdis : Disjoint V₁ Z)
    (hsmall : fixedCodim act.representation (Source.starImage H A) ≤ 2)
    (hsection : fixedCodim (sectionRepresentation act.representation L N)
      (Source.starImage H A) = 2)
    (hbound : ⁅Source.UH H V₃ ⊓ centralizer (A : Set G), B⁆ ≤ Z)
    (hZ : Nat.card Z = 2) :
    ∃ D : Submodule (ZMod 2)
      (N.toSubmodule ⧸ (sectionLower act.representation L N).toSubmodule),
      Module.finrank (ZMod 2) D ≤ 1 ∧
        ∀ b ∈ Source.starImage H B, ∀ w ∈
          fixedSpace (sectionRepresentation act.representation L N) (Source.starImage H A),
          sectionRepresentation act.representation L N b w - w ∈ D := by
  have hc := fixedCodim_section_le act.representation L N (Source.starImage H A)
  have heq : fixedCodim (sectionRepresentation act.representation L N) (Source.starImage H A) =
      fixedCodim act.representation (Source.starImage H A) := by omega
  exact ⟨sectionImage H V₃ V₁ act L N Z,
    sectionImage_finrank_le_one H V₃ V₁ act L N Z hZ,
    fixed_section_displacement_mem_of_index_two H V₃ V₁ act L N A B Z
      hAH hindex hnZ hnV hmoved hdis heq hbound⟩

omit [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsMulCommutative (Source.Utilde H V₃ V₁)]
  [Module (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]
  [FiniteDimensional (ZMod 2) (Additive (Source.Utilde H V₃ V₁))] [Finite G] in
/-- Transport 13.7.3(7) by the actual critical conjugator. The reverse
containment comes from F.9.13(2); all centralizers remain relative to H or H^g. -/
theorem conjugate_centralizer_bound (V : Subgroup G) (g : G)
    (hreverse : Source.UH H V₃ ≤ H.map (MulAut.conj g).toMonoidHom)
    (hbound : ⁅Source.HC H V₃, Source.VH H V⁆ ≤ V₁) :
    ⁅Source.UH H V₃ ⊓ centralizer
      ((Source.UH H V₃).map (MulAut.conj g).toMonoidHom : Set G),
      (Source.VH H V).map (MulAut.conj g).toMonoidHom⁆ ≤
        V₁.map (MulAut.conj g).toMonoidHom := by
  have hle : Source.UH H V₃ ⊓ centralizer
      ((Source.UH H V₃).map (MulAut.conj g).toMonoidHom : Set G) ≤
      (Source.HC H V₃).map (MulAut.conj g).toMonoidHom := by
    intro x hx
    obtain ⟨y, hy, he⟩ := hreverse hx.1
    change (MulAut.conj g) y = x at he
    refine ⟨y, ⟨hy, ?_⟩, he⟩
    apply mem_centralizer_iff.mpr
    intro u hu
    apply (MulAut.conj g).injective
    simpa only [map_mul, he] using
      mem_centralizer_iff.mp hx.2 ((MulAut.conj g) u) (mem_map_of_mem _ hu)
  apply (commutator_mono hle le_rfl).trans
  rw [← map_commutator]
  exact map_mono hbound

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.MarkedCritical
