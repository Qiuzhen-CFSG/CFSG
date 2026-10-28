module

public import Theory.GroupTheory.DoubleCoverCentralizer.ProjectiveRadicalSplitting.Linear
public import Theory.GroupTheory.DoubleCoverCentralizer.ProjectiveRadicalSplitting.QuotientAction

/-!
# Splitting a central radical extension by projectivity

Let `R` be the kernel of a surjection from `H` to A₅, and let `V,Z ≤ R`
be central and disjoint, with `V ≤ [R,H]`. Suppose `R/V` is elementary
abelian and the literal conjugation-equivariant map from `R` onto the binary
five-point augmentation module has kernel `VZ`. Then `R = [R,H]Z` and
`[R,H] ∩ Z = 1`.

We descend conjugation through the specified map to A₅ and linearize the
literal quotient map. Its kernel is exactly the image of `Z`. Projectivity
splits this map, and displacement generation identifies the section image
with the image of `[R,H]`. Lifting uses `V ≤ [R,H]` and `V ∩ Z = 1`.
No complement or covering-group recognition is assumed. The splitting itself
does not need finiteness or perfection; those are used in the subsequent
source recognition of the quotient by `[R,H]`.

Source: Aschbacher–Smith I.2.2(5), printed pp.411–412 / PDF pp.422–423,
combined manuscript of 1 March 2004.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative commutatorElement

namespace ProjectiveRadicalSplitting

/-- Lift a projective module splitting to the literal radical and commutator
subgroups, retaining the quotient kernel and conjugation formulas. -/
theorem split_of_linear_map
    {H A E W : Type*} [Group H] [Group A] [Group E] [IsElementaryAbelian 2 E]
    [AddCommGroup W] [Module (ZMod 2) W]
    (R V Z : Subgroup H) [R.Normal]
    (hV : V ≤ center H) (hZ : Z ≤ center H) (hZR : Z ≤ R)
    (hVD : V ≤ ⁅R, (⊤ : Subgroup H)⁆) (hVZ : Disjoint V Z)
    (a : H →* A) (ha : Function.Surjective a)
    (q : R →* E) (hq : Function.Surjective q) (hqker : q.ker = V.subgroupOf R)
    (α : A →* MulAut E)
    (hα : ∀ h : H, ∀ r : R, α (a h) (q r) = q (MulAut.conjNormal h r))
    (ρ : Representation (ZMod 2) A W)
    [Module.Projective (MonoidAlgebra (ZMod 2) A) ρ.asModule]
    (hc : Coinvariants.ker ρ = ⊤)
    (f : (linearAction α).IntertwiningMap ρ) (hf : Function.Surjective f)
    (hfker : ∀ r : R, f (Additive.ofMul (q r)) = 0 ↔ (r : H) ∈ V ⊔ Z) :
    R = ⁅R, (⊤ : Subgroup H)⁆ ⊔ Z ∧ Disjoint ⁅R, (⊤ : Subgroup H)⁆ Z := by
  let D : Subgroup H := ⁅R, (⊤ : Subgroup H)⁆
  have hDR : D ≤ R := commutator_le_left _ _
  have hk : ∀ w, f w = 0 → ∀ g, linearAction α g w = w := by
    intro w hw g
    obtain ⟨h, rfl⟩ := ha g
    obtain ⟨r, hr⟩ := hq w.toMul
    have hwr : w = Additive.ofMul (q r) := congrArg Additive.ofMul hr.symm
    subst w
    have hz := (sup_le hV hZ) ((hfker r).mp hw)
    rw [linearAction_apply, toMul_ofMul, hα]
    congr 2
    apply Subtype.ext
    change h * (r : H) * h⁻¹ = r
    rw [mem_center_iff.mp hz h]
    simp
  obtain ⟨s, hs, hsrange⟩ := exists_section_range_eq_coinvariants f hf hk hc
  have himage := commutatorImage_eq_coinvariants R a ha q hq α hα
  have hmem (r : R) (hr : (r : H) ∈ D) :
      Additive.ofMul (q r) ∈ Coinvariants.ker (linearAction α) := by
    rw [← himage]
    exact ⟨r, hr, rfl⟩
  constructor
  · apply le_antisymm ?_ (sup_le hDR hZR)
    intro x hx
    let r : R := ⟨x, hx⟩
    let w := Additive.ofMul (q r)
    have hsC : s (f w) ∈ Coinvariants.ker (linearAction α) := by
      rw [← hsrange]
      exact ⟨f w, rfl⟩
    rw [← himage] at hsC
    obtain ⟨d, hd, hde⟩ := (show (s (f w)).toMul ∈ (D.subgroupOf R).map q from hsC)
    have hzero : f (Additive.ofMul (q (r * d⁻¹))) = 0 := by
      rw [map_mul, map_inv, hde]
      simp only [ofMul_mul, ofMul_inv, ofMul_toMul]
      change f (w + -(s (f w))) = 0
      rw [← sub_eq_add_neg]
      rw [map_sub, hs, sub_self]
    have hrD : (x * (d : H)⁻¹) ∈ D ⊔ Z :=
      sup_le_sup_right hVD Z ((hfker (r * d⁻¹)).mp hzero)
    have hxD := (D ⊔ Z).mul_mem hrD (mem_sup_left hd)
    simpa using hxD
  · apply disjoint_iff.mpr
    apply eq_bot_iff.mpr
    rintro x ⟨hxD, hxZ⟩
    let r : R := ⟨x, hDR hxD⟩
    have hfzero : f (Additive.ofMul (q r)) = 0 := (hfker r).mpr (mem_sup_right hxZ)
    have hw := hmem r hxD
    rw [← hsrange] at hw
    obtain ⟨w, hw⟩ := hw
    change s w = Additive.ofMul (q r) at hw
    have hwzero : w = 0 := by rw [← hs w, hw, hfzero]
    have hqr : q r = 1 := by
      have he : Additive.ofMul (q r) = 0 := by rw [← hw, hwzero, map_zero]
      exact congrArg Additive.toMul he
    have hxV : x ∈ V := by
      have hr := MonoidHom.mem_ker.mpr hqr
      rw [hqker] at hr
      exact hr
    exact disjoint_def.mp hVZ hxV hxZ

end ProjectiveRadicalSplitting

namespace ProjectiveRadicalSplitting

/-- The given radical homomorphism induces an equivariant linear surjection
on the literal `R/V`, with kernel exactly the image of `Z`. -/
theorem exists_linear_quotient_map
    {H A W : Type*} [Group H] [Group A] [AddCommGroup W] [Module (ZMod 2) W]
    (R V Z : Subgroup H) [R.Normal] [(V.subgroupOf R).Normal]
    [IsElementaryAbelian 2 (R ⧸ V.subgroupOf R)]
    (hV : V ≤ center H) (hVR : V ≤ R) (hZR : Z ≤ R)
    (a : H →* A) (ha : Function.Surjective a)
    (α : A →* MulAut (R ⧸ V.subgroupOf R))
    (hα : ∀ h : H, ∀ r : R,
      α (a h) (QuotientGroup.mk' (V.subgroupOf R) r) =
        QuotientGroup.mk' (V.subgroupOf R) (MulAut.conjNormal h r))
    (ρ : Representation (ZMod 2) A W)
    (b : R →* Multiplicative W) (hb : Function.Surjective b)
    (hbker : b.ker = (V ⊔ Z).subgroupOf R)
    (hbe : ∀ h : H, ∀ r : R,
      (b (MulAut.conjNormal h r)).toAdd = ρ (a h) (b r).toAdd) :
    ∃ f : (linearAction α).IntertwiningMap ρ,
      Function.Surjective f ∧
      (∀ r : R, f (Additive.ofMul (QuotientGroup.mk' (V.subgroupOf R) r)) =
        (b r).toAdd) ∧
      f.toLinearMap.ker = AddSubgroup.toZModSubmodule 2
        (((Z.subgroupOf R).map (QuotientGroup.mk' (V.subgroupOf R))).toAddSubgroup) := by
  let q := QuotientGroup.mk' (V.subgroupOf R)
  have hVb : V.subgroupOf R ≤ b.ker := by
    rw [hbker]
    intro r hr
    exact mem_sup_left hr
  let B := QuotientGroup.lift (V.subgroupOf R) b hVb
  let F := B.toAdditiveLeft.toZModLinearMap 2
  have hF (r : R) : F (Additive.ofMul (q r)) = (b r).toAdd := rfl
  have he : ∀ g w, F (linearAction α g w) = ρ g (F w) := by
    intro g w
    obtain ⟨h, rfl⟩ := ha g
    obtain ⟨r, hr⟩ := QuotientGroup.mk'_surjective (V.subgroupOf R) w.toMul
    have hwr : w = Additive.ofMul (q r) := congrArg Additive.ofMul hr.symm
    rw [hwr, linearAction_apply, toMul_ofMul, hα, hF, hF]
    exact hbe h r
  let f := F.intertwiningMap_of_isIntertwiningMap (linearAction α) ρ he
  have hf (r : R) : f (Additive.ofMul (q r)) = (b r).toAdd := hF r
  refine ⟨f, ?_, hf, ?_⟩
  · intro w
    obtain ⟨r, hr⟩ := hb (Multiplicative.ofAdd w)
    exact ⟨Additive.ofMul (q r), (hf r).trans (congrArg Multiplicative.toAdd hr)⟩
  · have : V.Normal := ⟨fun v hv h => by
      rw [mem_center_iff.mp (hV hv) h]
      simpa using hv⟩
    ext w
    obtain ⟨r, hr⟩ := QuotientGroup.mk'_surjective (V.subgroupOf R) w.toMul
    have hwr : w = Additive.ofMul (q r) := congrArg Additive.ofMul hr.symm
    rw [hwr]
    change f (Additive.ofMul (q r)) = 0 ↔ q r ∈ (Z.subgroupOf R).map q
    rw [hf]
    constructor
    · intro hr0
      have hbr : b r = 1 := congrArg Multiplicative.ofAdd hr0
      have hrker := MonoidHom.mem_ker.mpr hbr
      rw [hbker] at hrker
      obtain ⟨v, hv, z, hz, heq⟩ := mem_sup_of_normal_left.mp hrker
      let vR : R := ⟨v, hVR hv⟩
      let zR : R := ⟨z, hZR hz⟩
      have hre : r = vR * zR := Subtype.ext heq.symm
      refine ⟨zR, hz, ?_⟩
      rw [hre, map_mul, show q vR = 1 from (QuotientGroup.eq_one_iff vR).mpr hv,
        one_mul]
    · rintro ⟨z, hz, heq⟩
      have hzker : b z = 1 := MonoidHom.mem_ker.mp (hbker ▸ mem_sup_right hz)
      have heF := congrArg (fun x => f (Additive.ofMul x)) heq
      rw [hf, hf, hzker] at heF
      exact heF.symm

/-- Projectivity of the actual binary A₅ augmentation module gives the central
supplement and its trivial intersection with the intrinsic commutator. -/
theorem radical_splitting
    {H : Type*} [Group H]
    (R V Z : Subgroup H) [R.Normal] [(V.subgroupOf R).Normal]
    [IsElementaryAbelian 2 (R ⧸ V.subgroupOf R)]
    (a : H →* alternatingGroup (Fin 5)) (ha : Function.Surjective a) (hR : a.ker = R)
    (hV : V ≤ center H) (hZ : Z ≤ center H) (hZR : Z ≤ R)
    (hVD : V ≤ ⁅R, (⊤ : Subgroup H)⁆) (hVZ : Disjoint V Z)
    (b : R →* Multiplicative (BinaryPermutation.core (Fin 5)))
    (hb : Function.Surjective b) (hbker : b.ker = (V ⊔ Z).subgroupOf R)
    (hbe : ∀ h : H, ∀ r : R,
      (b (MulAut.conjNormal h r)).toAdd =
        BinaryPermutation.alternatingCoreRepresentation (Fin 5) (a h) (b r).toAdd) :
    R = ⁅R, (⊤ : Subgroup H)⁆ ⊔ Z ∧ Disjoint ⁅R, (⊤ : Subgroup H)⁆ Z := by
  obtain ⟨α, hα⟩ := exists_quotient_action R V a ha hR hV
  let ρ := BinaryPermutation.alternatingCoreRepresentation (Fin 5)
  obtain ⟨f, hf, hfr, _⟩ := exists_linear_quotient_map R V Z hV
    (hVD.trans (commutator_le_left _ _)) hZR a ha α hα ρ b hb hbker hbe
  have hfk (r : R) : f (Additive.ofMul (QuotientGroup.mk' (V.subgroupOf R) r)) = 0 ↔
      (r : H) ∈ V ⊔ Z := by
    rw [hfr]
    change b r = 1 ↔ r ∈ (V ⊔ Z).subgroupOf R
    rw [← hbker]
    rfl
  let := BinaryPermutation.alternatingFive_core_projective
  exact split_of_linear_map R V Z hV hZ hZR hVD hVZ a ha
    (QuotientGroup.mk' (V.subgroupOf R)) (QuotientGroup.mk'_surjective _) (by simp)
    α hα ρ alternatingFive_core_generated f hf hfk

end ProjectiveRadicalSplitting
