module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.PairsBranch.CentralAction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.PairsBranch.ModuleSelection.Seed
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.SourceSeed

/-!
# The literal source module in the three-pairs branch

The image of V₃ in U_H/V₁ generates under H* because U_H is its H-conjugate
span. Relative normalization gives its L₁*T*-invariance. The group identity
U_H = [U_H,K] descends to linear commutator generation by K*: pull the linear
commutator subspace back to a subgroup and check the group generators.

These transport results use the actual quotient action on representatives.
They require only normality of V₁ inside U_H, and do not assert any module
classification or nontrivial action on a proper submodule.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.21(4)
and the paragraph preceding 13.8.22, printed p.957/PDF p.974.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.PairsBranch
open AlternatingAndLinear.FourStructure.ChiefFactors
variable {G : Type*} [Group G] (H V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- The literal image of a local subgroup in U_H/V₁; intersection with U_H
is part of the definition, including for A₁ when it is not contained in U_H. -/
def sourceImage (X : Subgroup G) : Submodule (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) :=
  AddSubgroup.toZModSubmodule 2
    (((X.subgroupOf (Source.UH H V₃)).map (sourceProjection H V₃ V₁)).toAddSubgroup)

variable (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
  (hρ : CentralAction.IsSourceAction H V₃ V₁ ρ)

include hρ in
/-- The actual seed generates, without an additional linear generation premise. -/
theorem source_seed_generates : ModuleSelection.SeedGenerates ρ (sourceImage H V₃ V₁ V₃) := by
  let S := Submodule.span (ZMod 2) {v | ∃ h : Source.Hstar H,
    ∃ a ∈ sourceImage H V₃ V₁ V₃, ρ h a = v}
  have hs : ∀ h : Source.Hstar H, ∀ v ∈ S, ρ h v ∈ S := by
    intro h v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨g, a, ha, rfl⟩ := hv
      exact Submodule.subset_span ⟨h * g, a, ha, by rw [map_mul]; rfl⟩
    | zero => simp
    | add v w hv hw ihv ihw => simpa using S.add_mem ihv ihw
    | smul c v hv ih => simpa using S.smul_mem c ih
  exact congrArg Subrepresentation.toSubmodule
    (sourceSeedSpace_generates H V₃ V₁ ρ hρ (⟨S, hs⟩ : Subrepresentation ρ)
      (fun v hv => Submodule.subset_span ⟨1, v, hv, by simp⟩))

include hρ in
/-- Relative normalization induces invariance of the literal image. -/
theorem source_image_stable (P X : Subgroup G) (hP : P ≤ normalizer (X : Set G)) :
    Source.starImage H P ≤ subspaceStabilizer ρ (sourceImage H V₃ V₁ X) := by
  have hact : IsSourceAction H V₃ V₁ ρ := hρ
  apply le_subspaceStabilizer
  rintro _ ⟨h, hh, rfl⟩ _ ⟨u, hu, rfl⟩
  change ρ (QuotientGroup.mk' (pCore 2 H) h)
    (Additive.ofMul (sourceProjection H V₃ V₁ u)) ∈ sourceImage H V₃ V₁ X
  rw [hact]
  exact ⟨sourceConjugate H V₃ h u, (mem_normalizer_iff.mp (hP hh) u).mp hu, rfl⟩

/-- The seed with its actual restricted L₁*-action. -/
def sourceSeed (L₁ : Subgroup G) (hL : L₁ ≤ normalizer (V₃ : Set G)) :
    Subrepresentation (ρ.comp (Source.starImage H L₁).subtype) :=
  invariantSubspace ρ (Source.starImage H L₁) (sourceImage H V₃ V₁ V₃)
    (source_image_stable H V₃ V₁ ρ hρ L₁ V₃ hL)

include hρ in
/-- The group commutator identity supplies the linear identity used by the sieve. -/
theorem source_commutator_generated (K : Subgroup G) (hKH : K ≤ H)
    (hgen : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆) :
    subspaceCommutator ρ ⊤ (Source.starImage H K) = ⊤ := by
  have hact : IsSourceAction H V₃ V₁ ρ := hρ
  let C := subspaceCommutator ρ ⊤ (Source.starImage H K)
  let J : Subgroup (Source.UH H V₃) :=
    (Subgroup.toAddSubgroup.symm C.toAddSubgroup).comap (sourceProjection H V₃ V₁)
  let B : Subgroup G := J.map (Source.UH H V₃).subtype
  have hcomm : ⁅K, Source.UH H V₃⁆ ≤ B := by
    apply commutator_le.mpr
    intro k hk u hu
    let kH : H := ⟨k, hKH hk⟩
    let uH : Source.UH H V₃ := ⟨u, hu⟩
    let d : Source.UH H V₃ := sourceConjugate H V₃ kH uH * uH⁻¹
    refine ⟨d, ?_, rfl⟩
    have hd : ρ (QuotientGroup.mk' (pCore 2 H) kH)
        (Additive.ofMul (sourceProjection H V₃ V₁ uH)) -
        Additive.ofMul (sourceProjection H V₃ V₁ uH) ∈ C :=
      Submodule.subset_span ⟨_, ⟨kH, hk, rfl⟩, _, Submodule.mem_top, rfl⟩
    rw [hact] at hd
    change Additive.ofMul (sourceProjection H V₃ V₁
      (sourceConjugate H V₃ kH uH * uH⁻¹)) ∈ C
    rw [map_mul, map_inv]
    change Additive.ofMul (sourceProjection H V₃ V₁ (sourceConjugate H V₃ kH uH)) +
      -Additive.ofMul (sourceProjection H V₃ V₁ uH) ∈ C
    simpa only [sub_eq_add_neg] using hd
  have hUB : Source.UH H V₃ ≤ B := by
    rw [hgen, commutator_comm]
    exact hcomm
  apply top_unique
  intro v _
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (V₁.subgroupOf (Source.UH H V₃)) v.toMul
  obtain ⟨w, hw, hwu⟩ := hUB u.property
  have he : w = u := Subtype.ext hwu
  subst w
  change Additive.ofMul (sourceProjection H V₃ V₁ u) ∈ C at hw
  simpa [sourceProjection, hu] using hw

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.PairsBranch
