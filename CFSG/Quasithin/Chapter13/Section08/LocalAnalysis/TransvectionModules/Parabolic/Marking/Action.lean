module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Action

/-!
# Literal commutator and fixed-space transport for the parabolic marking

The image of [U_H,K] in U_H/V₁ is exactly the linear commutator space of
K*. Both containments are proved on the group and vector generators, using
the actual conjugation action. The pointwise fixer of the image of V₂ is
likewise the subgroup defined by [h,V₂] ≤ V₁. In particular neither the
commutator carrier nor the point centralizer is replaced by an unrelated
representation.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the natural
section premise of 13.7.6(3), printed pp.938–939, and 13.8.6, printed p.948.
These bridges prepare the source applicability and marking arguments.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.Marking
open TransvectionRecognition
variable {G : Type*} [Group G] (H V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- The literal additive image of X in U_H/V₁. -/
def sectionImage (X : Subgroup G) :
    Submodule (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) :=
  AddSubgroup.toZModSubmodule 2
    (((X.subgroupOf (Source.UH H V₃)).map
      (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)))).toAddSubgroup)

variable {H V₃ V₁}
variable (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
  (hρ : IsConjugation H V₃ V₁ ρ)

include hρ

/-- The linear commutator is exactly the image of the source group commutator. -/
theorem commutator_image (K : Subgroup G) (hKH : K ≤ H) :
    sectionImage H V₃ V₁ ⁅Source.UH H V₃, K⁆ =
      subspaceCommutator ρ ⊤ (Source.starImage H K) := by
  let U := Source.UH H V₃
  let q : U →* Source.Utilde H V₃ V₁ := QuotientGroup.mk' (V₁.subgroupOf U)
  let S := subspaceCommutator ρ ⊤ (Source.starImage H K)
  let C := (S.toAddSubgroup.toSubgroup'.comap q).map U.subtype
  have hcomm : ⁅U, K⁆ ≤ C := by
    apply commutator_le.mpr
    intro u hu k hk
    have hc : ⁅u, k⁆ ∈ U :=
      le_normalizer_iff_commutator_le_left.mp (le_normalizer_conjugateSpanBy V₃ H)
        (commutator_mem_commutator hu (hKH hk))
    refine ⟨⟨⁅u, k⁆, hc⟩, ?_, rfl⟩
    change vector H V₃ V₁ _ ∈ S
    rw [vector_commutator ρ hρ ⟨u, hu⟩ ⟨k, hKH hk⟩]
    have hm : ρ (QuotientGroup.mk' (pCore 2 H) ⟨k, hKH hk⟩)
        (vector H V₃ V₁ ⟨u, hu⟩) - vector H V₃ V₁ ⟨u, hu⟩ ∈ S :=
      Submodule.subset_span ⟨_, ⟨⟨k, hKH hk⟩, hk, rfl⟩, _, Submodule.mem_top, rfl⟩
    simpa only [neg_sub] using S.neg_mem hm
  apply le_antisymm
  · rintro x ⟨u, hu, rfl⟩
    obtain ⟨w, hw, he⟩ := hcomm hu
    have he' : w = u := Subtype.ext he
    subst w
    exact hw
  · apply Submodule.span_le.mpr
    rintro x ⟨a, ⟨k, hk, rfl⟩, u, _, rfl⟩
    obtain ⟨v, hv⟩ := QuotientGroup.mk'_surjective (V₁.subgroupOf U) u.toMul
    have hvec : vector H V₃ V₁ v = u := congrArg Additive.ofMul hv
    rw [← hvec]
    let c : U := ⟨⁅(v : G), (k : G)⁆,
      le_normalizer_iff_commutator_le_left.mp (le_normalizer_conjugateSpanBy V₃ H)
        (commutator_mem_commutator v.property k.property)⟩
    have hc : vector H V₃ V₁ c ∈ sectionImage H V₃ V₁ ⁅U, K⁆ :=
      ⟨c, commutator_mem_commutator v.property hk, rfl⟩
    rw [vector_commutator ρ hρ v k] at hc
    have hn := (sectionImage H V₃ V₁ ⁅U, K⁆).neg_mem hc
    rw [neg_sub] at hn
    change ρ (QuotientGroup.mk' (pCore 2 H) k) (vector H V₃ V₁ v) -
      vector H V₃ V₁ v ∈ sectionImage H V₃ V₁ ⁅U, K⁆
    exact hn

/-- The quotient centralizer uses the image of the actual V₂. -/
theorem quotient_centralizer_preimage (V₂ : Subgroup G) (hV₂ : V₂ ≤ Source.UH H V₃)
    (hHZ : H ≤ normalizer (V₁ : Set G)) :
    (commutatorPreimage H V₂ V₁).subgroupOf H =
      subspaceKernel (ρ.comp (QuotientGroup.mk' (pCore 2 H)))
        (sectionImage H V₃ V₁ V₂) ⊤ := by
  let U := Source.UH H V₃
  let A := subspaceKernel (ρ.comp (QuotientGroup.mk' (pCore 2 H)))
    (sectionImage H V₃ V₁ V₂) ⊤
  apply le_antisymm
  · intro h hh
    refine ⟨mem_top _, ?_⟩
    rintro x ⟨v, hv, rfl⟩
    have hc : ⁅(v : G), (h : G)⁆ ∈ V₁ := by
      have hc := commutator_commutatorPreimage_le H V₂ V₁ hHZ
      rw [commutator_comm] at hc
      exact hc (commutator_mem_commutator hv hh)
    have hz : vector H V₃ V₁ ⟨⁅(v : G), (h : G)⁆,
        le_normalizer_iff_commutator_le_left.mp (le_normalizer_conjugateSpanBy V₃ H)
          (commutator_mem_commutator v.property h.property)⟩ = 0 :=
      (QuotientGroup.eq_one_iff _).mpr hc
    rw [vector_commutator ρ hρ v h] at hz
    exact (sub_eq_zero.mp hz).symm
  · have hC : A.map H.subtype ≤ commutatorPreimage H V₂ V₁ := by
      apply le_commutatorPreimage (map_subtype_le _)
      rw [commutator_comm]
      apply commutator_le.mpr
      rintro v hv _ ⟨h, hh, rfl⟩
      let u : U := ⟨v, hV₂ hv⟩
      have hf := hh.2 (vector H V₃ V₁ u) ⟨u, hv, rfl⟩
      change ρ (QuotientGroup.mk' (pCore 2 H) h) (vector H V₃ V₁ u) =
        vector H V₃ V₁ u at hf
      have hz := vector_commutator ρ hρ u h
      rw [hf, sub_self] at hz
      exact (QuotientGroup.eq_one_iff (N := V₁.subgroupOf U)
        (⟨⁅v, (h : G)⁆, le_normalizer_iff_commutator_le_left.mp
          (le_normalizer_conjugateSpanBy V₃ H)
          (commutator_mem_commutator (hV₂ hv) h.property)⟩ : U)).mp hz
    intro h hh
    exact hC ⟨h, hh, rfl⟩
end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.Marking
