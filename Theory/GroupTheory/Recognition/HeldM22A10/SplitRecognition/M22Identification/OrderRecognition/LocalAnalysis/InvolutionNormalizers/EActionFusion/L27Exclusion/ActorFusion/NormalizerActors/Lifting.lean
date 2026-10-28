module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.L27Exclusion.ActorFusion.NormalizerActors.Centralizer

/-!
# Lifting the marked binary actor conjugacy

A conjugator between the two marked actors in the faithful binary image
lifts to the actual normalizer. Its error lies in E. Every involution in
Ea is E-conjugate to a, as a calculation in the given twisted model shows,
so this error can be removed without assuming a splitting of N(E).

This module leaves binary actor conjugacy explicit. Its application to
Janko's order-168 branch must supply that finite-action theorem.
Source: Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, Lemma 6, printed p.6.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
open LocalModelDichotomy

local instance : DecidableEq TwistedModel := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right) SemidirectProduct.ext_iff.symm
local instance : Fintype TwistedModel := Fintype.ofEquiv
  (BinaryFour × SymmetricFour) SemidirectProduct.equivProd.symm

private theorem involutions_in_Ea : ∀ x : TwistedModel,
    x.right = a.right → x ^ 2 = 1 →
    ∃ v : BinaryFour, SemidirectProduct.inl v * x * (SemidirectProduct.inl v)⁻¹ = a := by
  decide +kernel

universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

/-- A local permutation actor in the actual faithful binary image. -/
@[expose] public noncomputable def eNormalizerBinaryActor (s : SymmetricFour) :
    eNormalizerBinaryImage D k :=
  ⟨twistedAction s, twistedAction_le_eNormalizerBinaryImage D k ⟨s, rfl⟩⟩

/-- Binary conjugacy of the marked actors lifts to actual conjugacy in N(E).
The explicit premise is the remaining finite-action input, not ambient fusion. -/
public theorem l27_actor_d_conjugate_a_of_binary_isConj
    (hc : IsConj (eNormalizerBinaryActor D k d.right) (eNormalizerBinaryActor D k a.right)) :
    ∃ n : normalizer (E D k : Set G),
      (n : G) * into D k d * (n : G)⁻¹ = into D k a := by
  let N := normalizer (E D k : Set G)
  let dN : N := ⟨into D k d, centralizer_le_normalizer_E D k (k d).property⟩
  let aN : N := ⟨into D k a, centralizer_le_normalizer_E D k (k a).property⟩
  let q := eNormalizerBinaryAction D k
  have hdq : q dN = twistedAction d.right := eNormalizerBinaryAction_local D k d.right
  have haq : q aN = twistedAction a.right := eNormalizerBinaryAction_local D k a.right
  obtain ⟨f, hf⟩ := isConj_iff.mp hc
  have hfmem : f.val ∈ q.range := by
    simpa only [q, eNormalizerBinaryAction_range D k] using f.property
  obtain ⟨g, hg⟩ := hfmem
  have hgq : q (g * dN * g⁻¹) = q aN := by
    rw [map_mul, map_mul, map_inv, hdq, haq, hg]
    exact congrArg Subtype.val hf
  have hvker : (g * dN * g⁻¹) / aN ∈ q.ker := by
    change q ((g * dN * g⁻¹) / aN) = 1
    rw [map_div, hgq, div_self']
  rw [eNormalizerBinaryAction_ker] at hvker
  have hvE : ((g : G) * into D k d * (g : G)⁻¹) / into D k a ∈ E D k := hvker
  have hvE' : ((g : G) * into D k d * (g : G)⁻¹) / into D k a ∈
      modelE.map (into D k) := by
    simpa only [modelE_map D k] using hvE
  obtain ⟨v, hv, he⟩ := hvE'
  let x := v * a
  have hxg : into D k x = (g : G) * into D k d * (g : G)⁻¹ := by
    simp only [x, map_mul, he, div_mul_cancel]
  have hxr : x.right = a.right := by
    change v.right * a.right = a.right
    change v.right = 1 at hv
    rw [hv, one_mul]
  have hx2 : x ^ 2 = 1 := by
    apply into_injective D k
    rw [map_pow, hxg, map_one]
    calc
      ((g : G) * into D k d * (g : G)⁻¹) ^ 2 =
          (g : G) * (into D k d) ^ 2 * (g : G)⁻¹ :=
            (map_pow (MulAut.conj (g : G)) _ _).symm
      _ = 1 := by
        rw [← map_pow, show d ^ 2 = 1 from by decide +kernel, map_one]
        group
  obtain ⟨v', hv'⟩ := involutions_in_Ea x hxr hx2
  refine ⟨⟨into D k (SemidirectProduct.inl v') * (g : G),
    N.mul_mem (centralizer_le_normalizer_E D k (k (SemidirectProduct.inl v')).property)
      g.property⟩, ?_⟩
  change (into D k (SemidirectProduct.inl v') * (g : G)) * into D k d *
    (into D k (SemidirectProduct.inl v') * (g : G))⁻¹ = into D k a
  calc
    _ = into D k (SemidirectProduct.inl v') * into D k x *
        (into D k (SemidirectProduct.inl v'))⁻¹ := by rw [hxg]; group
    _ = into D k a := by simpa only [map_mul, map_inv] using congrArg (into D k) hv'

end Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
