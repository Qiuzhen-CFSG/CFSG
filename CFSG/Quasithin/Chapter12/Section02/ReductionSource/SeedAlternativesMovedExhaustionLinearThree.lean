module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedExhaustionSuzukiFive
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionLinearThree

/-!
# The odd-degree SL₃ actor on the literal local orbit

A natural SL₃ seed of odd defining degree has no outer two-action in its
linear stabilizer. The resulting homomorphism from the original starred
actor to the component has exactly the component-centralizer kernel.
Normality and Sylow maximality put its image in the original Sylow subgroup.
Their difference centralizes the component and hence fixes the whole local
orbit W, so this same homomorphism realizes the actual action on W.

The faithful action on the seed bounds the centralizer quotient rank by
2m. This supplies the inner-action and denominator steps of the final
D.3.10 argument. The remaining support/FF exclusions, U = W and Source325
assembly stay with qt-baumann-fsu.
Source: Aschbacher--Smith D.3.19 and the proof of D.3.10, pp.203--204.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325 ChapterB.QuasisimpleSource ChapterD
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- A stabilized natural seed identifies the original cubic actor's action
on L with inner automorphisms and bounds its actual centralizer quotient. -/
theorem normalizer_starred_inner_and_rank_of_odd_linearThree
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hne : componentOrbit V (normalizer (L : Set G)) ≠ componentOrbit V (T : Subgroup G))
    (F : BinaryField) (ho : Odd F.degree)
    (e : ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) (linearNatural F 3)) :
    letI := D.normalizerOrbit_elementary h.toHypothesis1221
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let ρ := UniqueFactor.imageRepresentation M U hn
    let K := (L.subgroupOf M).map (internalHom M U hn)
    let I := internalSection U V
    ∀ A : Subgroup (internalActionImage M U hn),
      A ≤ internalSylow T M U hn D.sylow_normalizes_component → A ∈ QhatStar ρ →
      restrictedSubgroup ρ I A ≤ restrictedSubgroup ρ I K ∧
      (∀ a ∈ A, ∃ k ∈ K, ∀ l ∈ K, a*l*a⁻¹ = k*l*k⁻¹) ∧
      (∃ f : A →* K, f.ker = (centralizer (K : Set (internalActionImage M U hn))).subgroupOf A ∧
        (∀ a : A, (f a : internalActionImage M U hn) ∈
          internalSylow T M U hn D.sylow_normalizes_component) ∧
        (∀ (a : A) (l : K), a.val*l.val*a.val⁻¹ =
          (f a : internalActionImage M U hn)*l.val*(f a : internalActionImage M U hn)⁻¹) ∧
        ∀ (a : A) (v : internalSection U (componentOrbit V (T : Subgroup G))),
          ρ (f a : internalActionImage M U hn) v.val = ρ a.val v.val) ∧
      rank A ≤ rank (A ⊓ centralizer (K : Set (internalActionImage M U hn))) + 2 * F.degree ∧
      rank A - rank (A ⊓ centralizer (K : Set (internalActionImage M U hn))) ≤ 2 * F.degree := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let hn := le_normalizer_componentOrbit V M
  let ρ := UniqueFactor.imageRepresentation M U hn
  let f := internalHom M U hn
  let K := (L.subgroupOf M).map f
  let I := internalSection U V
  let : (L.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : K.Normal := Normal.map inferInstance f
    (UniqueFactor.actionHom M U hn).rangeRestrict_surjective
  let := D.normalizer_component_quasisimple h.toHypothesis1221 hc
  have hKI : K ≤ subspaceStabilizer ρ I := internalSection_stable M U V L hn D.normalizes
  obtain ⟨a,_⟩ := D.normalizer_component_actionEquiv_of_constituentModel h.toHypothesis1221
    (Or.inl ⟨F,⟨e⟩⟩)
  let b : ActionEquiv (invariantSubspace ρ K I hKI).toRepresentation (linearNatural F 3) :=
    ⟨a.groupEquiv.trans e.groupEquiv,a.linearEquiv.trans e.linearEquiv,by
      intro k v
      exact (congrArg e.linearEquiv (a.intertwines k v)).trans
        (e.intertwines (a.groupEquiv k) (a.linearEquiv v))⟩
  dsimp only
  intro A hAS hA
  have hAI := D.normalizer_starred_stabilizes_seed_of_moved_of_many h hmany hc hm hne A hAS hA
  have hAp := (internalSylow T M U hn D.sylow_normalizes_component).isPGroup'.to_le hAS
  have hr := restricted_rank_le_odd_linearThree ρ K I hKI F ho b A hAI hA.1.2.1.2
  have heq := rank_subspaceKernel_add_image ρ I A hAI hAp
  rw [(D.normalizer_sylow_seed_orbit_kernels h.toHypothesis1221 hc A hAS).1] at heq
  refine ⟨restricted_two_subgroup_le_odd_linearThree ρ K I hKI F ho b A hAp,
    inner_on_component_of_odd_linearThree ρ K I hKI
      (D.normalizer_seed_not_fixed h.toHypothesis1221 hc) F ho b A hAI hAp,?_,?_,?_⟩
  · exact exists_sylow_inner_lift_on_fixed_subspace ρ K I
      (internalSection U (componentOrbit V (T : Subgroup G))) hKI
      (D.normalizer_seed_not_fixed h.toHypothesis1221 hc) F ho b
      (internalSylow T M U hn D.sylow_normalizes_component)
      (D.normalizer_sylow_component_centralizer_fixes h.toHypothesis1221 hc).2 A hAS hAI
  · omega
  · omega

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
