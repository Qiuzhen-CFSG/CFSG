module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedExhaustionCentralizer
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionQuotient

/-!
# Eliminating fixed-space supplements in the chosen normalizer action

For the literal U = componentOrbit V (normalizer L), the component image K
satisfies [U,K] = U. The Sylow orbit W is K-invariant. If U is larger than W,
the action on U/W has kernel centralizing K. Together with the checked
identity C_A(W) = C_A(K), this excludes W + C_U(A) = U for every nontrivial
A in the original Sylow image.

Consequently a starred actor that moves K has strictly smaller ratio on W
than on U. The final application chooses the actor from the original cubic
standing guard under hmany and retains precisely the centralizing-actor
branch. No nontrivial-centralizer premise is needed for this inequality.
The D.3.13--18 model/centralizer arguments, U = W, and final Source325 remain
with qt-baumann-fsu. All actions retain the literal component image and its
central cover; no special-linear group is replaced by its central quotient.
Source: Aschbacher--Smith D.3.10--19 and3.2.5, printed pp.201--204 and580.
-/

public noncomputable section
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open Chapter3.Section02.ChosenSource325 ChapterD
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual image of L generates U by its commutators, using the
original irreducible seed and all its normalizer conjugates. -/
theorem normalizer_component_fully_moved
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hc : V ⊓ centralizer (L : Set G) = ⊥) :
    letI := D.normalizerOrbit_elementary h
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let ρ := UniqueFactor.imageRepresentation M U hn
    let K := (L.subgroupOf M).map (internalHom M U hn)
    subspaceCommutator ρ ⊤ K = ⊤ := by
  let := D.normalizerOrbit_elementary h
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let hn := le_normalizer_componentOrbit V M
  let ρ := UniqueFactor.imageRepresentation M U hn
  let f := internalHom M U hn
  let K := (L.subgroupOf M).map f
  let S := internalImageSubrepresentation hn D.normalizes
  let : (L.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : K.Normal := Normal.map inferInstance f
    (UniqueFactor.actionHom M U hn).rangeRestrict_surjective
  have hi := internalImageSubrepresentation_irreducible hn D.normalizes
    (internalSubrepresentation_irreducible hn L.le_normalizer
      (le_componentOrbit V M) D.normalizes D.ne_bot (D.seed_invariant_subgroup_eq hc))
  apply fully_moved_of_irreducible_orbit ρ K S hi (D.normalizer_seed_not_fixed h hc)
  apply top_unique
  have hs := internalSection_componentOrbit_le_orbitSpan hn M le_rfl (le_componentOrbit V M)
  have hsub : orbitSpan ρ ((M.subgroupOf M).map f) (internalSection U V) ≤
      orbitSpan ρ ⊤ (internalSection U V) := by
    apply iSup_le
    intro g
    exact le_iSup (fun a : (⊤ : Subgroup (internalActionImage M U hn)) =>
      (internalSection U V).map (ρ a.val)) ⟨g.val,mem_top _⟩
  intro v _
  exact hsub (hs (show v ∈ internalSection U (componentOrbit V M) from v.toMul.property))

/-- The original component image stabilizes W inside U. -/
theorem normalizer_sylow_section_component_invariant
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) :
    letI := D.normalizerOrbit_elementary h
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let K := (L.subgroupOf M).map (internalHom M U hn)
    K ≤ subspaceStabilizer (UniqueFactor.imageRepresentation M U hn)
      (internalSection U (componentOrbit V (T : Subgroup G))) := by
  let := D.normalizerOrbit_elementary h
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let hn := le_normalizer_componentOrbit V M
  have hLW : L ≤ normalizer (componentOrbit V (T : Subgroup G) : Set G) := by
    rw [←D.orbitSpace_image]
    exact (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left).trans
      (ReducedNormal.subspaceImage_normalized _ _
        (Homogeneous.orbitSpan_invariant _ ⊤ D.space))
  exact internalSection_stable M U _ L hn hLW

/-- If U is larger than W, every component-moving starred actor in the
original Sylow image has strict ratio decrease on W. The component-centralizer
nontriviality premise of the earlier inequality is unnecessary here. -/
theorem normalizer_starred_section_strict_of_larger_orbit
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : componentOrbit V (normalizer (L : Set G)) ≠ componentOrbit V (T : Subgroup G)) :
    letI := D.normalizerOrbit_elementary h
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let W := componentOrbit V (T : Subgroup G)
    let hn := le_normalizer_componentOrbit V M
    let ρ := UniqueFactor.imageRepresentation M U hn
    let K := (L.subgroupOf M).map (internalHom M U hn)
    ∀ A : Subgroup (internalActionImage M U hn),
      A ≤ internalSylow T M U hn D.sylow_normalizes_component → A ∈ QhatStar ρ →
      ¬ A ≤ centralizer (K : Set (internalActionImage M U hn)) →
      restrictedSubgroup ρ (internalSection U W) A ∈
        Qhat (subspaceImageRepresentation ρ (internalSection U W)) ∧
      actionRatio (subspaceImageRepresentation ρ (internalSection U W))
        (restrictedSubgroup ρ (internalSection U W) A) < cubicRatio ρ := by
  let := D.normalizerOrbit_elementary h
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let W := componentOrbit V (T : Subgroup G)
  let hn := le_normalizer_componentOrbit V M
  let ρ := UniqueFactor.imageRepresentation M U hn
  let f := internalHom M U hn
  let K := (L.subgroupOf M).map f
  let : (L.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : K.Normal := Normal.map inferInstance f
    (UniqueFactor.actionHom M U hn).rangeRestrict_surjective
  let := D.normalizer_component_quasisimple h hc
  have hWU : W ≤ U := iSup_conjugates_le_of_le_normalizer V T U
    (le_componentOrbit V M) (D.sylow_normalizes_component.trans hn)
  have hproper : internalSection U W ≠ ⊤ := by
    intro he
    apply hne
    apply le_antisymm _ hWU
    intro v hv
    have hh : Additive.ofMul (⟨v,hv⟩ : U) ∈ internalSection U W := by rw [he]; trivial
    exact hh
  have hnon : ¬ internalSection U W ≤ fixedSpace ρ K := by
    intro hf
    apply D.normalizer_seed_not_fixed h hc
    exact (show internalSection U V ≤ internalSection U W from
      fun _ hv => le_componentOrbit V T hv).trans hf
  dsimp only
  intro A hAS hA hm
  exact starred_restriction_strict_of_component_quotient ρ K
    (D.normalizer_component_fully_moved h hc) (internalSection U W)
    (D.normalizer_sylow_section_component_invariant h) hnon hproper hA
    (hAS.trans (internalSylow_section_stable T M U W hn
      D.sylow_normalizes_component (le_normalizer_componentOrbit V T))) hm

/-- The proper Sylow orbit admits no fixed-space supplement for any
nontrivial subgroup of the original Sylow image. -/
theorem normalizer_sylow_no_fixed_supplement
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : componentOrbit V (normalizer (L : Set G)) ≠ componentOrbit V (T : Subgroup G)) :
    letI := D.normalizerOrbit_elementary h
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let W := componentOrbit V (T : Subgroup G)
    let hn := le_normalizer_componentOrbit V M
    let ρ := UniqueFactor.imageRepresentation M U hn
    ∀ A : Subgroup (internalActionImage M U hn),
      A ≤ internalSylow T M U hn D.sylow_normalizes_component → A ≠ ⊥ →
      internalSection U W ⊔ fixedSpace ρ A ≠ ⊤ := by
  let := D.normalizerOrbit_elementary h
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let W := componentOrbit V (T : Subgroup G)
  let hn := le_normalizer_componentOrbit V M
  let ρ := UniqueFactor.imageRepresentation M U hn
  let f := internalHom M U hn
  let K := (L.subgroupOf M).map f
  let : (L.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : K.Normal := Normal.map inferInstance f
    (UniqueFactor.actionHom M U hn).rangeRestrict_surjective
  let := D.normalizer_component_quasisimple h hc
  have hWU : W ≤ U := iSup_conjugates_le_of_le_normalizer V T U
    (le_componentOrbit V M) (D.sylow_normalizes_component.trans hn)
  have hproper : internalSection U W ≠ ⊤ := by
    intro he
    apply hne
    apply le_antisymm _ hWU
    intro v hv
    have hh : Additive.ofMul (⟨v,hv⟩ : U) ∈ internalSection U W := by rw [he]; trivial
    exact hh
  dsimp only
  intro A hAS hA
  exact no_fixed_supplement_of_component_kernel ρ
    (UniqueFactor.imageRepresentation_injective M U hn) K
    (D.normalizer_component_fully_moved h hc) (internalSection U W)
    (D.normalizer_sylow_section_component_invariant h) hproper A hA
    (hAS.trans (internalSylow_section_stable T M U W hn
      D.sylow_normalizes_component (le_normalizer_componentOrbit V T)))
    (D.normalizer_sylow_seed_orbit_kernels h hc A hAS).2

/-- The original cubic standing guard produces an actual starred actor:
it either centralizes the component or has strict ratio decrease on W.
The remaining centralizer and model exclusions stay with qt-baumann-fsu. -/
theorem exists_normalizer_starred_centralizes_or_strict_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : componentOrbit V (normalizer (L : Set G)) ≠ componentOrbit V (T : Subgroup G)) :
    letI := D.normalizerOrbit_elementary h.toHypothesis1221
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let W := componentOrbit V (T : Subgroup G)
    let hn := le_normalizer_componentOrbit V M
    let ρ := UniqueFactor.imageRepresentation M U hn
    let K := (L.subgroupOf M).map (internalHom M U hn)
    ∃ A : Subgroup (internalActionImage M U hn),
      A ≤ internalSylow T M U hn D.sylow_normalizes_component ∧ A ∈ QhatStar ρ ∧
      (A ≤ centralizer (K : Set (internalActionImage M U hn)) ∨
        (restrictedSubgroup ρ (internalSection U W) A ∈
          Qhat (subspaceImageRepresentation ρ (internalSection U W)) ∧
        actionRatio (subspaceImageRepresentation ρ (internalSection U W))
          (restrictedSubgroup ρ (internalSection U W) A) < cubicRatio ρ)) := by
  classical
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let hn := le_normalizer_componentOrbit V M
  let K := (L.subgroupOf M).map (internalHom M U hn)
  obtain ⟨A,hAS,hA,_⟩ := D.exists_normalizer_starred_in_sylow_of_many h hmany
  refine ⟨A,hAS,hA,?_⟩
  by_cases hm : A ≤ centralizer (K : Set (internalActionImage M U hn))
  · exact Or.inl hm
  · exact Or.inr (D.normalizer_starred_section_strict_of_larger_orbit
      h.toHypothesis1221 hc hne A hAS hA hm)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
