module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.WordSetup
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.Enumeration

/-!
# Relabeling the explicit Fi₂₃ lift orbit

The numerical relabeling is injective by a checked left inverse. Its checked
spanning tree lowers a natural-number depth along a generator edge. Given the
two ambient pointwise intertwinings, induction on that depth puts every label
in the actual lifted subgroup orbit of 508. Given the comparisons with the
exact Fi₂₃ generators, closure induction shows the range is invariant under
the entire lifted subgroup, proving surjectivity onto that orbit. Conjugating
by the resulting equivalence gives both required permutation equalities.

The four pointwise comparisons remain explicit in the theorem below. This is
an assembly theorem, not the unconditional generator comparison. The latter
must discharge the two source-map equalities and the two ambient-word actions.
Neither faithfulness nor a point-stabilizer identification is assumed here.

Source: GLS3 Table 5.3v and `refs/KGroup/GLS3/Chapter5(sec3-).tex`, around line
1053; exact ATLAS F23G1-p31671B0 and F24G1-p306936B0 tables. Both source maps
use the inverse-left-action convention of `CycleEncoding`.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift
open Certificate

private theorem mem_suborbit_of_image_mem (g : liftedGroup) (x : Fin 306936)
    (h : g.val.val x ∈ suborbit) : x ∈ suborbit := by
  have hh := MulAction.mem_orbit_of_mem_orbit g⁻¹ h
  change g⁻¹ • (g • x) ∈ suborbit at hh
  simpa only [inv_smul_smul] using hh

private theorem membership_of_tree
    (hroot : labelMap 27192 = 508)
    (ht : ∀ i, i = 27192 ∨ (depth (parent i) < depth i ∧
      (sourceA (parent i) = i ∨ sourceA i = parent i ∨
        sourceB (parent i) = i ∨ sourceB i = parent i)))
    (ha : ∀ i, candidateA.val (labelMap i) = labelMap (sourceA i))
    (hb : ∀ i, candidateB.val (labelMap i) = labelMap (sourceB i)) :
    ∀ i, labelMap i ∈ suborbit := by
  intro i
  induction i using (measure depth).wf.induction with
  | h i ih =>
    rcases ht i with h | ⟨hd, ht⟩
    · rw [h, hroot]
      exact MulAction.mem_orbit_self _
    · have hp := ih (parent i) hd
      rcases ht with h | h | h | h
      · have hm := MulAction.mem_orbit_of_mem_orbit aLift hp
        change candidateA.val (labelMap (parent i)) ∈ suborbit at hm
        rwa [ha, h] at hm
      · apply mem_suborbit_of_image_mem aLift
        change candidateA.val (labelMap i) ∈ suborbit
        rw [ha i, h]
        exact hp
      · have hm := MulAction.mem_orbit_of_mem_orbit bLift hp
        change candidateB.val (labelMap (parent i)) ∈ suborbit at hm
        rwa [hb, h] at hm
      · apply mem_suborbit_of_image_mem bLift
        change candidateB.val (labelMap i) ∈ suborbit
        rw [hb i, h]
        exact hp


/-- The checked spanning tree places every label in the actual orbit, once
its numerical edges have been identified with the two explicit word actions. -/
theorem labelMap_mem_suborbit_of_intertwinings
    (ha : ∀ i, candidateA.val (labelMap i) = labelMap (sourceA i))
    (hb : ∀ i, candidateB.val (labelMap i) = labelMap (sourceB i)) :
    ∀ i, labelMap i ∈ suborbit :=
  membership_of_tree labelMap_root tree_step ha hb

private theorem perm_eq_permCongr {α β : Type*} (j : α ≃ β)
    (p : Equiv.Perm α) (q : Equiv.Perm β) (h : ∀ i, q (j i) = j (p i)) :
    q = j.permCongrHom p := by
  apply Equiv.ext
  intro x
  obtain ⟨i, rfl⟩ := j.surjective x
  simpa only [Equiv.permCongrHom_coe, Equiv.permCongr_apply,
    Equiv.symm_apply_apply] using h i

private theorem comparison_of_pointwise (f : Fin 31671 → Fin 306936)
    (hf : Function.Injective f) (hroot : f 27192 = 508)
    (hmem : ∀ i, f i ∈ suborbit)
    (ha : ∀ i, candidateA.val (f i) = f (Fi23.generatorA i))
    (hb : ∀ i, candidateB.val (f i) = f (Fi23.generatorB i)) :
    ∃ j : Fin 31671 ≃ Letters,
      action aLift = j.permCongrHom Fi23.generatorA ∧
      action bLift = j.permCongrHom Fi23.generatorB := by
  have hg : ∀ g ∈ liftedGroup, ∃ p : Equiv.Perm (Fin 31671),
      ∀ i, g.val (f i) = f (p i) := by
    intro g h
    induction h using Subgroup.closure_induction with
    | mem g h =>
      rcases h with rfl | rfl
      · exact ⟨Fi23.generatorA, ha⟩
      · exact ⟨Fi23.generatorB, hb⟩
    | one => exact ⟨1, fun _ => rfl⟩
    | mul g h _ _ hg hh =>
      obtain ⟨p, hp⟩ := hg
      obtain ⟨q, hq⟩ := hh
      refine ⟨p * q, fun i => ?_⟩
      change g.val (h.val (f i)) = f (p (q i))
      rw [hq, hp]
    | inv g _ hg =>
      obtain ⟨p, hp⟩ := hg
      refine ⟨p⁻¹, fun i => ?_⟩
      apply g.val.injective
      change g.val (g.val.symm (f i)) = g.val (f (p.symm i))
      rw [Equiv.apply_symm_apply, hp, Equiv.apply_symm_apply]
  let F : Fin 31671 → Letters := fun i => ⟨f i, hmem i⟩
  have hF : Function.Bijective F := by
    constructor
    · intro i j h
      exact hf (congrArg Subtype.val h)
    · intro x
      obtain ⟨g, hgx⟩ := MulAction.mem_orbit_iff.mp x.property
      obtain ⟨p, hp⟩ := hg g.val g.property
      refine ⟨p 27192, Subtype.ext ?_⟩
      change f (p 27192) = x.val
      rw [← hp, hroot]
      exact hgx
  let j := Equiv.ofBijective F hF
  have hj : ∀ i, (j i).val = f i := fun _ => rfl
  refine ⟨j, ?_, ?_⟩
  · apply perm_eq_permCongr
    intro i
    apply Subtype.ext
    rw [action_apply, hj, hj]
    exact ha i
  · apply perm_eq_permCongr
    intro i
    apply Subtype.ext
    rw [action_apply, hj, hj]
    exact hb i

/-- Assemble the generator comparison from the precise finite certificate
obligations. The inverse and spanning-tree certificates are already discharged. -/
theorem exists_generator_comparison_of_pointwise_certificates
    (hsourceA : ∀ i, Fi23.generatorA i = sourceA i)
    (hsourceB : ∀ i, Fi23.generatorB i = sourceB i)
    (hambientA : ∀ i, candidateA.val (labelMap i) = labelMap (sourceA i))
    (hambientB : ∀ i, candidateB.val (labelMap i) = labelMap (sourceB i)) :
    ∃ j : Fin 31671 ≃ Letters,
      action aLift = j.permCongrHom Fi23.generatorA ∧
      action bLift = j.permCongrHom Fi23.generatorB := by
  apply comparison_of_pointwise labelMap labelMap_injective labelMap_root
    (labelMap_mem_suborbit_of_intertwinings hambientA hambientB)
  · intro i
    rw [hsourceA]
    exact hambientA i
  · intro i
    rw [hsourceB]
    exact hambientB i

end Sporadic.Fischer.Fi24Prime.Fi23Lift
