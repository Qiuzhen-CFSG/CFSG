module

public import Theory.SpecificGroups.PSL5Two.UniversalCover.Presentation
public import Theory.GroupTheory.PerfectCentralCoverExistence

/-!
# Commutator lifts of the binary degree-five roots

In a central extension of PSL₅(2), choose preimages of the elementary
matrices. A root has a lift obtained by taking a commutator through a third
index. These lifts project to the specified roots and generate every perfect
central extension. This does not yet assert the Steinberg relations for the
lifts; those relations are the remaining central-extension calculation.

Source: the elementary root method for the multiplier calculation in
Aschbacher–Smith I.1.3, printed p.407, citing GLS98 §6.1.
-/

@[expose] public section

namespace Theory.SpecificGroups.PSL5Two.UniversalCover

open scoped commutatorElement

noncomputable def auxiliary (r : Root) : Fin 5 :=
  Classical.choose (Fin.exists_ne_and_ne_of_two_lt r.val.1 r.val.2 (by decide : 2 < 5))

theorem auxiliary_ne_left (r : Root) : auxiliary r ≠ r.val.1 :=
  (Classical.choose_spec
    (Fin.exists_ne_and_ne_of_two_lt r.val.1 r.val.2 (by decide : 2 < 5))).1

theorem auxiliary_ne_right (r : Root) : auxiliary r ≠ r.val.2 :=
  (Classical.choose_spec
    (Fin.exists_ne_and_ne_of_two_lt r.val.1 r.val.2 (by decide : 2 < 5))).2

variable {E : Type*} [Group E]

noncomputable def rootPreimage (f : E →* G) (hf : Function.Surjective f) (r : Root) : E :=
  Classical.choose (hf (projectiveRoot r))

@[simp] theorem rootPreimage_map (f : E →* G) (hf : Function.Surjective f) (r : Root) :
    f (rootPreimage f hf r) = projectiveRoot r := Classical.choose_spec (hf _)

/-- The lift uses two arbitrary preimages but takes their actual commutator. -/
noncomputable def rootLift (f : E →* G) (hf : Function.Surjective f) (r : Root) : E :=
  ⁅rootPreimage f hf (root r.val.1 (auxiliary r) (auxiliary_ne_left r).symm),
    rootPreimage f hf (root (auxiliary r) r.val.2 (auxiliary_ne_right r))⁆

@[simp] theorem rootLift_map (f : E →* G) (hf : Function.Surjective f) (r : Root) :
    f (rootLift f hf r) = projectiveRoot r := by
  rw [rootLift, map_commutatorElement, rootPreimage_map, rootPreimage_map]
  exact projectiveRoot_relations.chain _ _ _ _ _ r.property

/-- Any family above the twenty roots generates a perfect central extension. -/
theorem closure_range_eq_top_of_root_images [Group.IsPerfect E]
    (f : E →* G) (hker : f.ker ≤ Subgroup.center E)
    (x : Root → E) (hx : ∀ r, f (x r) = projectiveRoot r) :
    Subgroup.closure (Set.range x) = ⊤ := by
  let H := Subgroup.closure (Set.range x)
  have hmap : H.map f = ⊤ := by
    apply top_unique
    rw [← closure_range_projectiveRoot, Subgroup.closure_le]
    rintro _ ⟨r, rfl⟩
    exact ⟨x r, Subgroup.subset_closure (Set.mem_range_self r), hx r⟩
  have hcomp : Function.Surjective (f.comp H.subtype) := by
    intro g
    have hg : g ∈ H.map f := by rw [hmap]; trivial
    obtain ⟨y, hy, hfy⟩ := hg
    exact ⟨⟨y, hy⟩, hfy⟩
  have hsurj := PerfectCentralCovering.surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
    f H.subtype hcomp hker
  apply top_unique
  intro y _
  obtain ⟨z, rfl⟩ := hsurj y
  exact z.property

theorem rootLift_generates [Group.IsPerfect E]
    (f : E →* G) (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center E) :
    Subgroup.closure (Set.range (rootLift f hf)) = ⊤ :=
  closure_range_eq_top_of_root_images f hker _ (rootLift_map f hf)

/-- Faithfulness and the lifted root relations give an actual splitting
homomorphism of the specified extension. Both inputs are explicit. -/
theorem exists_section_of_faithful_of_relations
    (hinj : Function.Injective projectiveMap)
    (f : E →* G) (hf : Function.Surjective f)
    (hrel : Relations (rootLift f hf)) :
    ∃ s : G →* E, f.comp s = MonoidHom.id G := by
  let e : SteinbergGroup ≃* G := MulEquiv.ofBijective projectiveMap
    ⟨hinj, projectiveMap_surjective⟩
  have hfac : f.comp (lift hrel) = projectiveMap := by
    apply PresentedGroup.ext
    intro r
    change f (lift hrel (generator r)) = projectiveMap (generator r)
    rw [lift_generator, projectiveMap_generator, rootLift_map]
  refine ⟨(lift hrel).comp e.symm.toMonoidHom, ?_⟩
  ext g
  change f (lift hrel (e.symm g)) = g
  rw [← MonoidHom.comp_apply, hfac]
  exact e.apply_symm_apply g

/-- The splitting kills the kernel when the total group is perfect and the
kernel is central. In particular this applies to the constructed universal cover. -/
theorem ker_eq_bot_of_faithful_of_relations [Group.IsPerfect E]
    (hinj : Function.Injective projectiveMap)
    (f : E →* G) (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center E)
    (hrel : Relations (rootLift f hf)) : f.ker = ⊥ := by
  obtain ⟨s, hs⟩ := exists_section_of_faithful_of_relations hinj f hf hrel
  have hsurj : Function.Surjective s :=
    PerfectCentralCovering.surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
      f s (by rw [hs]; exact Function.surjective_id) hker
  apply (MonoidHom.ker_eq_bot_iff f).mpr
  intro x y hxy
  obtain ⟨a, rfl⟩ := hsurj x
  obtain ⟨b, rfl⟩ := hsurj y
  have hab : a = b := by
    have ha := DFunLike.congr_fun hs a
    have hb := DFunLike.congr_fun hs b
    exact ha.symm.trans (hxy.trans hb)
  rw [hab]

end Theory.SpecificGroups.PSL5Two.UniversalCover
