module

public import Theory.SpecificGroups.PSL3.UniversalProjection.Basic
public import Theory.SpecificGroups.LinearHigher.Presentation

/-!
# Commutator lifts for the six degree-three roots

A root lift is the commutator of arbitrary preimages of two roots through
the third index. It has the required projective image. Centrality makes
this commutator independent of the preimages: any family satisfying the
Steinberg relations and having the specified images equals these lifts.

Faithfulness of the elementary presentation and relations for these lifts
then construct the unique homomorphism from the actual SL₃, retaining the
literal projection square. The two premises are separate mathematical
obligations, not consequences of the center computation.

Source: Steinberg, *Lectures on Chevalley Groups*, §§6–7, Theorems 9–10,
`refs/KGroup/GLS3/Chapter2St1.tex`, printed pp.74 and 80–85. The central
commutator argument also appears in the binary degree-five development
`Theory.SpecificGroups.PSL5Two.UniversalCover.LiftRelations`.
-/

@[expose] public section

namespace Matrix.PSL3.UniversalProjection

open Theory.SpecificGroups.LinearHigher
open scoped MatrixGroups commutatorElement

universe u v

variable {F : Type u} [Field F] {E : Type v} [Group E]

/-- The third coordinate outside a degree-three root. -/
noncomputable def auxiliary (r : Root 3) : Fin 3 :=
  Classical.choose (Fin.exists_ne_and_ne_of_two_lt r.val.1 r.val.2 (by decide : 2 < 3))

theorem auxiliary_ne_left (r : Root 3) : auxiliary r ≠ r.val.1 :=
  (Classical.choose_spec
    (Fin.exists_ne_and_ne_of_two_lt r.val.1 r.val.2 (by decide : 2 < 3))).1

theorem auxiliary_ne_right (r : Root 3) : auxiliary r ≠ r.val.2 :=
  (Classical.choose_spec
    (Fin.exists_ne_and_ne_of_two_lt r.val.1 r.val.2 (by decide : 2 < 3))).2

noncomputable def rootPreimage (f : E →* PSL(3, F)) (hf : Function.Surjective f)
    (r : Root 3) (a : F) : E := Classical.choose (hf (projectiveRoot r a))

@[simp] theorem rootPreimage_map (f : E →* PSL(3, F)) (hf : Function.Surjective f)
    (r : Root 3) (a : F) : f (rootPreimage f hf r a) = projectiveRoot r a :=
  Classical.choose_spec (hf _)

/-- The root lift is a commutator, not an arbitrary representative. -/
noncomputable def rootLift (f : E →* PSL(3, F)) (hf : Function.Surjective f)
    (r : Root 3) (a : F) : E :=
  ⁅rootPreimage f hf (root r.val.1 (auxiliary r) (auxiliary_ne_left r).symm) a,
    rootPreimage f hf (root (auxiliary r) r.val.2 (auxiliary_ne_right r)) 1⁆

@[simp] theorem rootLift_map (f : E →* PSL(3, F)) (hf : Function.Surjective f)
    (r : Root 3) (a : F) : f (rootLift f hf r a) = projectiveRoot r a := by
  rcases r with ⟨⟨i, j⟩, hij⟩
  rw [rootLift, map_commutatorElement, rootPreimage_map, rootPreimage_map]
  change _ = projectiveRoot (root i j hij) a
  simpa only [mul_one] using projectiveRoot_relations.chain i (auxiliary ⟨(i, j), hij⟩) j
    (auxiliary_ne_left ⟨(i, j), hij⟩).symm (auxiliary_ne_right ⟨(i, j), hij⟩) hij a (1 : F)

private theorem commutator_mul_center (z w a b : E)
    (hz : z ∈ Subgroup.center E) (hw : w ∈ Subgroup.center E) :
    ⁅z * a, w * b⁆ = ⁅a, b⁆ := by
  have hzC (x : E) : Commute z x := (Subgroup.mem_center_iff.mp hz x).symm
  have hwC (x : E) : Commute w x := (Subgroup.mem_center_iff.mp hw x).symm
  rw [commutatorElement_mul_left_eq_conj_mul, (hzC (w * b)).commutator_eq]
  simp only [mul_one, (hzC ⁅a, w * b⁆).eq, mul_inv_cancel_right]
  rw [commutatorElement_mul_right_eq_mul_conj, (hwC a).symm.commutator_eq]
  simp only [one_mul, (hwC ⁅a, b⁆).eq, mul_inv_cancel_right]

private theorem commutator_eq_of_map_eq (f : E →* PSL(3, F))
    (hc : f.ker ≤ Subgroup.center E) {a b c d : E}
    (hac : f a = f c) (hbd : f b = f d) : ⁅a, b⁆ = ⁅c, d⁆ := by
  have hz : a * c⁻¹ ∈ Subgroup.center E := hc (by simp [MonoidHom.mem_ker, hac])
  have hw : b * d⁻¹ ∈ Subgroup.center E := hc (by simp [MonoidHom.mem_ker, hbd])
  simpa only [inv_mul_cancel_right] using commutator_mul_center (a * c⁻¹) (b * d⁻¹) c d hz hw

/-- The choice of representatives imposes no extra condition: any lifted
root family satisfying the chain relations equals the commutator lifts. -/
theorem rootLift_eq_of_relations (f : E →* PSL(3, F)) (hf : Function.Surjective f)
    (hc : f.ker ≤ Subgroup.center E) (x : Root 3 → F → E)
    (hx : ∀ r a, f (x r a) = projectiveRoot r a) (hrel : Relations x)
    (r : Root 3) (a : F) : rootLift f hf r a = x r a := by
  rcases r with ⟨⟨i, j⟩, hij⟩
  unfold rootLift
  rw [commutator_eq_of_map_eq f hc
    ((rootPreimage_map _ _ _ _).trans (hx _ _).symm)
    ((rootPreimage_map _ _ _ _).trans (hx _ _).symm)]
  change _ = x (root i j hij) a
  simpa only [mul_one] using hrel.chain i (auxiliary ⟨(i, j), hij⟩) j
    (auxiliary_ne_left ⟨(i, j), hij⟩).symm (auxiliary_ne_right ⟨(i, j), hij⟩) hij a (1 : F)

/-- A root family with the right images generates any perfect central extension. -/
theorem closure_range_eq_top_of_root_images [Group.IsPerfect E]
    (f : E →* PSL(3, F)) (hc : f.ker ≤ Subgroup.center E)
    (x : Root 3 → F → E) (hx : ∀ r a, f (x r a) = projectiveRoot r a) :
    Subgroup.closure (Set.range (fun p : Root 3 × F => x p.1 p.2)) = ⊤ := by
  let H := Subgroup.closure (Set.range (fun p : Root 3 × F => x p.1 p.2))
  have hmap : H.map f = ⊤ := by
    apply top_unique
    rw [← Atlas.psl_elementary_generation (ι := Fin 3) (F := F)]
    rw [Subgroup.closure_le]
    rintro _ ⟨z, ⟨i, j, hij, a, rfl⟩, rfl⟩
    exact ⟨x (root i j hij) a, Subgroup.subset_closure
      (Set.mem_range_self (root i j hij, a)), hx _ _⟩
  have hcomp : Function.Surjective (f.comp H.subtype) := by
    intro g
    have hg : g ∈ H.map f := by rw [hmap]; trivial
    obtain ⟨y, hy, hfy⟩ := hg
    exact ⟨⟨y, hy⟩, hfy⟩
  have hsurj :=
    PerfectCentralCovering.surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
      f H.subtype hcomp hc
  apply top_unique
  intro y _
  obtain ⟨z, rfl⟩ := hsurj y
  exact z.property

theorem rootLift_generates [Group.IsPerfect E]
    (f : E →* PSL(3, F)) (hf : Function.Surjective f)
    (hc : f.ker ≤ Subgroup.center E) :
    Subgroup.closure (Set.range (fun p : Root 3 × F => rootLift f hf p.1 p.2)) = ⊤ :=
  closure_range_eq_top_of_root_images f hc _ (rootLift_map f hf)

/-- Relations give a homomorphism out of the presentation, with the exact
projective marking. No faithfulness of that presentation is used here. -/
theorem lift_fac_of_root_images (f : E →* PSL(3, F))
    (x : Root 3 → F → E) (hx : ∀ r a, f (x r a) = projectiveRoot r a)
    (hrel : Relations x) : f.comp (lift hrel) = projectiveMap := by
  apply PresentedGroup.ext
  rintro ⟨r, a⟩
  change f (lift hrel (generator r a)) = projectiveMap (generator r a)
  rw [lift_generator, projectiveMap_generator, hx]

/-- The faithful matrix presentation turns lifted root relations into an
actual unique lift from SL₃ through the specified central extension. -/
theorem existsUnique_lift_of_faithful_of_relations
    (hinj : Function.Injective (matrixMap (n := 3) (F := F)))
    (f : E →* PSL(3, F)) (hf : Function.Surjective f)
    (hc : f.ker ≤ Subgroup.center E) (hrel : Relations (rootLift f hf)) :
    ∃! s : SL(3, F) →* E, f.comp s = projection F := by
  let e : SteinbergGroup 3 F ≃* SL(3, F) :=
    MulEquiv.ofBijective matrixMap ⟨hinj, matrixMap_surjective (by decide)⟩
  let s := (lift hrel).comp e.symm.toMonoidHom
  have hs : f.comp s = projection F := by
    ext g
    change f (lift hrel (e.symm g)) = projection F g
    rw [← MonoidHom.comp_apply, lift_fac_of_root_images f _ (rootLift_map f hf),
      projectiveMap_eq]
    change projection F (e (e.symm g)) = projection F g
    rw [e.apply_symm_apply]
  exact ⟨s, hs, fun t ht => projection_lift_unique F f hc ht hs⟩

end Matrix.PSL3.UniversalProjection
