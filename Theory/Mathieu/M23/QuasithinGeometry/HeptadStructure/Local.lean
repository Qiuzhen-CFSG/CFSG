module

public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.Basic
public import Theory.Mathieu.M23.QuasithinGeometry.Actions
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Intersections in the M23 four-set stabilizer

Fixing the adjacent pairs {6,7} and {5,6} forces their common point and their
other two points to be fixed. Inside the four-set stabilizer the remaining point
is then fixed as well. Thus the two-pair intersection is precisely the pointwise
four-set kernel. The pair stabilizer also fixes each of the three parts of the
partition of the heptad of sizes 3,2,2.

Source: Aschbacher--Smith, §5.2, Lemmas 5.2.20 and 5.2.22.
-/

@[expose] public section
namespace Sporadic.Mathieu.M23Geometry
open scoped Pointwise

/-- The subgroup denoted I_x in the source, included into M23. -/
noncomputable def fourPairStabilizer : Subgroup M23 := fourStabilizer ⊓ pairStabilizer

/-- The subgroup denoted I_{x,y}, included into M23. -/
noncomputable def fourTwoPairStabilizer : Subgroup M23 :=
  fourPairStabilizer ⊓ MulAction.stabilizer M23 y.val

/-- The subgroup denoted I({x,y}), allowing the two pairs to be exchanged. -/
noncomputable def fourEdgeStabilizer : Subgroup M23 :=
  fourStabilizer ⊓ MulAction.stabilizer M23 ({x.val, y.val} : Finset (Finset (Fin 23)))

/-- The pointwise four-set kernel, included into M23. -/
noncomputable def fourKernelAmbient : Subgroup M23 :=
  (setAction lambda).ker.map fourStabilizer.subtype

theorem mem_fourKernelAmbient (g : M23) :
    g ∈ fourKernelAmbient ↔ ∀ a ∈ lambda, g • a = a :=
  mem_setAction_ker_map lambda g

private theorem fixes_subset (g : M23) {S T : Finset (Fin 23)} (hST : S ⊆ T)
    (h : ∀ a ∈ T, g • a = a) : g ∈ MulAction.stabilizer M23 S := by
  apply MulAction.mem_stabilizer_finset'.mpr
  intro a ha
  rwa [h a (hST ha)]

/-- The pointwise four-set kernel fixes both source pairs. -/
theorem fourKernelAmbient_le_twoPair : fourKernelAmbient ≤ fourTwoPairStabilizer := by
  intro g hg
  have h := (mem_fourKernelAmbient g).mp hg
  exact ⟨⟨fixes_subset g (Finset.Subset.refl _) h, fixes_subset g x_subset_lambda h⟩,
    fixes_subset g y_subset_lambda h⟩

/-- The two-pair intersection is exactly the pointwise four-set kernel. -/
theorem fourTwoPairStabilizer_eq_kernel : fourTwoPairStabilizer = fourKernelAmbient := by
  apply le_antisymm _ fourKernelAmbient_le_twoPair
  intro g hg
  rcases hg with ⟨⟨hI, hx⟩, hy⟩
  apply (mem_fourKernelAmbient g).mpr
  have hxs : g • x.val = x.val := MulAction.mem_stabilizer_iff.mp hx
  have hys : g • y.val = y.val := MulAction.mem_stabilizer_iff.mp hy
  have hIs : g • lambda = lambda := MulAction.mem_stabilizer_iff.mp hI
  have h11 : g • (11 : Fin 23) = 11 := by
    have h : g • (x.val ∩ y.val) = x.val ∩ y.val := by
      rw [Finset.smul_finset_inter, hxs, hys]
    have he : x.val ∩ y.val = {11} := by decide +kernel
    simpa only [he, Finset.smul_finset_singleton, Finset.singleton_inj] using h
  have h17 : g • (17 : Fin 23) = 17 := by
    have h : g • (x.val \ y.val) = x.val \ y.val := by
      rw [Finset.smul_finset_sdiff, hxs, hys]
    have he : x.val \ y.val = {17} := by decide +kernel
    simpa only [he, Finset.smul_finset_singleton, Finset.singleton_inj] using h
  have h5 : g • (5 : Fin 23) = 5 := by
    have h : g • (y.val \ x.val) = y.val \ x.val := by
      rw [Finset.smul_finset_sdiff, hxs, hys]
    have he : y.val \ x.val = {5} := by decide +kernel
    simpa only [he, Finset.smul_finset_singleton, Finset.singleton_inj] using h
  have h4 : g • (4 : Fin 23) = 4 := by
    have h : g • (lambda \ (x.val ∪ y.val)) = lambda \ (x.val ∪ y.val) := by
      rw [Finset.smul_finset_sdiff, Finset.smul_finset_union, hxs, hys, hIs]
    have he : lambda \ (x.val ∪ y.val) = {4} := by decide +kernel
    simpa only [he, Finset.smul_finset_singleton, Finset.singleton_inj] using h
  intro a ha
  have he : lambda = {4, 5, 11, 17} := by decide +kernel
  simp only [he, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · exact h4
  · exact h5
  · exact h11
  · exact h17

/-- The heptad kernel is contained in the two-pair intersection. -/
theorem heptadKernelAmbient_le_twoPair : heptadKernelAmbient ≤ fourTwoPairStabilizer := by
  rw [fourTwoPairStabilizer_eq_kernel]
  intro g hg
  exact (mem_fourKernelAmbient g).mpr (fun a ha =>
    (mem_heptadKernelAmbient g).mp hg a (lambda_subset_omega ha))

/-- Stabilizing x inside I is equivalent to fixing each part of the source
partition. The two parts of size two are fixed individually. -/
theorem mem_fourPairStabilizer_iff_partition (g : M23) :
    g ∈ fourPairStabilizer ↔ g ∈ heptadStabilizer ∧
      g • (omega \ lambda) = omega \ lambda ∧
      g • (lambda \ x.val) = lambda \ x.val ∧ g • x.val = x.val := by
  constructor
  · rintro ⟨hI, hx⟩
    have hH := fourStabilizer_le hI
    have hIs := MulAction.mem_stabilizer_iff.mp hI
    have hxs := MulAction.mem_stabilizer_iff.mp hx
    refine ⟨hH, ?_, ?_, hxs⟩
    · rw [Finset.smul_finset_sdiff, MulAction.mem_stabilizer_iff.mp hH, hIs]
    · rw [Finset.smul_finset_sdiff, hIs, hxs]
  · rintro ⟨_, _, hdiff, hx⟩
    refine ⟨MulAction.mem_stabilizer_iff.mpr ?_, MulAction.mem_stabilizer_iff.mpr hx⟩
    have hrecover : x.val ∪ (lambda \ x.val) = lambda :=
      Finset.union_sdiff_of_subset x_subset_lambda
    calc
      g • lambda = g • (x.val ∪ (lambda \ x.val)) := congrArg (g • ·) hrecover.symm
      _ = x.val ∪ (lambda \ x.val) := by rw [Finset.smul_finset_union, hx, hdiff]
      _ = lambda := hrecover

/-- Order the four points along a path whose middle edge exchanges x and y. -/
private def generationLabel : Fin 4 ↪ Fin 23 where
  toFun := ![4, 5, 17, 11]
  inj' := by decide +kernel

private noncomputable def generationEquiv : Fin 4 ≃ lambda :=
  Equiv.ofBijective (fun i => ⟨generationLabel i, by
    fin_cases i <;> decide +kernel⟩) (by
    constructor
    · intro i j h
      exact generationLabel.injective (congrArg Subtype.val h)
    · intro a
      have ha : a.val ∈ Finset.univ.image generationLabel := by
        have h : Finset.univ.image generationLabel = lambda := by decide +kernel
        simpa only [h] using a.property
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ha
      exact ⟨i, Subtype.ext hi⟩)

private noncomputable def generationAction : fourStabilizer →* Equiv.Perm (Fin 4) :=
  generationEquiv.symm.permCongrHom.toMonoidHom.comp (setAction lambda)

private theorem generationAction_apply (g : fourStabilizer) (i : Fin 4) :
    generationLabel (generationAction g i) = (g : M23) • generationLabel i := by
  change (generationEquiv
    (generationEquiv.symm (setAction lambda g (generationEquiv i)))).val = _
  rw [generationEquiv.apply_symm_apply]
  rfl

private theorem generationAction_surjective : Function.Surjective generationAction :=
  generationEquiv.symm.permCongrHom.surjective.comp lambda_action_surjective

private theorem adjacentSwap_lift (i : Fin 3) :
    ∃ g : fourStabilizer, generationAction g = Equiv.swap i.castSucc i.succ ∧
      (g : M23) ∈ fourPairStabilizer ⊔ fourEdgeStabilizer := by
  obtain ⟨g, hg⟩ := generationAction_surjective (Equiv.swap i.castSucc i.succ)
  refine ⟨g, hg, ?_⟩
  have happ (j : Fin 4) : (g : M23) • generationLabel j =
      generationLabel (Equiv.swap i.castSucc i.succ j) := by
    rw [← generationAction_apply, hg]
  fin_cases i
  · apply Subgroup.mem_sup_left
    refine ⟨g.property, MulAction.mem_stabilizer_iff.mpr ?_⟩
    have h11 : (g : M23) • (11 : Fin 23) = 11 := by simpa [generationLabel, Equiv.swap_apply_def] using happ 3
    have h17 : (g : M23) • (17 : Fin 23) = 17 := by simpa [generationLabel, Equiv.swap_apply_def] using happ 2
    change (g : M23) • ({11, 17} : Finset (Fin 23)) = {11, 17}
    simp only [Finset.smul_finset_insert, Finset.smul_finset_singleton, h11, h17]
  · apply Subgroup.mem_sup_right
    refine ⟨g.property, MulAction.mem_stabilizer_iff.mpr ?_⟩
    have h11 : (g : M23) • (11 : Fin 23) = 11 := by simpa [generationLabel, Equiv.swap_apply_def] using happ 3
    have h17 : (g : M23) • (17 : Fin 23) = 5 := by simpa [generationLabel, Equiv.swap_apply_def] using happ 2
    have h5 : (g : M23) • (5 : Fin 23) = 17 := by simpa [generationLabel, Equiv.swap_apply_def] using happ 1
    have hx : (g : M23) • x.val = y.val := by
      change (g : M23) • ({11, 17} : Finset (Fin 23)) = {5, 11}
      simp only [Finset.smul_finset_insert, Finset.smul_finset_singleton, h11, h17]
      decide +kernel
    have hy : (g : M23) • y.val = x.val := by
      change (g : M23) • ({5, 11} : Finset (Fin 23)) = {11, 17}
      simp only [Finset.smul_finset_insert, Finset.smul_finset_singleton, h5, h11]
      decide +kernel
    simp only [Finset.smul_finset_insert, Finset.smul_finset_singleton, hx, hy,
      Finset.pair_comm]
  · apply Subgroup.mem_sup_left
    refine ⟨g.property, MulAction.mem_stabilizer_iff.mpr ?_⟩
    have h11 : (g : M23) • (11 : Fin 23) = 17 := by simpa [generationLabel, Equiv.swap_apply_def] using happ 3
    have h17 : (g : M23) • (17 : Fin 23) = 11 := by simpa [generationLabel, Equiv.swap_apply_def] using happ 2
    change (g : M23) • ({11, 17} : Finset (Fin 23)) = {11, 17}
    simp only [Finset.smul_finset_insert, Finset.smul_finset_singleton, h11, h17]
    decide +kernel

/-- Lemma 5.2.22 for the actual M23 subgroups, with their ambient inclusions. -/
theorem fourStabilizer_generated :
    fourPairStabilizer ⊔ fourEdgeStabilizer = fourStabilizer := by
  let J := fourPairStabilizer ⊔ fourEdgeStabilizer
  have hJI : J ≤ fourStabilizer := sup_le inf_le_left inf_le_left
  let K : Subgroup fourStabilizer := J.comap fourStabilizer.subtype
  have hker : generationAction.ker ≤ K := by
    intro g hg
    have he : generationAction.ker = (setAction lambda).ker :=
      MonoidHom.ker_mulEquiv_comp (setAction lambda) generationEquiv.symm.permCongrHom
    rw [he] at hg
    have hk : (g : M23) ∈ fourKernelAmbient := Subgroup.mem_map.mpr ⟨g, hg, rfl⟩
    exact (le_sup_left : fourPairStabilizer ≤ J) (fourKernelAmbient_le_twoPair hk).1
  have hmap : K.map generationAction = ⊤ := by
    apply top_unique
    have hm : (⊤ : Submonoid (Equiv.Perm (Fin 4))) ≤
        (K.map generationAction).toSubmonoid := by
      rw [← Equiv.Perm.mclosure_swap_castSucc_succ 3]
      apply Submonoid.closure_le.mpr
      rintro _ ⟨i, rfl⟩
      obtain ⟨g, hg, hJ⟩ := adjacentSwap_lift i
      exact Subgroup.mem_map.mpr ⟨g, hJ, hg⟩
    exact hm
  have hK : K = ⊤ := by
    apply Subgroup.map_injective_of_ker_le generationAction hker le_top
    rw [hmap, ← MonoidHom.range_eq_map, generationAction.range_eq_top_of_surjective
      generationAction_surjective]
  apply le_antisymm hJI
  intro g hg
  have : (⟨g, hg⟩ : fourStabilizer) ∈ K := by rw [hK]; trivial
  exact this

end Sporadic.Mathieu.M23Geometry
