module
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.Automorphisms
public import Theory.GroupTheory.Amalgam.RankTwoCompletion
/-!
# The Tits presentation inside a faithful full Ree completion

The eight positive generators lie in the common Borel; each reflection lies
in its original marked endpoint. Erasing the absent reflection in the free
group proves all thirty-six local defining relations independently of the
concrete matrix representation. The remaining relation is exactly the
canonical eighth-power braid.

Under that explicit relation, Parrott's checked presentation gives a faithful
Tits embedding into the completion. The embedding agrees with both original
inclusions on their entire derived parabolics. Faithfulness follows from
simplicity and the nonidentity central Sylow word in the first endpoint.
The canonical braid is a separate geometric and pointed-marking obligation;
this module does not assume or assert arbitrary-completion recognition.

Source: Parrott (1972), p.683; Aschbacher--Smith F.4.15--17, pp.281--283.
-/

@[expose] public section
noncomputable section
namespace Tits.ExceptionalParabolics.FullRee.CompletionPresentation
open Theory.GroupTheory
variable {G : Type*} [Group G] (c : RankTwoAmalgam.FaithfulCompletion FullRee.amalgam (G := G))

/-- The ten marked generators in the concrete full group. -/
def modelGenerator (i : ParrottGenerator) : ReeF4.Model 0 :=
  atlasEmbedding (atlas1600ParrottAssignment i)

private theorem positive_mem_S (i : ParrottGenerator) (h1 : i ≠ .r1) (h8 : i ≠ .r8) :
    atlas1600ParrottAssignment i ∈ ExceptionalParabolics.S := by
  rw [ExceptionalParabolics.S, atlas1600SylowTwoSubgroup_eq]
  apply Subgroup.subset_closure
  cases i <;> simp_all

theorem modelGenerator_mem_B (i : ParrottGenerator) (h1 : i ≠ .r1) (h8 : i ≠ .r8) :
    modelGenerator i ∈ FullRee.B := by
  rw [borel_eq_sylow]
  exact atlas_sylow_map_le ⟨_, positive_mem_S i h1 h8, rfl⟩

theorem modelGenerator_mem_first (i : ParrottGenerator) (h8 : i ≠ .r8) :
    modelGenerator i ∈ FullRee.first := by
  by_cases h1 : i = .r1
  · subst i
    exact atlas_first_map_le ⟨_, ExceptionalParabolics.reflection_mem_first, rfl⟩
  · exact borel_le_first (modelGenerator_mem_B i h1 h8)

theorem modelGenerator_mem_second (i : ParrottGenerator) (h1 : i ≠ .r1) :
    modelGenerator i ∈ FullRee.second := by
  by_cases h8 : i = .r8
  · subst i
    exact atlas_second_map_le ⟨_, ExceptionalParabolics.reflection_mem_second, rfl⟩
  · exact borel_le_second (modelGenerator_mem_B i h1 h8)

/-- Each endpoint assignment uses a harmless identity at its absent reflection. -/
def leftAssignment (i : ParrottGenerator) : FullRee.first :=
  if h : i = .r8 then 1 else ⟨modelGenerator i, modelGenerator_mem_first i h⟩
def rightAssignment (i : ParrottGenerator) : FullRee.second :=
  if h : i = .r1 then 1 else ⟨modelGenerator i, modelGenerator_mem_second i h⟩

/-- The actual source generator assignment; positive roots use the first inclusion. -/
def sourceGenerator (i : ParrottGenerator) : G :=
  if i = .r8 then c.right (rightAssignment i) else c.left (leftAssignment i)

theorem sourceGenerator_left (i : ParrottGenerator) (h8 : i ≠ .r8) :
    sourceGenerator c i = c.left (leftAssignment i) := if_neg h8

theorem sourceGenerator_right (i : ParrottGenerator) (h1 : i ≠ .r1) :
    sourceGenerator c i = c.right (rightAssignment i) := by
  by_cases h8 : i = .r8
  · simp only [sourceGenerator, h8, ↓reduceIte]
  · rw [sourceGenerator_left c i h8]
    have h := DFunLike.congr_fun c.compatible
      ⟨modelGenerator i, modelGenerator_mem_B i h1 h8⟩
    change c.left ⟨modelGenerator i, _⟩ = c.right ⟨modelGenerator i, _⟩ at h
    simpa only [leftAssignment, rightAssignment, dif_neg h8, dif_neg h1] using h


/-- The single Parrott relation involving both endpoints. -/
def CanonicalBraid : Prop :=
  (sourceGenerator c .r1 * sourceGenerator c .r8) ^ 8 = 1

private def rightRelator : ParrottRelatorIndex → Bool
  | .i_r8 | .vi_r8_s8 | .viii_s2 | .viii_s4 | .viii_s1 | .viii_s7 | .viii_s3 | .viii_r3 => true
  | _ => false

private theorem model_relations : SatisfiesParrottRelations modelGenerator := by
  intro j
  have he : atlasEmbedding.comp (FreeGroup.lift atlas1600ParrottAssignment) =
      FreeGroup.lift modelGenerator := by
    apply FreeGroup.ext_hom
    intro i
    simp only [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
    rfl
  rw [← he, MonoidHom.comp_apply, atlas1600ParrottAssignment_relations j, map_one]

private def eraseLeft : FreeGroup ParrottGenerator →* FreeGroup ParrottGenerator :=
  FreeGroup.lift (fun i => if i = .r8 then 1 else FreeGroup.of i)
private def eraseRight : FreeGroup ParrottGenerator →* FreeGroup ParrottGenerator :=
  FreeGroup.lift (fun i => if i = .r1 then 1 else FreeGroup.of i)

private theorem eraseLeft_relator (j : ParrottRelatorIndex)
    (hj : j ≠ .vi_r1_r8) (hr : rightRelator j = false) :
    eraseLeft (parrottRelator j) = parrottRelator j := by
  cases j <;> simp only [rightRelator, Bool.true_eq_false] at hr <;> try contradiction
  all_goals simp only [parrottRelator, parrottCommutator, parrottR3, parrottR5,
    parrottR7, map_mul, map_inv, map_pow, eraseLeft, FreeGroup.lift_apply_of,
    reduceCtorEq, ↓reduceIte]

private theorem eraseRight_relator (j : ParrottRelatorIndex) (hr : rightRelator j = true) :
    eraseRight (parrottRelator j) = parrottRelator j := by
  cases j <;> simp only [rightRelator, Bool.false_eq_true] at hr <;> try contradiction
  all_goals simp only [parrottRelator, parrottR3, parrottR5,
    parrottR7, map_mul, map_inv, map_pow, eraseRight, FreeGroup.lift_apply_of,
    reduceCtorEq, ↓reduceIte]

private theorem left_assignment_lift :
    FullRee.first.subtype.comp (FreeGroup.lift leftAssignment) =
      (FreeGroup.lift modelGenerator).comp eraseLeft := by
  apply FreeGroup.ext_hom
  intro i
  by_cases hi : i = .r8
  · simp only [MonoidHom.comp_apply, eraseLeft, FreeGroup.lift_apply_of, leftAssignment,
      if_pos hi, dif_pos hi, map_one]
  · simp only [MonoidHom.comp_apply, eraseLeft, FreeGroup.lift_apply_of, leftAssignment,
      if_neg hi, dif_neg hi]
    rfl

private theorem right_assignment_lift :
    FullRee.second.subtype.comp (FreeGroup.lift rightAssignment) =
      (FreeGroup.lift modelGenerator).comp eraseRight := by
  apply FreeGroup.ext_hom
  intro i
  by_cases hi : i = .r1
  · simp only [MonoidHom.comp_apply, eraseRight, FreeGroup.lift_apply_of, rightAssignment,
      if_pos hi, dif_pos hi, map_one]
  · simp only [MonoidHom.comp_apply, eraseRight, FreeGroup.lift_apply_of, rightAssignment,
      if_neg hi, dif_neg hi]
    rfl

private theorem left_relations (j : ParrottRelatorIndex)
    (hj : j ≠ .vi_r1_r8) (hr : rightRelator j = false) :
    FreeGroup.lift leftAssignment (parrottRelator j) = 1 := by
  apply Subtype.ext
  change (FullRee.first.subtype.comp (FreeGroup.lift leftAssignment)) (parrottRelator j) = 1
  rw [left_assignment_lift, MonoidHom.comp_apply, eraseLeft_relator j hj hr, model_relations j]

private theorem right_relations (j : ParrottRelatorIndex) (hr : rightRelator j = true) :
    FreeGroup.lift rightAssignment (parrottRelator j) = 1 := by
  apply Subtype.ext
  change (FullRee.second.subtype.comp (FreeGroup.lift rightAssignment)) (parrottRelator j) = 1
  rw [right_assignment_lift, MonoidHom.comp_apply, eraseRight_relator j hr, model_relations j]

private theorem source_left_lift :
    (FreeGroup.lift (sourceGenerator c)).comp eraseLeft =
      c.left.comp (FreeGroup.lift leftAssignment) := by
  apply FreeGroup.ext_hom
  intro i
  by_cases hi : i = .r8
  · simp only [MonoidHom.comp_apply, eraseLeft, FreeGroup.lift_apply_of, leftAssignment,
      if_pos hi, dif_pos hi, map_one]
  · simp only [MonoidHom.comp_apply, eraseLeft, FreeGroup.lift_apply_of, if_neg hi]
    exact sourceGenerator_left c i hi

private theorem source_right_lift :
    (FreeGroup.lift (sourceGenerator c)).comp eraseRight =
      c.right.comp (FreeGroup.lift rightAssignment) := by
  apply FreeGroup.ext_hom
  intro i
  by_cases hi : i = .r1
  · simp only [MonoidHom.comp_apply, eraseRight, FreeGroup.lift_apply_of, rightAssignment,
      if_pos hi, dif_pos hi, map_one]
  · simp only [MonoidHom.comp_apply, eraseRight, FreeGroup.lift_apply_of, if_neg hi]
    exact sourceGenerator_right c i hi

/-- All local relations transfer through the actual inclusion maps. The only
remaining defining relation is precisely the canonical eighth-power braid. -/
theorem source_relations (hbraid : CanonicalBraid c) :
    SatisfiesParrottRelations (sourceGenerator c) := by
  intro j
  by_cases hj : j = .vi_r1_r8
  · subst j
    change (sourceGenerator c .r1 * sourceGenerator c .r8) ^ 8 = 1 at hbraid
    simpa only [parrottRelator, map_pow, map_mul, FreeGroup.lift_apply_of] using hbraid
  · by_cases hr : rightRelator j = true
    · rw [← eraseRight_relator j hr]
      change ((FreeGroup.lift (sourceGenerator c)).comp eraseRight) (parrottRelator j) = 1
      rw [source_right_lift, MonoidHom.comp_apply, right_relations j hr, map_one]
    · have hrf : rightRelator j = false := Bool.eq_false_iff.mpr hr
      rw [← eraseLeft_relator j hj hrf]
      change ((FreeGroup.lift (sourceGenerator c)).comp eraseLeft) (parrottRelator j) = 1
      rw [source_left_lift, MonoidHom.comp_apply, left_relations j hj hrf, map_one]

/-- The checked Parrott presentation gives the marked Tits map into the original completion. -/
def atlasLift (hbraid : CanonicalBraid c) : Atlas1600Group →* G :=
  (parrottLift (sourceGenerator c) (source_relations c hbraid)).comp
    parrottFiniteImageEquiv.symm.toMonoidHom

@[simp] theorem atlasLift_generator (hbraid : CanonicalBraid c) (i : ParrottGenerator) :
    atlasLift c hbraid (atlas1600ParrottAssignment i) = sourceGenerator c i := by
  have he : parrottFiniteImageEquiv.symm (atlas1600ParrottAssignment i) = parrottGenerator i := by
    apply parrottFiniteImageEquiv.injective
    rw [MulEquiv.apply_symm_apply, parrottFiniteImageEquiv_generator]
  change parrottLift _ _ (parrottFiniteImageEquiv.symm _) = _
  rw [he, parrottLift_generator]

private theorem agrees_on_closure {A M E : Type*} [Group A] [Group M] [Group E]
    (e : A →* M) (f : A →* E) (K : Subgroup M) (j : K →* E) (X : Set A)
    (hX : (Subgroup.closure X).map e ≤ K)
    (hgen : ∀ x ∈ X, ∀ hx : e x ∈ K, f x = j ⟨e x, hx⟩)
    {x : A} (hx : x ∈ Subgroup.closure X) :
    ∀ hm : e x ∈ K, f x = j ⟨e x, hm⟩ := by
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hgen x hx
  | one =>
    intro hm
    have he : (⟨e 1, hm⟩ : K) = 1 := Subtype.ext e.map_one
    rw [he, map_one, map_one]
  | mul x y hx hy ihx ihy =>
    intro hm
    have hxm : e x ∈ K := hX ⟨x, hx, rfl⟩
    have hym : e y ∈ K := hX ⟨y, hy, rfl⟩
    have he : (⟨e (x * y), hm⟩ : K) = ⟨e x, hxm⟩ * ⟨e y, hym⟩ :=
      Subtype.ext (e.map_mul x y)
    rw [he, map_mul, map_mul, ihx hxm, ihy hym]
  | inv x hx ih =>
    intro hm
    have hxm : e x ∈ K := hX ⟨x, hx, rfl⟩
    have he : (⟨e x⁻¹, hm⟩ : K) = (⟨e x, hxm⟩ : K)⁻¹ := Subtype.ext (e.map_inv x)
    rw [he, map_inv, map_inv, ih hxm]

private def positiveAtoms : Set Atlas1600Group :=
  {atlas1600ParrottAssignment .s8, atlas1600ParrottAssignment .s7,
   atlas1600ParrottAssignment .s6, atlas1600ParrottAssignment .s5,
   atlas1600ParrottAssignment .s4, atlas1600ParrottAssignment .s3,
   atlas1600ParrottAssignment .s2, atlas1600ParrottAssignment .s1}

private theorem positiveAtoms_closure : Subgroup.closure positiveAtoms = ExceptionalParabolics.S :=
  atlas1600SylowTwoSubgroup_eq.symm

private theorem lift_left_generator (hbraid : CanonicalBraid c) (i : ParrottGenerator)
    (hi : i ≠ .r8) (hm : modelGenerator i ∈ FullRee.first) :
    atlasLift c hbraid (atlas1600ParrottAssignment i) = c.left ⟨modelGenerator i, hm⟩ := by
  rw [atlasLift_generator, sourceGenerator_left c i hi]
  simp only [leftAssignment, dif_neg hi]

private theorem lift_right_generator (hbraid : CanonicalBraid c) (i : ParrottGenerator)
    (hi : i ≠ .r1) (hm : modelGenerator i ∈ FullRee.second) :
    atlasLift c hbraid (atlas1600ParrottAssignment i) = c.right ⟨modelGenerator i, hm⟩ := by
  rw [atlasLift_generator, sourceGenerator_right c i hi]
  simp only [rightAssignment, dif_neg hi]

/-- The Tits lift agrees on every element of the actual first derived parabolic. -/
theorem atlasLift_left (hbraid : CanonicalBraid c) (x : Atlas1600Group)
    (hx : x ∈ ExceptionalParabolics.first) :
    atlasLift c hbraid x = c.left ⟨atlasEmbedding x, atlas_first_map_le ⟨x, hx, rfl⟩⟩ := by
  let X := positiveAtoms ∪ {atlas1600ParrottAssignment .r1}
  have hX : Subgroup.closure X = ExceptionalParabolics.first := by
    dsimp only [X]
    rw [Subgroup.closure_union, positiveAtoms_closure]
    rfl
  apply agrees_on_closure atlasEmbedding (atlasLift c hbraid) FullRee.first c.left X
    (by rw [hX]; exact atlas_first_map_le) ?_ (hX ▸ hx)
  intro x hx hm
  rcases hx with hx | hx
  · simp only [positiveAtoms, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact lift_left_generator c hbraid _ (by decide) hm
  · obtain rfl := Set.mem_singleton_iff.mp hx
    exact lift_left_generator c hbraid _ (by decide) hm

/-- The same lift agrees with the original second inclusion, including all positive roots. -/
theorem atlasLift_right (hbraid : CanonicalBraid c) (x : Atlas1600Group)
    (hx : x ∈ ExceptionalParabolics.second) :
    atlasLift c hbraid x = c.right ⟨atlasEmbedding x, atlas_second_map_le ⟨x, hx, rfl⟩⟩ := by
  let X := positiveAtoms ∪ {atlas1600ParrottAssignment .r8}
  have hX : Subgroup.closure X = ExceptionalParabolics.second := by
    dsimp only [X]
    rw [Subgroup.closure_union, positiveAtoms_closure]
    rfl
  apply agrees_on_closure atlasEmbedding (atlasLift c hbraid) FullRee.second c.right X
    (by rw [hX]; exact atlas_second_map_le) ?_ (hX ▸ hx)
  intro x hx hm
  rcases hx with hx | hx
  · simp only [positiveAtoms, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact lift_right_generator c hbraid _ (by decide) hm
  · obtain rfl := Set.mem_singleton_iff.mp hx
    exact lift_right_generator c hbraid _ (by decide) hm

/-- The simple Tits carrier embeds; faithfulness is forced by the first local inclusion. -/
theorem atlasLift_injective (hbraid : CanonicalBraid c) :
    Function.Injective (atlasLift c hbraid) := by
  rcases (inferInstance : (atlasLift c hbraid).ker.Normal).eq_bot_or_eq_top with hk | hk
  · exact (MonoidHom.ker_eq_bot_iff _).mp hk
  · have hx : atlas1600R5 ∈ ExceptionalParabolics.first :=
      ExceptionalParabolics.sylow_le_first atlas1600R5_mem_sylowTwo
    have he : atlasLift c hbraid atlas1600R5 = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [hk]
      trivial
    rw [atlasLift_left c hbraid _ hx] at he
    have hlocal := c.left_injective (he.trans c.left.map_one.symm)
    have hmodel : atlasEmbedding atlas1600R5 = 1 := congrArg Subtype.val hlocal
    exact (atlas1600R5_ne_one (atlasEmbedding_injective (hmodel.trans atlasEmbedding.map_one.symm))).elim

end Tits.ExceptionalParabolics.FullRee.CompletionPresentation
