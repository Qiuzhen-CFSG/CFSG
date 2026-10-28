module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.Alternating.ProperComponents.NonprimitiveRecognition.OrbitImages
public import Mathlib.GroupTheory.GroupAction.Primitive

/-!
# The literal block actions in the alternating imprimitive reduction

A nontrivial block supplies a system of translates and a permutation action
on that system. Its kernel restricts to each individual block, and these
restrictions jointly separate elements. Thus centerless component images
recover actual component isomorphisms, not just central quotients.

Source: Aschbacher–Smith B.1.13, printed p.74 (PDF p.85), final paragraph.
The kernel restriction construction follows the independent section argument
in `MainConverse/AlternatingSections/SymmetricEight/Nonprimitive.lean`.
-/

public section
open Subgroup MulAction Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups

variable {m : ℕ} (X : Subgroup (alternatingGroup (Fin m)))

theorem alternating_exists_nontrivial_block
    [IsPretransitive X (Fin m)] (hp : ¬ IsPreprimitive X (Fin m)) :
    ∃ B : Set (Fin m), IsBlock X B ∧ ¬ B.Subsingleton ∧ B ≠ Set.univ := by
  by_contra! h
  apply hp
  refine { isTrivialBlock_of_isBlock := ?_ }
  intro B hB
  by_cases hBs : B.Subsingleton
  · exact Or.inl hBs
  · exact Or.inr (h B hB (by simpa using hBs))

/-- The block-system action uses the actual translates of the chosen subset. -/
@[expose] def alternatingBlockAction (B : Set (Fin m)) :
    X →* Equiv.Perm (orbit X B) := toPermHom X (orbit X B)

abbrev alternatingBlockKernel (B : Set (Fin m)) :=
  (alternatingBlockAction X B).ker

theorem alternatingBlockKernel_fixes (B : Set (Fin m))
    (k : alternatingBlockKernel X B) (C : orbit X B) :
    (k : X) • C.val = C.val :=
  congrArg (fun p : Equiv.Perm (orbit X B) => (p C).val) k.property

/-- Restriction of a kernel element to one block; no arbitrary product
ambient or ambient normality of a component is asserted. -/
@[expose] def alternatingBlockRestriction (B : Set (Fin m)) (C : orbit X B) :
    alternatingBlockKernel X B →* Equiv.Perm C.val where
  toFun k := (toPerm (k : X)).subtypePerm (fun x => by
    change (k : X) • x ∈ C.val ↔ x ∈ C.val
    calc
      (k : X) • x ∈ C.val ↔ (k : X) • x ∈ (k : X) • C.val := by
        rw [alternatingBlockKernel_fixes]
      _ ↔ x ∈ C.val := Set.smul_mem_smul_set_iff)
  map_one' := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    exact one_smul X x.val
  map_mul' k l := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    exact mul_smul (k : X) (l : X) x.val

abbrev alternatingBlockImage (B : Set (Fin m)) (C : orbit X B) :=
  (alternatingBlockRestriction X B C).range

@[expose] def alternatingBlockProjection (B : Set (Fin m)) (C : orbit X B) :
    alternatingBlockKernel X B →* alternatingBlockImage X B C :=
  (alternatingBlockRestriction X B C).rangeRestrict

theorem alternatingBlockProjection_surjective (B : Set (Fin m)) (C : orbit X B) :
    Function.Surjective (alternatingBlockProjection X B C) :=
  (alternatingBlockRestriction X B C).rangeRestrict_surjective

theorem alternatingBlockProjection_separates [IsPretransitive X (Fin m)]
    {B : Set (Fin m)} (hB : B.Nonempty) (k : alternatingBlockKernel X B)
    (hk : ∀ C, alternatingBlockProjection X B C k = 1) : k = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro x
  obtain ⟨b, hb⟩ := hB
  obtain ⟨g, hg⟩ := exists_smul_eq X b x
  let C : orbit X B := ⟨g • B, mem_orbit B g⟩
  have hx : x ∈ C.val := ⟨b, hb, hg⟩
  exact congrArg (fun p : alternatingBlockImage X B C => (p.val ⟨x, hx⟩).val) (hk C)

/-- The kernel really embeds in the product of the block permutation groups. -/
@[expose] def alternatingBlockKernelEmbedding (B : Set (Fin m)) :
    alternatingBlockKernel X B →* (∀ C : orbit X B, Equiv.Perm C.val) where
  toFun k C := alternatingBlockRestriction X B C k
  map_one' := by funext C; exact (alternatingBlockRestriction X B C).map_one
  map_mul' k l := by funext C; exact (alternatingBlockRestriction X B C).map_mul k l

theorem alternatingBlockKernelEmbedding_injective [IsPretransitive X (Fin m)]
    {B : Set (Fin m)} (hB : B.Nonempty) :
    Function.Injective (alternatingBlockKernelEmbedding X B) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro k hk
  apply mem_bot.mpr
  apply alternatingBlockProjection_separates X hB k
  intro C
  apply Subtype.ext
  exact congrFun (MonoidHom.mem_ker.mp hk) C

theorem alternatingBlock_isBlockSystem [IsPretransitive X (Fin m)]
    {B : Set (Fin m)} (hB : IsBlock X B) (hne : B.Nonempty) :
    IsBlockSystem X (orbit X B) := by
  exact hB.isBlockSystem hne

theorem alternatingBlock_card_eq {B : Set (Fin m)} (C : orbit X B) :
    Nat.card C.val = Nat.card B := by
  obtain ⟨g, hg⟩ := C.property
  change C.val.ncard = B.ncard
  rw [← hg, Set.ncard_smul_set]

theorem alternatingBlock_degrees [IsPretransitive X (Fin m)]
    {B : Set (Fin m)} (hB : IsBlock X B) (hBs : ¬ B.Subsingleton)
    (hBu : B ≠ Set.univ) :
    2 ≤ Nat.card B ∧ Nat.card B < m ∧ Nat.card (orbit X B) < m := by
  have htwo : 2 ≤ B.ncard := by
    have : ¬ B.ncard ≤ 1 := by simpa only [Set.ncard_le_one_iff_subsingleton] using hBs
    omega
  have hne : B.Nonempty := (Set.ncard_pos (Set.toFinite B)).mp (by omega)
  have hlt : Nat.card B < m := by
    change B.ncard < m
    simpa only [Nat.card_fin] using Set.ncard_lt_card hBu
  have hmul := hB.ncard_block_mul_ncard_orbit_eq hne
  simp only [Nat.card_fin] at hmul
  exact ⟨htwo, hlt, by change (orbit X B).ncard < m; nlinarith⟩

/-- Classified images in all literal block restrictions remove the central
kernels and classify each component of the block kernel. -/
theorem alternating_block_kernel_component_models [IsPretransitive X (Fin m)]
    {B : Set (Fin m)} (hB : B.Nonempty)
    (hmodels : ∀ C : orbit X B, ∀ E : Subgroup (alternatingBlockImage X B C),
      IsComponent (alternatingBlockImage X B C) E → AlternatingSubgroupModels m E)
    (D : Subgroup (alternatingBlockKernel X B)) (hD : IsComponent _ D) :
    AlternatingSubgroupModels m D := by
  have hcenter : ∀ C, center (D.map (alternatingBlockProjection X B C)) = ⊥ := by
    intro C
    rcases hD.map_surjective (alternatingBlockProjection X B C)
        (alternatingBlockProjection_surjective X B C) with hb | hc
    · rw [hb]
      exact (center (⊥ : Subgroup (alternatingBlockImage X B C))).eq_bot_of_subsingleton
    · let := hc.2
      let E := D.map (alternatingBlockProjection X B C)
      let : IsSimpleGroup (E ⧸ center E) := IsQuasisimple.simple
      let : Nontrivial E := (QuotientGroup.mk'_surjective (center E)).nontrivial
      exact alternating_models_center_eq_bot (hmodels C _ hc)
  obtain ⟨C, hC, ⟨e⟩⟩ := hD.exists_equiv_image_of_separating_homs
    (alternatingBlockProjection X B) (alternatingBlockProjection_surjective X B)
    (alternatingBlockProjection_separates X hB) hcenter
  exact (hmodels C _ hC).of_mulEquiv e

/-- A component contained in the kernel remains a relative component there;
normality of the component in the original overgroup is not needed. -/
theorem alternating_component_models_of_block_kernel [IsPretransitive X (Fin m)]
    {B : Set (Fin m)} (hB : B.Nonempty)
    (hmodels : ∀ C : orbit X B, ∀ E : Subgroup (alternatingBlockImage X B C),
      IsComponent (alternatingBlockImage X B C) E → AlternatingSubgroupModels m E)
    (D : Subgroup X) (hD : IsComponent X D) (hle : D ≤ alternatingBlockKernel X B) :
    AlternatingSubgroupModels m D :=
  (alternating_block_kernel_component_models X hB hmodels
    (D.subgroupOf (alternatingBlockKernel X B)) (hD.subgroupOf hle)).of_mulEquiv
      (subgroupOfEquivOfLe hle).symm

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups
