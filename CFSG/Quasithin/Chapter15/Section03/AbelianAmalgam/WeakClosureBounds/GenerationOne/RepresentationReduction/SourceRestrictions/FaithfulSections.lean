module

public import Theory.Representation.BinaryOffender.ActionImage
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.BinaryOffender.Ratio
public import Theory.GroupTheory.PerfectCentralizerLift
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.Representation.BinaryOffender.MovedSpaceTransport
public import Theory.GroupTheory.ConjugateSpanOrder


/-!
# Faithful section bounds in the representation restriction argument

The ratio-two inequality bounds the sum of the fixed codimensions on an
invariant submodule and its quotient. Either both sections are FF-modules,
or one is a strong FF-module. Passing to the actual faithful action images
requires preserving the rank of the same elementary actor on both sections.

The component-normal-subgroup dichotomy supplies this faithfulness: a kernel
on a nontrivial section centralizes the whole orbit of components. Thus an
actor faithful on the component orbit remains faithful on each section. The
full-commutator and properness hypotheses ensure nontriviality on both sections.
This handles single and exchanged components without assuming ambient normality
of the individual component. The faithful actor is still an explicit input,
as in F.9.18(2); the quadratic ratio bound alone does not provide it.

These are the linear and kernel arguments in Aschbacher--Smith, combined
manuscript (1 March 2004), F.9.18(3),(6), printed pp.325--326. They do not assert
the representation classifications in F.9.18(4),(5), B.4.2, B.4.5 or B.5.1,
nor the no-FF conclusions of 15.3.65, printed p.1152.
-/

@[expose] public section

open Representation Representation.BinaryOffender Subgroup
open scoped ENNReal

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions

variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]

/-- The kernel on a module centralizes a normal perfect subgroup if its
intersection with that subgroup is central there. -/
theorem action_kernel_le_centralizer
    (σ : Representation (ZMod 2) D V) (L : Subgroup D)
    [L.Normal] [Group.IsPerfect L]
    (hker : L ⊓ (actionHom σ).ker ≤ centralizer (L : Set D)) :
    (actionHom σ).ker ≤ centralizer (L : Set D) := by
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply commutator_eq_bot_of_iterated_eq_bot
  apply commutator_eq_bot_iff_le_centralizer.mpr
  exact (le_inf (commutator_le_right _ _) (commutator_le_left _ _)).trans hker

/-- Faithfulness on L passes to a section whose L-kernel is central. -/
theorem faithful_on_section_of_central_kernel
    (σ : Representation (ZMod 2) D V) (L A : Subgroup D)
    [L.Normal] [Group.IsPerfect L]
    (hA : A ⊓ centralizer (L : Set D) = ⊥)
    (hker : L ⊓ (actionHom σ).ker ≤ centralizer (L : Set D)) :
    ∀ a ∈ A, (∀ v, σ a v = v) → a = 1 := by
  intro a ha hv
  have hc := action_kernel_le_centralizer σ L hker
    ((actionHom_eq_one_iff σ a).mpr hv)
  exact mem_bot.mp (hA ▸ (show a ∈ A ⊓ centralizer (L : Set D) from ⟨ha, hc⟩))

/-- The ratio-two bound in integral fixed codimensions. -/
theorem actionRatio_le_two_iff [Finite D]
    (ρ : Representation (ZMod 2) D V) {A : Subgroup D} (hA : IsElementaryTwo A) :
    actionRatio ρ A ≤ 2 ↔ fixedCodim ρ A ≤ 2 * rank A := by
  have h0 : (rank A : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hA.rank_pos)
  rw [actionRatio, ENNReal.div_le_iff h0 (by simp)]
  exact_mod_cast Iff.rfl

/-- A ratio at most two supplies an actual quadratic elementary actor. -/
theorem exists_quadratic_actor_of_ratio_le_two [Finite D]
    (ρ : Representation (ZMod 2) D V) (hq : quadraticRatio ρ ≤ 2) :
    ∃ A, IsElementaryTwo A ∧ IsQuadratic ρ A ∧ fixedCodim ρ A ≤ 2 * rank A := by
  obtain ⟨A, hA, hquad, hbound⟩ := (quadraticRatio_le_iff ρ (by simp)).mp hq
  exact ⟨A, hA, hquad, (actionRatio_le_two_iff ρ hA).mp hbound⟩

/-- The fixed-codimension argument in F.9.18(6), for the original actor.
No faithfulness of the two section actions is claimed here. -/
theorem ff_alternative_of_codim_bound [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (W : Subrepresentation ρ)
    {A : Subgroup D} (hA : IsElementaryTwo A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A) :
    (IsFFModule W.toRepresentation ∧ IsFFModule W.quotientRepresentation) ∨
      IsStrongFFModule W.toRepresentation ∨ IsStrongFFModule W.quotientRepresentation := by
  have hsum := fixedCodim_quotient_add_subrepresentation_le ρ W A
  by_cases hw : fixedCodim W.toRepresentation A < rank A
  · exact Or.inr (Or.inl ⟨A, hA, hw⟩)
  by_cases hq : fixedCodim W.quotientRepresentation A < rank A
  · exact Or.inr (Or.inr ⟨A, hA, hq⟩)
  exact Or.inl ⟨⟨A, hA, by omega⟩, ⟨A, hA, by omega⟩⟩

/-- The same alternatives on the actual faithful action images. The common
actor A must be faithful on both sections, so its rank is preserved. -/
theorem faithful_image_ff_alternative [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (W : Subrepresentation ρ)
    {A : Subgroup D} (hA : IsElementaryTwo A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (hW : ∀ a ∈ A, (∀ w, W.toRepresentation a w = w) → a = 1)
    (hQ : ∀ a ∈ A, (∀ w, W.quotientRepresentation a w = w) → a = 1) :
    (IsFFModule (imageRepresentation W.toRepresentation) ∧
      IsFFModule (imageRepresentation W.quotientRepresentation)) ∨
      IsStrongFFModule (imageRepresentation W.toRepresentation) ∨
        IsStrongFFModule (imageRepresentation W.quotientRepresentation) := by
  have hsum := fixedCodim_quotient_add_subrepresentation_le ρ W A
  have hwA := hA.actionSubgroup W.toRepresentation hW
  have hqA := hA.actionSubgroup W.quotientRepresentation hQ
  have hwc := fixedCodim_actionSubgroup W.toRepresentation A
  have hqc := fixedCodim_actionSubgroup W.quotientRepresentation A
  have hwr := actionSubgroup_rank W.toRepresentation A hW
  have hqr := actionSubgroup_rank W.quotientRepresentation A hQ
  by_cases hw : fixedCodim W.toRepresentation A < rank A
  · exact Or.inr (Or.inl ⟨actionSubgroup W.toRepresentation A, hwA, by omega⟩)
  by_cases hq : fixedCodim W.quotientRepresentation A < rank A
  · exact Or.inr (Or.inr ⟨actionSubgroup W.quotientRepresentation A, hqA, by omega⟩)
  exact Or.inl ⟨⟨actionSubgroup W.toRepresentation A, hwA, by omega⟩,
    ⟨actionSubgroup W.quotientRepresentation A, hqA, by omega⟩⟩

/-- F.9.18(6)'s section argument from the actual central-kernel conditions.
Both action images are finite faithful modules when D and V are finite. -/
theorem faithful_image_ff_alternative_of_central_kernels
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (W : Subrepresentation ρ)
    (L A : Subgroup D) [L.Normal] [Group.IsPerfect L]
    (hA : IsElementaryTwo A) (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (hfaith : A ⊓ centralizer (L : Set D) = ⊥)
    (hW : L ⊓ (actionHom W.toRepresentation).ker ≤ centralizer (L : Set D))
    (hQ : L ⊓ (actionHom W.quotientRepresentation).ker ≤ centralizer (L : Set D)) :
    (IsFFModule (imageRepresentation W.toRepresentation) ∧
      IsFFModule (imageRepresentation W.quotientRepresentation)) ∨
      IsStrongFFModule (imageRepresentation W.toRepresentation) ∨
        IsStrongFFModule (imageRepresentation W.quotientRepresentation) :=
  faithful_image_ff_alternative ρ W hA hbound
    (faithful_on_section_of_central_kernel _ L A hfaith hW)
    (faithful_on_section_of_central_kernel _ L A hfaith hQ)


/-- A nontrivial action of a quasisimple subgroup has central kernel. -/
theorem central_kernel_of_quasisimple
    (σ : Representation (ZMod 2) D V) (L : Subgroup D)
    [Theory.GroupTheory.IsQuasisimple L]
    (hL : ¬ ∀ l ∈ L, ∀ v, σ l v = v) :
    L ⊓ (actionHom σ).ker ≤ centralizer (L : Set D) := by
  let N := ((actionHom σ).ker).subgroupOf L
  rcases Theory.GroupTheory.IsQuasisimple.normal_le_center_or_eq_top N with hc | ht
  · intro l hl
    have hlc : (⟨l, hl.1⟩ : L) ∈ center L := hc hl.2
    rw [mem_centralizer_iff]
    intro x hx
    exact congrArg (fun z : L => (z : D))
      ((Subgroup.mem_center_iff.mp hlc) ⟨x, hx⟩)
  · exfalso
    apply hL
    intro l hl v
    have hm : (⟨l, hl⟩ : L) ∈ N := by rw [ht]; trivial
    exact (actionHom_eq_one_iff σ l).mp hm v

/-- Nonzero full-commutator submodules have nontrivial restricted action. -/
theorem subrepresentation_action_nontrivial
    (ρ : Representation (ZMod 2) D V) (W : Subrepresentation ρ) (L : Subgroup D)
    (hW : W.toSubmodule ≠ ⊥) (hc : subspaceCommutator ρ W.toSubmodule L = W.toSubmodule) :
    ¬ ∀ l ∈ L, ∀ w, W.toRepresentation l w = w := by
  intro ht
  apply hW
  rw [← hc, subspaceCommutator_eq_bot_iff]
  intro v hv l
  exact congrArg (fun w : W => (w : V)) (ht l l.property ⟨v, hv⟩)

/-- A proper subspace of [V,L] leaves a nontrivial quotient action. -/
theorem quotient_action_nontrivial
    (ρ : Representation (ZMod 2) D V) (W : Subrepresentation ρ) (L : Subgroup D)
    (hc : subspaceCommutator ρ W.toSubmodule L = W.toSubmodule)
    (hne : W.toSubmodule ≠ subspaceCommutator ρ ⊤ L) :
    ¬ ∀ l ∈ L, ∀ w, W.quotientRepresentation l w = w := by
  intro ht
  apply hne
  apply le_antisymm
  · rw [← hc]
    exact subspaceCommutator_mono_left ρ le_top L
  · apply Submodule.span_le.mpr
    rintro _ ⟨l, hl, v, _, rfl⟩
    exact (Submodule.Quotient.eq W.toSubmodule).mp
      (ht l hl (W.toSubmodule.mkQ v))

/-- The single-quasisimple case of F.9.18(6). All section actions are
replaced by their faithful images, and the offender is required faithful on L.
The two central-kernel conditions follow from the genuine hypotheses on W. -/
theorem faithful_image_ff_alternative_of_quasisimple
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (W : Subrepresentation ρ)
    (L A : Subgroup D) [L.Normal] [Theory.GroupTheory.IsQuasisimple L]
    (hA : IsElementaryTwo A) (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (hfaith : A ⊓ centralizer (L : Set D) = ⊥)
    (hW : W.toSubmodule ≠ ⊥)
    (hc : subspaceCommutator ρ W.toSubmodule L = W.toSubmodule) :
    W.toSubmodule = subspaceCommutator ρ ⊤ L ∨
    (IsFFModule (imageRepresentation W.toRepresentation) ∧
      IsFFModule (imageRepresentation W.quotientRepresentation)) ∨
      IsStrongFFModule (imageRepresentation W.toRepresentation) ∨
        IsStrongFFModule (imageRepresentation W.quotientRepresentation) := by
  by_cases he : W.toSubmodule = subspaceCommutator ρ ⊤ L
  · exact Or.inl he
  · exact Or.inr (faithful_image_ff_alternative_of_central_kernels ρ W L A hA hbound hfaith
      (central_kernel_of_quasisimple _ L (subrepresentation_action_nontrivial ρ W L hW hc))
      (central_kernel_of_quasisimple _ L (quotient_action_nontrivial ρ W L hc he)))


/-- If neither faithful section image has a strong offender, the ratio-two
bound is sharp on both sections and on the original module. In particular
the same elementary actor induces an offender on each faithful image. -/
theorem section_codims_eq_rank_of_no_strong
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (W : Subrepresentation ρ)
    {A : Subgroup D} (hA : IsElementaryTwo A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (hW : ∀ a ∈ A, (∀ w, W.toRepresentation a w = w) → a = 1)
    (hQ : ∀ a ∈ A, (∀ w, W.quotientRepresentation a w = w) → a = 1)
    (hnW : ¬ IsStrongFFModule (imageRepresentation W.toRepresentation))
    (hnQ : ¬ IsStrongFFModule (imageRepresentation W.quotientRepresentation)) :
    fixedCodim W.toRepresentation A = rank A ∧
      fixedCodim W.quotientRepresentation A = rank A ∧
        fixedCodim ρ A = 2 * rank A ∧
          IsOffender (imageRepresentation W.toRepresentation)
            (actionSubgroup W.toRepresentation A) ∧
          IsOffender (imageRepresentation W.quotientRepresentation)
            (actionSubgroup W.quotientRepresentation A) := by
  have hsum := fixedCodim_quotient_add_subrepresentation_le ρ W A
  have hwA := hA.actionSubgroup W.toRepresentation hW
  have hqA := hA.actionSubgroup W.quotientRepresentation hQ
  have hwc := fixedCodim_actionSubgroup W.toRepresentation A
  have hqc := fixedCodim_actionSubgroup W.quotientRepresentation A
  have hwr := actionSubgroup_rank W.toRepresentation A hW
  have hqr := actionSubgroup_rank W.quotientRepresentation A hQ
  have hw : rank A ≤ fixedCodim W.toRepresentation A := by
    by_contra! h
    exact hnW ⟨actionSubgroup W.toRepresentation A, hwA, by omega⟩
  have hq : rank A ≤ fixedCodim W.quotientRepresentation A := by
    by_contra! h
    exact hnQ ⟨actionSubgroup W.quotientRepresentation A, hqA, by omega⟩
  exact ⟨by omega, by omega, by omega, ⟨hwA, by omega⟩, ⟨hqA, by omega⟩⟩


/-- If a component orbit acts nontrivially, the entire action kernel centralizes
that orbit. The component-normal-subgroup dichotomy handles every conjugate;
no ambient normality of the individual component is assumed. -/
theorem action_kernel_le_centralizer_of_component_orbit
    (σ : Representation (ZMod 2) D V) (K T : Subgroup D)
    (hK : Theory.GroupTheory.IsComponent D K)
    (hL : ¬ ∀ l ∈ conjugateSpanBy K T, ∀ v, σ l v = v) :
    (actionHom σ).ker ≤ centralizer (conjugateSpanBy K T : Set D) := by
  rcases hK.normal_dichotomy (actionHom σ).ker with hk | hk
  · exfalso
    apply hL
    have hker : conjugateSpanBy K T ≤ (actionHom σ).ker :=
      conjugateSpanBy_le hk (by rw [normalizer_eq_top]; exact le_top)
    intro l hl v
    exact (actionHom_eq_one_iff σ l).mp (hker hl) v
  · apply le_centralizer_iff.mp
    exact conjugateSpanBy_le (commutator_eq_bot_iff_le_centralizer.mp hk)
      (by rw [normalizer_eq_top]; exact le_top)

/-- F.9.18(6)'s dimension alternative for a full orbit of components,
including exchanged factors. Faithfulness of the common quadratic actor on
the orbit implies faithfulness on both nontrivial sections. -/
theorem faithful_image_ff_alternative_of_component_orbit
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (W : Subrepresentation ρ)
    (K T A : Subgroup D) (hK : Theory.GroupTheory.IsComponent D K)
    (hA : IsElementaryTwo A) (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (hfaith : A ⊓ centralizer (conjugateSpanBy K T : Set D) = ⊥)
    (hW : W.toSubmodule ≠ ⊥)
    (hc : subspaceCommutator ρ W.toSubmodule (conjugateSpanBy K T) = W.toSubmodule) :
    W.toSubmodule = subspaceCommutator ρ ⊤ (conjugateSpanBy K T) ∨
    (IsFFModule (imageRepresentation W.toRepresentation) ∧
      IsFFModule (imageRepresentation W.quotientRepresentation)) ∨
      IsStrongFFModule (imageRepresentation W.toRepresentation) ∨
        IsStrongFFModule (imageRepresentation W.quotientRepresentation) := by
  by_cases he : W.toSubmodule = subspaceCommutator ρ ⊤ (conjugateSpanBy K T)
  · exact Or.inl he
  · right
    have hwker := action_kernel_le_centralizer_of_component_orbit W.toRepresentation K T hK
      (subrepresentation_action_nontrivial ρ W _ hW hc)
    have hqker := action_kernel_le_centralizer_of_component_orbit W.quotientRepresentation K T hK
      (quotient_action_nontrivial ρ W _ hc he)
    apply faithful_image_ff_alternative ρ W hA hbound
    · intro a ha hv
      exact mem_bot.mp (hfaith ▸ (show a ∈ A ⊓ centralizer (conjugateSpanBy K T : Set D) from
        ⟨ha, hwker ((actionHom_eq_one_iff W.toRepresentation a).mpr hv)⟩))
    · intro a ha hv
      exact mem_bot.mp (hfaith ▸ (show a ∈ A ⊓ centralizer (conjugateSpanBy K T : Set D) from
        ⟨ha, hqker ((actionHom_eq_one_iff W.quotientRepresentation a).mpr hv)⟩))

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions
