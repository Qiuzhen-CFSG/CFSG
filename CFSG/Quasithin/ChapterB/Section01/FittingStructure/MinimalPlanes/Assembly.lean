module

public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.MinimalPlanes.Reduction
public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.MinimalPlanes.SolvableRecognition
public import Theory.Representation.BinaryGroupAction


/-!
# Recovering the original minimal Fitting plane

This proves the implication from the explicit `SourceReduction` contract to
all seven fields of `MinimalFittingPlane`. Genuine B.1.5 restriction gives a
minimal offender on the faithful solvable action image. B.1.8 gives equality
of rank and fixed codimension, so B.1.5 eliminates the kernel in A and splits
V as W+C_V(A). Since W lies in C_V(B), B is trivial. Thus W is the original
Fitting support, and the recorded relative kernel makes H faithful on it.
Normal generation selects one actual S₃ factor. Coprime support generation
gives its two-dimensional module, and oddness identifies F_A's order as three.

The implication is conditional: the source action reduction still has to be
constructed from the original faithful action and trivial ambient two-core.
Source: Aschbacher–Smith, B.1.9 proof, first paragraph,
printed p.71 (PDF p.82), combined 1 March 2004 manuscript.
-/

public section

namespace CFSG.Quasithin.ChapterB.FittingStructure.MinimalPlanes
open Subgroup Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

private theorem moved_comp_subtype (H X : Subgroup G) (hX : X ≤ H)
    (U : Submodule (ZMod 2) V) :
    subspaceCommutator (ρ.comp H.subtype) U (X.subgroupOf H) =
      subspaceCommutator ρ U X := by
  unfold subspaceCommutator
  apply congrArg (Submodule.span (ZMod 2))
  ext v
  constructor
  · rintro ⟨x, hx, w, hw, rfl⟩
    exact ⟨x, hx, w, hw, rfl⟩
  · rintro ⟨x, hx, w, hw, rfl⟩
    exact ⟨⟨x, hX hx⟩, hx, w, hw, rfl⟩

variable [Finite G] [FiniteDimensional (ZMod 2) V]

/-- Restriction and solvable rank equality give faithfulness on W and the
fixed-space supplement, with all actors transported through actual images. -/
theorem SourceReduction.restriction {A : Subgroup G}
    (d : SourceReduction ρ A) (hf : Function.Injective ρ)
    (hA : IsMinimalBestOffender ρ A) :
    IsMinimalBestOffender
      (subspaceImageRepresentation (localRepresentation ρ A) (testSpace ρ A))
      (restrictedSubgroup (localRepresentation ρ A) (testSpace ρ A) (localActor A)) ∧
    (∀ a ∈ A, (∀ w ∈ testSpace ρ A, ρ a w = w) → a = 1) ∧
    testSpace ρ A ⊔ fixedSpace ρ A = ⊤ := by
  let σ := localRepresentation ρ A
  let W := testSpace ρ A
  have hmin : IsMinimalBestOffender σ (localActor A) :=
    minimal_subgroupOf ρ hA le_sup_right
  have hσ : Function.Injective σ := hf.comp (localGroup A).subtype_injective
  obtain ⟨hm, hend⟩ := source_lemma_B_7_1_2 σ W hσ hmin
    (fun a _ w hw => (d.stable (mem_top a) w).2 hw) d.moving
  obtain ⟨f⟩ := solvableFFStructure_nonempty
    (subspaceImageRepresentation σ W) d.image_solvable d.image_core
    (subspaceImageRepresentation_injective σ W) ⟨_, hm.1.isOffender _⟩
  obtain ⟨ha, hs⟩ := hend (f.best_rank_eq _ hm.1).symm
  refine ⟨hm, ?_, ?_⟩
  · intro a haA hfix
    exact congrArg Subtype.val (ha ⟨a, (show A ≤ localGroup A from le_sup_right) haA⟩ haA hfix)
  · change W ⊔ fixedSpace (ρ.comp (localGroup A).subtype)
      (A.subgroupOf (localGroup A)) = ⊤ at hs
    rw [fixedSpace_comp_map, map_subgroupOf_eq_of_le (show A ≤ localGroup A from le_sup_right)] at hs
    exact hs

/-- Minimality eliminates the actual centralizer B=C_A(F_A). -/
theorem SourceReduction.kernelActor_eq_bot {A : Subgroup G}
    (d : SourceReduction ρ A) (hf : Function.Injective ρ)
    (hA : IsMinimalBestOffender ρ A) : kernelActor A = ⊥ := by
  apply bot_unique
  intro a ha
  exact (d.restriction ρ hf hA).2.1 a ha.1
    (fun w hw => d.fixed hw ⟨a, ha⟩)

/-- After eliminating B, the test space is the original Fitting support. -/
theorem SourceReduction.testSpace_eq {A : Subgroup G}
    (d : SourceReduction ρ A) (hf : Function.Injective ρ)
    (hA : IsMinimalBestOffender ρ A) :
    testSpace ρ A = subspaceCommutator ρ ⊤ (oddPart A) := by
  unfold testSpace
  rw [d.kernelActor_eq_bot ρ hf hA, fixedSpace_bot]

/-- The relative kernel equality recovers faithfulness of the whole H on W. -/
theorem SourceReduction.faithful {A : Subgroup G}
    (d : SourceReduction ρ A) (hf : Function.Injective ρ)
    (hA : IsMinimalBestOffender ρ A) (g : localGroup A)
    (hg : ∀ w ∈ testSpace ρ A, ρ g w = w) : g = 1 := by
  have hm : g ∈ subspaceKernel (localRepresentation ρ A) (testSpace ρ A) ⊤ :=
    ⟨mem_top g, hg⟩
  rw [d.kernel, d.kernelActor_eq_bot ρ hf hA] at hm
  exact Subtype.ext (mem_bot.mp hm)

private noncomputable def wholeActionHom {A : Subgroup G} (d : SourceReduction ρ A) :
    localGroup A →* testImage ρ A :=
  (subgroupActionHom (localRepresentation ρ A) (testSpace ρ A) ⊤ d.stable).comp
    Subgroup.topEquiv.symm.toMonoidHom

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem wholeActionHom_surjective {A : Subgroup G} (d : SourceReduction ρ A) :
    Function.Surjective (wholeActionHom ρ d) := by
  intro x
  obtain ⟨g, rfl⟩ :=
    (stabilizerRepresentation (localRepresentation ρ A) (testSpace ρ A)).asGroupHom.rangeRestrict_surjective x
  exact ⟨g, rfl⟩

private theorem wholeActionHom_injective {A : Subgroup G} (d : SourceReduction ρ A)
    (hf : Function.Injective ρ) (hA : IsMinimalBestOffender ρ A) :
    Function.Injective (wholeActionHom ρ d) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro g hg
  apply d.faithful ρ hf hA g
  intro w hw
  have he := congrArg (fun x =>
    subspaceImageRepresentation (localRepresentation ρ A) (testSpace ρ A) x ⟨w, hw⟩) hg
  exact congrArg Subtype.val he

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem image_moved_eq_top {A : Subgroup G} (d : SourceReduction ρ A) :
    subspaceCommutator
      (subspaceImageRepresentation (localRepresentation ρ A) (testSpace ρ A)) ⊤ ⊤ = ⊤ := by
  let σ := localRepresentation ρ A
  let W := testSpace ρ A
  let F := (oddPart A).subgroupOf (localGroup A)
  have he : subspaceCommutator σ W F = W :=
    (moved_comp_subtype ρ (localGroup A) (oddPart A) le_sup_left W).trans d.self_moved
  have hc := restricted_commutator_eq_top σ W F (le_top.trans d.stable) he
  apply top_unique
  calc
    ⊤ = subspaceCommutator (subspaceImageRepresentation σ W) ⊤
      (restrictedSubgroup σ W F) := hc.symm
    _ ≤ _ := ?_
  apply Submodule.span_mono
  rintro _ ⟨g, _, w, hw, rfl⟩
  exact ⟨g, mem_top g, w, hw, rfl⟩

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem moved_sup (X A : Subgroup G) :
    subspaceCommutator ρ ⊤ (X ⊔ A) =
      subspaceCommutator ρ ⊤ X ⊔ subspaceCommutator ρ ⊤ A := by
  simpa [iSup_bool_eq] using
    (Representation.BinaryGroupAction.moved_iSup ρ (fun b : Bool => if b then X else A))

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem moved_le_of_span_fixed {A : Subgroup G} {W : Submodule (ZMod 2) V}
    (hs : A ≤ subspaceStabilizer ρ W) (hspan : W ⊔ fixedSpace ρ A = ⊤) :
    subspaceCommutator ρ ⊤ A ≤ W := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a, ha, v, _, rfl⟩
  have hv : v ∈ W ⊔ fixedSpace ρ A := hspan ▸ Submodule.mem_top
  obtain ⟨w, hw, c, hc, rfl⟩ := Submodule.mem_sup.mp hv
  have hca : ρ a c = c := hc ⟨a, ha⟩
  rw [map_add, hca, add_sub_add_right_eq_sub]
  exact W.sub_mem ((hs ha w).2 hw) hw

/-- Assemble every local-plane conclusion from the source action reduction.
Construction of that reduction remains a separate, explicit obligation. -/
theorem minimalFittingPlane_of_reduction {A : Subgroup G}
    (hf : Function.Injective ρ) (hA : IsMinimalBestOffender ρ A)
    (hne : oddPart A ≠ ⊥) (d : SourceReduction ρ A) :
    Nonempty (MinimalFittingPlane ρ A) := by
  let σ := localRepresentation ρ A
  let W := testSpace ρ A
  let τ := subspaceImageRepresentation σ W
  obtain ⟨hm, hfaithA, hspan⟩ := d.restriction ρ hf hA
  obtain ⟨hcardA, ⟨model⟩, hdim⟩ := solvable_minimal_normally_generating τ
    d.image_solvable d.image_core (subspaceImageRepresentation_injective σ W)
    hm d.image_generated
  have hW : W = subspaceCommutator ρ ⊤ (oddPart A) := d.testSpace_eq ρ hf hA
  have hdimW : Module.finrank (ZMod 2) W = 2 := by
    rw [image_moved_eq_top ρ d, finrank_top] at hdim
    exact hdim
  let e : localGroup A ≃* testImage ρ A := MulEquiv.ofBijective
    (wholeActionHom ρ d) ⟨wholeActionHom_injective ρ d hf hA,
      wholeActionHom_surjective ρ d⟩
  have hactor : Nat.card A = 2 := by
    have hk : subspaceKernel σ W (localActor A) = ⊥ := by
      apply (subspaceKernel_eq_bot_iff σ W _).mpr
      intro a ha hh
      apply Subtype.ext
      exact hfaithA a ha hh
    have hmul := card_subspaceKernel_mul_image σ W (localActor A) (le_top.trans d.stable)
    rw [hk, card_bot, one_mul] at hmul
    rw [hmul] at hcardA
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show A ≤ localGroup A from le_sup_right)).toEquiv]
    exact hcardA
  have hlocalcard : Nat.card (localGroup A) = 6 := by
    rw [Nat.card_congr (e.trans model).toEquiv, Nat.card_perm, Nat.card_fin]
    decide
  have hoddcard : Nat.card (oddPart A) = 3 := by
    have hd := card_dvd_of_le (show oddPart A ≤ localGroup A from le_sup_left)
    rw [hlocalcard] at hd
    have hn : Nat.card (oddPart A) ≠ 1 := fun h => hne (card_eq_one.mp h)
    have ho := d.odd
    have hdiv : Nat.card (oddPart A) = 1 ∨ Nat.card (oddPart A) = 2 ∨
        Nat.card (oddPart A) = 3 ∨ Nat.card (oddPart A) = 6 := by
      have : Nat.card (oddPart A) ∈ Nat.divisors 6 :=
        Nat.mem_divisors.mpr ⟨hd, by decide⟩
      simpa only [show Nat.divisors 6 = {1, 2, 3, 6} from by decide,
        Finset.mem_insert, Finset.mem_singleton] using this
    rcases hdiv with h | h | h | h
    · exact (hn h).elim
    · norm_num [h] at ho
    · exact h
    · norm_num [h] at ho
  have hAstab : A ≤ subspaceStabilizer ρ W := by
    intro a ha
    exact d.stable (mem_top (⟨a, (show A ≤ localGroup A from le_sup_right) ha⟩ : localGroup A))
  have hmoveA := moved_le_of_span_fixed ρ hAstab hspan
  have hsupport : subspaceCommutator ρ ⊤ (oddPart A) =
      subspaceCommutator ρ ⊤ (localGroup A) := by
    rw [localGroup, moved_sup]
    exact (sup_eq_left.mpr (hW ▸ hmoveA)).symm
  refine ⟨{
    actor_card := hactor
    odd_card := hoddcard
    dimension := hW ▸ hdimW
    support_eq := hsupport
    fixed_sum := hW ▸ hspan
    model := e.trans model
    faithful_support := ?_ }⟩
  intro g hg hh
  exact congrArg Subtype.val (d.faithful ρ hf hA ⟨g, hg⟩ (fun w hw => hh w (hW ▸ hw)))

end CFSG.Quasithin.ChapterB.FittingStructure.MinimalPlanes
