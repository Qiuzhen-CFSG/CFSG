module

public import Theory.AlgebraicGroup.RootSystems.Weyl
public import Mathlib.LinearAlgebra.Projection

/-!
# Orthogonal sums of root pairings

This module constructs the block-diagonal orthogonal sum of two real root pairings.  Root and
coroot indices are combined by a sum type, and the two given bases combine to a natural base of
the resulting root system.  Root-system, crystallographic, and reduced hypotheses pass to the
sum.

The principal comparison theorem identifies a root system whose orthogonal decomposition has
two distinct parts with the orthogonal sum of the corresponding root subsystems.  Its proof uses
the canonical positive root form to show that the two root spans are disjoint, uses the covering
hypothesis to show that they span the whole weight space, and then applies the linear equivalence
associated to complementary submodules.  The reflection-closure assumptions remain explicit
because they are precisely the data needed to form `RootPairing.rootSubsystem`.

This is the root-system decomposition underlying GLS3, Theorem 1.10.6, based on Definition 1.8.4
and the orthogonal-decomposition results of Theorem 1.8.5.
-/

open Function Set Submodule

noncomputable section

namespace RootPairing

universe uι₁ uι₂ uM₁ uN₁ uM₂ uN₂

variable {ι₁ : Type uι₁} {ι₂ : Type uι₂}
  {M₁ : Type uM₁} {N₁ : Type uN₁} {M₂ : Type uM₂} {N₂ : Type uN₂}
  [AddCommGroup M₁] [Module ℝ M₁] [AddCommGroup N₁] [Module ℝ N₁]
  [AddCommGroup M₂] [Module ℝ M₂] [AddCommGroup N₂] [Module ℝ N₂]

/-- The block-diagonal perfect pairing underlying `RootPairing.orthogonalSum`. -/
@[expose] public noncomputable def orthogonalSumPairing
    (P₁ : RootPairing ι₁ ℝ M₁ N₁) (P₂ : RootPairing ι₂ ℝ M₂ N₂) :
    (M₁ × M₂) →ₗ[ℝ] (N₁ × N₂) →ₗ[ℝ] ℝ := by
  letI : Module.IsReflexive ℝ N₁ := .of_isPerfPair P₁.flip.toLinearMap
  letI : Module.IsReflexive ℝ N₂ := .of_isPerfPair P₂.flip.toLinearMap
  exact ((P₁.toLinearMap.toPerfPair.prodCongr P₂.toLinearMap.toPerfPair) ≪≫ₗ
    Module.dualProdDualEquivDual ℝ N₁ N₂).toLinearMap

@[simp] public lemma orthogonalSumPairing_apply
    (P₁ : RootPairing ι₁ ℝ M₁ N₁) (P₂ : RootPairing ι₂ ℝ M₂ N₂)
    (x : M₁ × M₂) (y : N₁ × N₂) :
    orthogonalSumPairing P₁ P₂ x y =
      P₁.toLinearMap x.1 y.1 + P₂.toLinearMap x.2 y.2 := by
  simp [orthogonalSumPairing]

/-- The embedding of the two root families in the product weight module. -/
@[expose] public noncomputable def rootSumEmbedding
    (P₁ : RootPairing ι₁ ℝ M₁ N₁) (P₂ : RootPairing ι₂ ℝ M₂ N₂) :
    ι₁ ⊕ ι₂ ↪ M₁ × M₂ where
  toFun := Sum.elim (fun i => (P₁.root i, 0)) (fun j => (0, P₂.root j))
  inj' := by
    rintro (i | j) (i' | j') h
    · exact congrArg Sum.inl (P₁.root.injective (congrArg Prod.fst h))
    · exact False.elim (P₁.ne_zero i (congrArg Prod.fst h))
    · exact False.elim (P₁.ne_zero i' (congrArg Prod.fst h).symm)
    · exact congrArg Sum.inr (P₂.root.injective (congrArg Prod.snd h))

/-- The embedding of the two coroot families in the product coweight module. -/
@[expose] public noncomputable def corootSumEmbedding
    (P₁ : RootPairing ι₁ ℝ M₁ N₁) (P₂ : RootPairing ι₂ ℝ M₂ N₂) :
    ι₁ ⊕ ι₂ ↪ N₁ × N₂ where
  toFun := Sum.elim (fun i => (P₁.coroot i, 0)) (fun j => (0, P₂.coroot j))
  inj' := by
    rintro (i | j) (i' | j') h
    · exact congrArg Sum.inl (P₁.coroot.injective (congrArg Prod.fst h))
    · exact False.elim (P₁.ne_zero' i (congrArg Prod.fst h))
    · exact False.elim (P₁.ne_zero' i' (congrArg Prod.fst h).symm)
    · exact congrArg Sum.inr (P₂.coroot.injective (congrArg Prod.snd h))

@[simp] private lemma rootSumEmbedding_inl
    (P₁ : RootPairing ι₁ ℝ M₁ N₁) (P₂ : RootPairing ι₂ ℝ M₂ N₂) (i : ι₁) :
    rootSumEmbedding P₁ P₂ (Sum.inl i) = (P₁.root i, 0) := rfl

@[simp] private lemma rootSumEmbedding_inr
    (P₁ : RootPairing ι₁ ℝ M₁ N₁) (P₂ : RootPairing ι₂ ℝ M₂ N₂) (j : ι₂) :
    rootSumEmbedding P₁ P₂ (Sum.inr j) = (0, P₂.root j) := rfl

@[simp] private lemma corootSumEmbedding_inl
    (P₁ : RootPairing ι₁ ℝ M₁ N₁) (P₂ : RootPairing ι₂ ℝ M₂ N₂) (i : ι₁) :
    corootSumEmbedding P₁ P₂ (Sum.inl i) = (P₁.coroot i, 0) := rfl

@[simp] private lemma corootSumEmbedding_inr
    (P₁ : RootPairing ι₁ ℝ M₁ N₁) (P₂ : RootPairing ι₂ ℝ M₂ N₂) (j : ι₂) :
    corootSumEmbedding P₁ P₂ (Sum.inr j) = (0, P₂.coroot j) := rfl

/-- The block-diagonal orthogonal sum of two root pairings. -/
@[expose] public noncomputable def orthogonalSum
    (P₁ : RootPairing ι₁ ℝ M₁ N₁) (P₂ : RootPairing ι₂ ℝ M₂ N₂) :
    RootPairing (ι₁ ⊕ ι₂) ℝ (M₁ × M₂) (N₁ × N₂) := by
  letI : Module.IsReflexive ℝ N₁ := .of_isPerfPair P₁.flip.toLinearMap
  letI : Module.IsReflexive ℝ N₂ := .of_isPerfPair P₂.flip.toLinearMap
  let pairing := orthogonalSumPairing P₁ P₂
  letI : pairing.IsPerfPair := by
    unfold pairing orthogonalSumPairing
    infer_instance
  exact
    { toLinearMap := pairing
      root := rootSumEmbedding P₁ P₂
      coroot := corootSumEmbedding P₁ P₂
      root_coroot_two := by
        rintro (i | j)
        · change P₁.toLinearMap (P₁.root i) (P₁.coroot i) +
            P₂.toLinearMap 0 0 = 2
          simpa only [map_zero, add_zero] using P₁.root_coroot_two i
        · change P₁.toLinearMap 0 0 +
            P₂.toLinearMap (P₂.root j) (P₂.coroot j) = 2
          simpa only [map_zero, zero_add] using P₂.root_coroot_two j
      reflectionPerm := fun
        | Sum.inl i => Equiv.sumCongr (P₁.reflectionPerm i) (Equiv.refl ι₂)
        | Sum.inr j => Equiv.sumCongr (Equiv.refl ι₁) (P₂.reflectionPerm j)
      reflectionPerm_root := by
        rintro (i | i) (j | j)
        · change (P₁.root j, 0) -
              (P₁.toLinearMap (P₁.root j) (P₁.coroot i) + P₂.toLinearMap 0 0) •
                (P₁.root i, 0) = (P₁.root (P₁.reflectionPerm i j), 0)
          apply Prod.ext <;> simp [P₁.reflection_apply_root]
        · change (0, P₂.root j) -
              (P₁.toLinearMap 0 (P₁.coroot i) + P₂.toLinearMap (P₂.root j) 0) •
                (P₁.root i, 0) = (0, P₂.root j)
          simp
        · change (P₁.root j, 0) -
              (P₁.toLinearMap (P₁.root j) 0 + P₂.toLinearMap 0 (P₂.coroot i)) •
                (0, P₂.root i) = (P₁.root j, 0)
          simp
        · change (0, P₂.root j) -
              (P₁.toLinearMap 0 0 + P₂.toLinearMap (P₂.root j) (P₂.coroot i)) •
                (0, P₂.root i) = (0, P₂.root (P₂.reflectionPerm i j))
          apply Prod.ext <;> simp [P₂.reflection_apply_root]
      reflectionPerm_coroot := by
        rintro (i | i) (j | j)
        · change (P₁.coroot j, 0) -
              (P₁.toLinearMap (P₁.root i) (P₁.coroot j) + P₂.toLinearMap 0 0) •
                (P₁.coroot i, 0) = (P₁.coroot (P₁.reflectionPerm i j), 0)
          apply Prod.ext <;> simp [P₁.coreflection_apply_coroot]
        · change (0, P₂.coroot j) -
              (P₁.toLinearMap (P₁.root i) 0 + P₂.toLinearMap 0 (P₂.coroot j)) •
                (P₁.coroot i, 0) = (0, P₂.coroot j)
          simp
        · change (P₁.coroot j, 0) -
              (P₁.toLinearMap 0 (P₁.coroot j) + P₂.toLinearMap (P₂.root i) 0) •
                (0, P₂.coroot i) = (P₁.coroot j, 0)
          simp
        · change (0, P₂.coroot j) -
              (P₁.toLinearMap 0 0 + P₂.toLinearMap (P₂.root i) (P₂.coroot j)) •
                (0, P₂.coroot i) = (0, P₂.coroot (P₂.reflectionPerm i j))
          apply Prod.ext <;> simp [P₂.coreflection_apply_coroot] }

@[simp] public lemma orthogonalSum_root_inl
    (P₁ : RootPairing ι₁ ℝ M₁ N₁) (P₂ : RootPairing ι₂ ℝ M₂ N₂) (i : ι₁) :
    (orthogonalSum P₁ P₂).root (Sum.inl i) = (P₁.root i, 0) := rfl

@[simp] public lemma orthogonalSum_root_inr
    (P₁ : RootPairing ι₁ ℝ M₁ N₁) (P₂ : RootPairing ι₂ ℝ M₂ N₂) (j : ι₂) :
    (orthogonalSum P₁ P₂).root (Sum.inr j) = (0, P₂.root j) := rfl

@[simp] public lemma orthogonalSum_coroot_inl
    (P₁ : RootPairing ι₁ ℝ M₁ N₁) (P₂ : RootPairing ι₂ ℝ M₂ N₂) (i : ι₁) :
    (orthogonalSum P₁ P₂).coroot (Sum.inl i) = (P₁.coroot i, 0) := rfl

@[simp] public lemma orthogonalSum_coroot_inr
    (P₁ : RootPairing ι₁ ℝ M₁ N₁) (P₂ : RootPairing ι₂ ℝ M₂ N₂) (j : ι₂) :
    (orthogonalSum P₁ P₂).coroot (Sum.inr j) = (0, P₂.coroot j) := rfl

@[simp] public lemma orthogonalSum_pairing_inl_inl
    (P₁ : RootPairing ι₁ ℝ M₁ N₁) (P₂ : RootPairing ι₂ ℝ M₂ N₂) (i j : ι₁) :
    (orthogonalSum P₁ P₂).pairing (Sum.inl i) (Sum.inl j) = P₁.pairing i j := by
  change orthogonalSumPairing P₁ P₂ (P₁.root i, 0) (P₁.coroot j, 0) = P₁.pairing i j
  rw [orthogonalSumPairing_apply]
  simp

@[simp] public lemma orthogonalSum_pairing_inl_inr
    (P₁ : RootPairing ι₁ ℝ M₁ N₁) (P₂ : RootPairing ι₂ ℝ M₂ N₂) (i : ι₁) (j : ι₂) :
    (orthogonalSum P₁ P₂).pairing (Sum.inl i) (Sum.inr j) = 0 := by
  change orthogonalSumPairing P₁ P₂ (P₁.root i, 0) (0, P₂.coroot j) = 0
  rw [orthogonalSumPairing_apply]
  simp

@[simp] public lemma orthogonalSum_pairing_inr_inl
    (P₁ : RootPairing ι₁ ℝ M₁ N₁) (P₂ : RootPairing ι₂ ℝ M₂ N₂) (i : ι₂) (j : ι₁) :
    (orthogonalSum P₁ P₂).pairing (Sum.inr i) (Sum.inl j) = 0 := by
  change orthogonalSumPairing P₁ P₂ (0, P₂.root i) (P₁.coroot j, 0) = 0
  rw [orthogonalSumPairing_apply]
  simp

@[simp] public lemma orthogonalSum_pairing_inr_inr
    (P₁ : RootPairing ι₁ ℝ M₁ N₁) (P₂ : RootPairing ι₂ ℝ M₂ N₂) (i j : ι₂) :
    (orthogonalSum P₁ P₂).pairing (Sum.inr i) (Sum.inr j) = P₂.pairing i j := by
  change orthogonalSumPairing P₁ P₂ (0, P₂.root i) (0, P₂.coroot j) = P₂.pairing i j
  rw [orthogonalSumPairing_apply]
  simp

public instance orthogonalSum.instIsRootSystem
    (P₁ : RootPairing ι₁ ℝ M₁ N₁) (P₂ : RootPairing ι₂ ℝ M₂ N₂)
    [P₁.IsRootSystem] [P₂.IsRootSystem] : (orthogonalSum P₁ P₂).IsRootSystem where
  span_root_eq_top := by
    rw [show range (orthogonalSum P₁ P₂).root =
        LinearMap.inl ℝ M₁ M₂ '' range P₁.root ∪
          LinearMap.inr ℝ M₁ M₂ '' range P₂.root by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        cases i with
        | inl i => exact Or.inl ⟨P₁.root i, ⟨i, rfl⟩, rfl⟩
        | inr i => exact Or.inr ⟨P₂.root i, ⟨i, rfl⟩, rfl⟩
      · rintro (⟨_, ⟨i, rfl⟩, rfl⟩ | ⟨_, ⟨i, rfl⟩, rfl⟩)
        · exact ⟨Sum.inl i, rfl⟩
        · exact ⟨Sum.inr i, rfl⟩]
    rw [LinearMap.span_inl_union_inr]
    simp
  span_coroot_eq_top := by
    rw [show range (orthogonalSum P₁ P₂).coroot =
        LinearMap.inl ℝ N₁ N₂ '' range P₁.coroot ∪
          LinearMap.inr ℝ N₁ N₂ '' range P₂.coroot by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        cases i with
        | inl i => exact Or.inl ⟨P₁.coroot i, ⟨i, rfl⟩, rfl⟩
        | inr i => exact Or.inr ⟨P₂.coroot i, ⟨i, rfl⟩, rfl⟩
      · rintro (⟨_, ⟨i, rfl⟩, rfl⟩ | ⟨_, ⟨i, rfl⟩, rfl⟩)
        · exact ⟨Sum.inl i, rfl⟩
        · exact ⟨Sum.inr i, rfl⟩]
    rw [LinearMap.span_inl_union_inr]
    simp

public instance orthogonalSum.instIsCrystallographic
    (P₁ : RootPairing ι₁ ℝ M₁ N₁) (P₂ : RootPairing ι₂ ℝ M₂ N₂)
    [P₁.IsCrystallographic] [P₂.IsCrystallographic] :
    (orthogonalSum P₁ P₂).IsCrystallographic where
  exists_value := by
    rintro (i | i) (j | j)
    · rw [orthogonalSum_pairing_inl_inl]
      exact P₁.exists_value i j
    · rw [orthogonalSum_pairing_inl_inr]
      exact ⟨0, by simp⟩
    · rw [orthogonalSum_pairing_inr_inl]
      exact ⟨0, by simp⟩
    · rw [orthogonalSum_pairing_inr_inr]
      exact P₂.exists_value i j

public instance orthogonalSum.instIsReduced
    (P₁ : RootPairing ι₁ ℝ M₁ N₁) (P₂ : RootPairing ι₂ ℝ M₂ N₂)
    [P₁.IsReduced] [P₂.IsReduced] : (orthogonalSum P₁ P₂).IsReduced := by
  rw [isReduced_iff']
  rintro (i | i) (j | j) hij hdep
  · have hdep' : ¬ LinearIndependent ℝ ![P₁.root i, P₁.root j] := by
      intro h
      apply hdep
      apply LinearIndependent.of_comp (LinearMap.fst ℝ M₁ M₂)
      simp_rw [orthogonalSum_root_inl]
      have hv : (LinearMap.fst ℝ M₁ M₂) ∘ ![(P₁.root i, 0), (P₁.root j, 0)] =
          ![P₁.root i, P₁.root j] := by
        funext k
        fin_cases k <;> rfl
      rw [hv]
      exact h
    have hred := (isReduced_iff' (P := P₁)).mp (inferInstance : P₁.IsReduced)
    simpa using hred i j (by simpa using hij) hdep'
  · exfalso
    apply hdep
    rw [LinearIndependent.pair_iff' (by simp [P₁.ne_zero])]
    intro a h
    apply P₂.ne_zero j
    simpa using (congrArg Prod.snd h).symm
  · exfalso
    apply hdep
    rw [LinearIndependent.pair_iff' (by simp [P₂.ne_zero])]
    intro a h
    apply P₁.ne_zero j
    simpa using (congrArg Prod.fst h).symm
  · have hdep' : ¬ LinearIndependent ℝ ![P₂.root i, P₂.root j] := by
      intro h
      apply hdep
      apply LinearIndependent.of_comp (LinearMap.snd ℝ M₁ M₂)
      simp_rw [orthogonalSum_root_inr]
      have hv : (LinearMap.snd ℝ M₁ M₂) ∘ ![(0, P₂.root i), (0, P₂.root j)] =
          ![P₂.root i, P₂.root j] := by
        funext k
        fin_cases k <;> rfl
      rw [hv]
      exact h
    have hred := (isReduced_iff' (P := P₂)).mp (inferInstance : P₂.IsReduced)
    simpa using hred i j (by simpa using hij) hdep'

private def orthogonalSumBaseSet
    {P₁ : RootPairing ι₁ ℝ M₁ N₁} {P₂ : RootPairing ι₂ ℝ M₂ N₂}
    (b₁ : P₁.Base) (b₂ : P₂.Base) : Set (ι₁ ⊕ ι₂) :=
  Sum.inl '' (b₁.support : Set ι₁) ∪ Sum.inr '' (b₂.support : Set ι₂)

private lemma orthogonalSumBase_linearIndepOn
    {P₁ : RootPairing ι₁ ℝ M₁ N₁} {P₂ : RootPairing ι₂ ℝ M₂ N₂}
    (b₁ : P₁.Base) (b₂ : P₂.Base) :
    LinearIndepOn ℝ (orthogonalSum P₁ P₂).root (orthogonalSumBaseSet b₁ b₂) := by
  rw [linearIndepOn_iff_image (orthogonalSum P₁ P₂).root.injective.injOn]
  rw [show (orthogonalSum P₁ P₂).root '' orthogonalSumBaseSet b₁ b₂ =
      LinearMap.inl ℝ M₁ M₂ '' (P₁.root '' (b₁.support : Set ι₁)) ∪
        LinearMap.inr ℝ M₁ M₂ '' (P₂.root '' (b₂.support : Set ι₂)) by
    ext x
    simp only [orthogonalSumBaseSet, image_union, image_image,
      orthogonalSum_root_inl, orthogonalSum_root_inr, LinearMap.inl_apply,
      LinearMap.inr_apply]
    ]
  exact ((linearIndepOn_iff_image P₁.root.injective.injOn).mp b₁.linearIndepOn_root).inl_union_inr
    ((linearIndepOn_iff_image P₂.root.injective.injOn).mp b₂.linearIndepOn_root)

private lemma orthogonalSumBase_closure_inl
    {P₁ : RootPairing ι₁ ℝ M₁ N₁} {P₂ : RootPairing ι₂ ℝ M₂ N₂}
    (b₁ : P₁.Base) (b₂ : P₂.Base) {x : M₁}
    (hx : x ∈ AddSubmonoid.closure (P₁.root '' (b₁.support : Set ι₁))) :
    (x, 0) ∈ AddSubmonoid.closure
      ((orthogonalSum P₁ P₂).root '' orthogonalSumBaseSet b₁ b₂) := by
  induction hx using AddSubmonoid.closure_induction with
  | mem x hx =>
      rcases hx with ⟨i, hi, rfl⟩
      apply AddSubmonoid.subset_closure
      exact ⟨Sum.inl i, Or.inl ⟨i, hi, rfl⟩, rfl⟩
  | zero => exact AddSubmonoid.zero_mem _
  | add x y hx hy ihx ihy => simpa using AddSubmonoid.add_mem _ ihx ihy

private lemma orthogonalSumBase_closure_inr
    {P₁ : RootPairing ι₁ ℝ M₁ N₁} {P₂ : RootPairing ι₂ ℝ M₂ N₂}
    (b₁ : P₁.Base) (b₂ : P₂.Base) {x : M₂}
    (hx : x ∈ AddSubmonoid.closure (P₂.root '' (b₂.support : Set ι₂))) :
    (0, x) ∈ AddSubmonoid.closure
      ((orthogonalSum P₁ P₂).root '' orthogonalSumBaseSet b₁ b₂) := by
  induction hx using AddSubmonoid.closure_induction with
  | mem x hx =>
      rcases hx with ⟨i, hi, rfl⟩
      apply AddSubmonoid.subset_closure
      exact ⟨Sum.inr i, Or.inr ⟨i, hi, rfl⟩, rfl⟩
  | zero => exact AddSubmonoid.zero_mem _
  | add x y hx hy ihx ihy => simpa using AddSubmonoid.add_mem _ ihx ihy

/-- The natural base of an orthogonal sum, obtained from the bases of both summands. -/
public noncomputable def orthogonalSumBase
    {P₁ : RootPairing ι₁ ℝ M₁ N₁} {P₂ : RootPairing ι₂ ℝ M₂ N₂}
    [Finite ι₁] [Finite ι₂] [P₁.IsRootSystem] [P₂.IsRootSystem]
    [P₁.IsCrystallographic] [P₂.IsCrystallographic] [P₁.IsReduced] [P₂.IsReduced]
    (b₁ : P₁.Base) (b₂ : P₂.Base) : (orthogonalSum P₁ P₂).Base :=
  Base.mk' (orthogonalSum P₁ P₂) (orthogonalSumBaseSet b₁ b₂)
    (orthogonalSumBase_linearIndepOn b₁ b₂) <| by
      rintro (i | i)
      · rcases b₁.root_mem_or_neg_mem i with hi | hi
        · exact Or.inl (orthogonalSumBase_closure_inl b₁ b₂ hi)
        · exact Or.inr (by simpa using orthogonalSumBase_closure_inl b₁ b₂ hi)
      · rcases b₂.root_mem_or_neg_mem i with hi | hi
        · exact Or.inl (orthogonalSumBase_closure_inr b₁ b₂ hi)
        · exact Or.inr (by simpa using orthogonalSumBase_closure_inr b₁ b₂ hi)

private lemma rootForm_root_eq_zero_of_isOrthogonal
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) {i j : ι} (hij : P.IsOrthogonal i j) :
    P.RootForm (P.root i) (P.root j) = 0 := by
  have hcox : P.coxeterWeight i j = 0 :=
    RootPairing.coxeterWeight_zero_iff_isOrthogonal.mpr hij
  have h := P.four_smul_rootForm_sq_eq_coxeterWeight_smul i j
  rw [hcox, zero_smul] at h
  norm_num [nsmul_eq_mul] at h ⊢
  nlinarith

private lemma rootForm_eq_zero_of_mem_orthogonalSpans
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) {s t : Set ι}
    (horth : ∀ i ∈ s, ∀ j ∈ t, P.IsOrthogonal i j)
    {x y : M} (hx : x ∈ P.rootSpanOfSet s) (hy : y ∈ P.rootSpanOfSet t) :
    P.RootForm x y = 0 := by
  have hroot (i : ι) (hi : i ∈ s) : P.RootForm (P.root i) y = 0 := by
    refine Submodule.span_induction (p := fun y _ => P.RootForm (P.root i) y = 0)
      ?_ (by simp) ?_ ?_ hy
    · rintro _ ⟨j, hj, rfl⟩
      exact rootForm_root_eq_zero_of_isOrthogonal P (horth i hi j hj)
    · intro y z _ _ hyz hzz
      simp [map_add, hyz, hzz]
    · intro a y _ hy0
      simp [map_smul, hy0]
  refine Submodule.span_induction (p := fun x _ => P.RootForm x y = 0)
    ?_ (by simp) ?_ ?_ hx
  · rintro _ ⟨i, hi, rfl⟩
    exact hroot i hi
  · intro x z _ _ hx0 hz0
    simp [map_add, hx0, hz0]
  · intro a x _ hx0
    simp [map_smul, hx0]

private lemma rootSpans_disjoint_of_orthogonal
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) {s t : Set ι}
    (horth : ∀ i ∈ s, ∀ j ∈ t, P.IsOrthogonal i j) :
    Disjoint (P.rootSpanOfSet s) (P.rootSpanOfSet t) := by
  rw [Submodule.disjoint_def]
  intro x hx hy
  apply P.eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero
  · apply Submodule.span_mono _ hx
    rintro _ ⟨i, hi, rfl⟩
    exact Set.mem_range_self i
  · exact rootForm_eq_zero_of_mem_orthogonalSpans P horth hx hy

/-- A root pairing with exactly two distinct orthogonal parts is equivalent to the orthogonal sum
of the root subsystems carried by those parts. -/
public theorem equiv_orthogonalSum_of_two_parts
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) [P.IsRootSystem]
    (d : P.OrthogonalDecomposition) (s₁ s₂ : Set ι)
    (hparts : d.parts = {s₁, s₂}) (hne : s₁ ≠ s₂)
    (hreflect₁ : ∀ i ∈ s₁, ∀ j ∈ s₁, P.reflectionPerm i j ∈ s₁)
    (hreflect₂ : ∀ i ∈ s₂, ∀ j ∈ s₂, P.reflectionPerm i j ∈ s₂) :
    Nonempty (P.Equiv (orthogonalSum (P.rootSubsystem s₁ hreflect₁)
      (P.rootSubsystem s₂ hreflect₂))) := by
  have hs₁ : s₁ ∈ d.parts := by rw [hparts]; simp
  have hs₂ : s₂ ∈ d.parts := by rw [hparts]; simp
  have hdisj : Disjoint s₁ s₂ := d.pairwise_disjoint hs₁ hs₂ hne
  have horth : ∀ i ∈ s₁, ∀ j ∈ s₂, P.IsOrthogonal i j :=
    d.orthogonal s₁ hs₁ s₂ hs₂ hne
  have hcover : s₁ ∪ s₂ = Set.univ := by
    calc
      s₁ ∪ s₂ = ⋃₀ {s₁, s₂} := (Set.sUnion_pair s₁ s₂).symm
      _ = ⋃₀ d.parts := congrArg Set.sUnion hparts.symm
      _ = Set.univ := d.cover
  let S₁ := P.rootSpanOfSet s₁
  let S₂ := P.rootSpanOfSet s₂
  have hspan_disj : Disjoint S₁ S₂ := rootSpans_disjoint_of_orthogonal P horth
  have hspan_sup : S₁ ⊔ S₂ = ⊤ := by
    change span ℝ (P.root '' s₁) ⊔ span ℝ (P.root '' s₂) = ⊤
    rw [← span_union, ← image_union, hcover]
    simp
  have hcompl : IsCompl S₁ S₂ := IsCompl.of_eq hspan_disj.eq_bot hspan_sup
  let sumEmbedding : s₁ ⊕ s₂ ↪ ι := Function.Embedding.sumSet hdisj
  have sumEmbedding_surjective : Function.Surjective sumEmbedding := by
    intro i
    have hi : i ∈ s₁ ∪ s₂ := by rw [hcover]; exact Set.mem_univ i
    rcases hi with hi | hi
    · exact ⟨Sum.inl ⟨i, hi⟩, rfl⟩
    · exact ⟨Sum.inr ⟨i, hi⟩, rfl⟩
  let sumEquiv : s₁ ⊕ s₂ ≃ ι :=
    Equiv.ofBijective sumEmbedding ⟨sumEmbedding.injective, sumEmbedding_surjective⟩
  let indexEquiv : ι ≃ s₁ ⊕ s₂ := sumEquiv.symm
  let weightEquiv : M ≃ₗ[ℝ] S₁ × S₂ :=
    (Submodule.prodEquivOfIsCompl S₁ S₂ hcompl).symm
  refine ⟨?_⟩
  apply Equiv.mk' P
    (orthogonalSum (P.rootSubsystem s₁ hreflect₁) (P.rootSubsystem s₂ hreflect₂))
    weightEquiv indexEquiv
  intro i
  by_cases hi : i ∈ s₁
  · have he : indexEquiv i = Sum.inl (⟨i, hi⟩ : s₁) := by
      apply sumEquiv.injective
      simp [indexEquiv]
      change i = i
      rfl
    rw [he, orthogonalSum_root_inl, rootSubsystem_root]
    exact Submodule.prodEquivOfIsCompl_symm_apply_left S₁ S₂ hcompl
      (P.rootInSpan s₁ ⟨i, hi⟩)
  · have hi₂ : i ∈ s₂ := by
      have hi' : i ∈ s₁ ∪ s₂ := by rw [hcover]; exact Set.mem_univ i
      exact hi'.resolve_left hi
    have he : indexEquiv i = Sum.inr (⟨i, hi₂⟩ : s₂) := by
      apply sumEquiv.injective
      simp [indexEquiv]
      change i = i
      rfl
    rw [he, orthogonalSum_root_inr, rootSubsystem_root]
    exact Submodule.prodEquivOfIsCompl_symm_apply_right S₁ S₂ hcompl
      (P.rootInSpan s₂ ⟨i, hi₂⟩)

end RootPairing
