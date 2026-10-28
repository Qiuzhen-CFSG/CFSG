module

public import Theory.SpecificGroups.Rudvalis.Model.CoreQuotients.Max6Action.Blocks
public import Theory.SpecificGroups.Rudvalis.Model.CoreQuotients.SurjectiveKernels

/-!
# The surjective five-letter action of the Rudvalis max6 word subgroup

The two literal ATLAS generators permute five distinct sixteen-point subsets
of the original degree-4060 carrier. Closure induction extends these two
certified block permutations to every element of max6. Distinctness makes
the resulting permutation unique, giving a homomorphism. Its image contains
an inverse five-cycle and an adjacent transposition, hence is all of S₅.

The certified local order and the trivial two-core of S₅ then identify the
kernel with the intrinsic two-core and give the genuine quotient equivalence,
compatible with its quotient projection. No ambient order, simplicity, or
splitting assumption is used.

Source: GLS3 Table 5.3r, printed p.279; the quotient is an input to the
Rudvalis case of Aschbacher–Smith E.1.14(5), printed p.214, citing Asc82a
Lemma 4.9. Block discovery and ATLAS attribution are retained in
`Max6Action/source/`; only kernel-checked facts enter the proof.
-/

namespace Rudvalis.CoreQuotients
open SylowOvergroups Max6Blocks

private def onFinsets : Model →* Equiv.Perm (Finset (Fin 4060)) where
  toFun g := g.val.finsetCongr
  map_one' := Equiv.finsetCongr_refl
  map_mul' g h := (Equiv.finsetCongr_trans h.val g.val).symm

private def Compatible (g : Model) (σ : Equiv.Perm (Fin 5)) : Prop :=
  ∀ i, onFinsets g (block i) = block (σ i)

private theorem compatible_unique {g : Model} {σ τ : Equiv.Perm (Fin 5)}
    (hσ : Compatible g σ) (hτ : Compatible g τ) : σ = τ := by
  apply Equiv.ext
  intro i
  exact block_injective ((hσ i).symm.trans (hτ i))

private theorem compatible_one : Compatible 1 1 := by
  intro i
  rw [map_one]
  rfl

private theorem compatible_mul {g h : Model} {σ τ : Equiv.Perm (Fin 5)}
    (hg : Compatible g σ) (hh : Compatible h τ) : Compatible (g * h) (σ * τ) := by
  intro i
  rw [map_mul, Equiv.Perm.mul_apply, hh i, hg (τ i)]
  rfl

private theorem compatible_inv {g : Model} {σ : Equiv.Perm (Fin 5)}
    (hg : Compatible g σ) : Compatible g⁻¹ σ⁻¹ := by
  intro i
  apply (onFinsets g).injective
  rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rw [hg]
  simp

private theorem compatible_first : Compatible max6Generators.1 cycle := by
  intro i
  change (block i).map (modelSubgroup.subtype max6Generators.1).toEmbedding = _
  rw [← LocalCardinality.Max6.generator0_eq]
  exact gen0_block i

private theorem compatible_second : Compatible max6Generators.2 transposition := by
  intro i
  change (block i).map (modelSubgroup.subtype max6Generators.2).toEmbedding = _
  rw [← LocalCardinality.Max6.generator1_eq]
  exact gen1_block i

private theorem exists_compatible (g : max6) :
    ∃ σ : Equiv.Perm (Fin 5), Compatible g.val σ := by
  suffices ∀ (x : Model), x ∈ max6 → ∃ σ, Compatible x σ from this g.val g.property
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨cycle, compatible_first⟩
    · exact ⟨transposition, compatible_second⟩
  | one => exact ⟨1, compatible_one⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨σ, hσ⟩ := ihx
    obtain ⟨τ, hτ⟩ := ihy
    exact ⟨σ * τ, compatible_mul hσ hτ⟩
  | inv x hx ih =>
    obtain ⟨σ, hσ⟩ := ih
    exact ⟨σ⁻¹, compatible_inv hσ⟩

/-- The action of the unchanged max6 word subgroup on its five certified blocks. -/
public noncomputable def max6FiveAction : max6 →* Equiv.Perm (Fin 5) where
  toFun g := Classical.choose (exists_compatible g)
  map_one' := compatible_unique (Classical.choose_spec (exists_compatible 1)) compatible_one
  map_mul' g h := compatible_unique (Classical.choose_spec (exists_compatible (g * h)))
    (compatible_mul (Classical.choose_spec (exists_compatible g))
      (Classical.choose_spec (exists_compatible h)))

/-- The action is induced by the literal degree-4060 permutation on each block. -/
public theorem max6FiveAction_blocks (g : max6) (i : Fin 5) :
    (block i).map g.val.val.toEmbedding = block (max6FiveAction g i) :=
  Classical.choose_spec (exists_compatible g) i

private def first : max6 :=
  ⟨max6Generators.1, Subgroup.subset_closure (Set.mem_insert _ _)⟩

private def second : max6 :=
  ⟨max6Generators.2, Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩

/-- The first original ATLAS generator induces the inverse five-cycle. -/
public theorem max6FiveAction_generator0 :
    max6FiveAction ⟨max6Generators.1,
      Subgroup.subset_closure (Set.mem_insert _ _)⟩ = cycle :=
  compatible_unique (Classical.choose_spec (exists_compatible first)) compatible_first

/-- The second original ATLAS generator induces the adjacent transposition. -/
public theorem max6FiveAction_generator1 :
    max6FiveAction ⟨max6Generators.2,
      Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩ =
        transposition :=
  compatible_unique (Classical.choose_spec (exists_compatible second)) compatible_second

/-- The certified block action has full symmetric image. -/
public theorem max6FiveAction_surjective : Function.Surjective max6FiveAction := by
  apply MonoidHom.range_eq_top.mp
  apply top_le_iff.mp
  rw [← cycle_transposition_generate, Subgroup.closure_le]
  intro σ hσ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hσ
  rcases hσ with rfl | rfl
  · exact ⟨first, max6FiveAction_generator0⟩
  · exact ⟨second, max6FiveAction_generator1⟩

/-- The five-block action has kernel of order 2¹¹. -/
public theorem max6FiveAction_kernel_card : Nat.card max6FiveAction.ker = 2048 :=
  max6_kernel_card max6FiveAction max6FiveAction_surjective

/-- The action kernel is exactly the intrinsic two-core of max6. -/
public theorem max6FiveAction_ker : max6FiveAction.ker = pCore 2 max6 :=
  max6_kernel_eq_pCore max6FiveAction max6FiveAction_surjective

/-- The intrinsic max6 two-core quotient is the actual five-letter symmetric group. -/
public noncomputable def max6FiveQuotientEquiv :
    (max6 ⧸ pCore 2 max6) ≃* Equiv.Perm (Fin 5) :=
  max6QuotientEquivOfSurjective max6FiveAction max6FiveAction_surjective

/-- Compatibility with the literal intrinsic quotient map. -/
@[simp] public theorem max6FiveQuotientEquiv_mk (g : max6) :
    max6FiveQuotientEquiv (QuotientGroup.mk' (pCore 2 max6) g) =
      max6FiveAction g :=
  max6QuotientEquivOfSurjective_mk max6FiveAction max6FiveAction_surjective g

end Rudvalis.CoreQuotients
