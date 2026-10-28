module

public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelRealization.MatrixGeneration
public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelRealization.CentralEmbedding
public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelRealization.OrderBound

/-!
# A concrete perfect central extension of PSL₃(4) with kernel C₄ × C₄ × C₃

`Realization` is an explicit finite perfect subgroup of
`Sym(224) × Sym(224) × SL₃(F₄)`, and `realizationProjection` is a proved
surjection onto the actual matrix PSL₃(4).

The checked order upper bound 967680 and explicit central subgroup
C₄ × C₄ × C₃ identify the kernel of this literal projection: injectivity
supplies 48 kernel elements, the order bound exhausts the kernel, and
centrality produces `realization`, the perfect central covering.
`realizationKernelEquiv` identifies its full kernel group structure.

Source: Aschbacher–Smith I.1.3(6), printed p.407; GLS3 §6.1, Tables 6.1.2–3.
This proves the existence of the exceptional covering required for the lower
bound in the source multiplier calculation. Universality and the independent
upper bound on the universal kernel are not needed for this construction.
-/

@[expose] public section
namespace Matrix.PSL3.ExceptionalFourCover

/-- The explicit subgroup model; its finite group and perfectness instances are inherited. -/
abbrev Realization := KernelModel.Group

/-- The literal projection to the canonical projective matrix group. -/
noncomputable abbrev realizationProjection : Realization →* PSL3Four.PSL :=
  KernelModel.projection

theorem realizationProjection_surjective : Function.Surjective realizationProjection :=
  KernelModel.projection_surjective

namespace KernelModel

theorem kernel_card_le_of_order_bound (horder : Nat.card Realization ≤ 967680) :
    Nat.card realizationProjection.ker ≤ 48 := by
  have h := realizationProjection.ker.card_mul_index
  rw [Subgroup.index_eq_card,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
      realizationProjection realizationProjection_surjective).toEquiv,
    PSL3Four.card_PSL] at h
  omega

/-- Restrict the explicit central candidates to the literal projection kernel. -/
noncomputable def kernelEmbedding (j : Multiplier →* Realization)
    (hproj : realizationProjection.comp j = 1) :
    Multiplier →* realizationProjection.ker :=
  j.codRestrict _ (fun a => DFunLike.congr_fun hproj a)

theorem kernelEmbedding_injective (j : Multiplier →* Realization)
    (hproj : realizationProjection.comp j = 1) (hj : Function.Injective j) :
    Function.Injective (kernelEmbedding j hproj) := by
  intro a b hab
  exact hj (congrArg Subtype.val hab)

/-- The order bound exhausts an independently constructed 48-element kernel subgroup. -/
theorem kernelEmbedding_bijective (j : Multiplier →* Realization)
    (hproj : realizationProjection.comp j = 1) (hj : Function.Injective j)
    (horder : Nat.card Realization ≤ 967680) :
    Function.Bijective (kernelEmbedding j hproj) := by
  rw [Nat.bijective_iff_injective_and_card]
  have hinj := kernelEmbedding_injective j hproj hj
  refine ⟨hinj, le_antisymm (Nat.card_le_card_of_injective _ hinj) ?_⟩
  rw [card_multiplier]
  exact kernel_card_le_of_order_bound horder

/-- Group structure, not just cardinality, for the literal kernel after both certificates. -/
noncomputable def kernelEquivOfEmbeddingAndOrder (j : Multiplier →* Realization)
    (hproj : realizationProjection.comp j = 1) (hj : Function.Injective j)
    (horder : Nat.card Realization ≤ 967680) :
    realizationProjection.ker ≃* Multiplier :=
  (MulEquiv.ofBijective (kernelEmbedding j hproj)
    (kernelEmbedding_bijective j hproj hj horder)).symm

theorem kernel_central_of_embedding_and_order (j : Multiplier →* Realization)
    (hproj : realizationProjection.comp j = 1) (hj : Function.Injective j)
    (hcentral : ∀ a, j a ∈ Subgroup.center Realization)
    (horder : Nat.card Realization ≤ 967680) :
    realizationProjection.ker ≤ Subgroup.center Realization := by
  intro g hg
  obtain ⟨a, ha⟩ := (kernelEmbedding_bijective j hproj hj horder).surjective ⟨g, hg⟩
  have he : j a = g := congrArg Subtype.val ha
  exact he ▸ hcentral a

/-- Actual application of the two finite certificates to the constructed projection. -/
noncomputable def perfectCoverOfEmbeddingAndOrder (j : Multiplier →* Realization)
    (hproj : realizationProjection.comp j = 1) (hj : Function.Injective j)
    (hcentral : ∀ a, j a ∈ Subgroup.center Realization)
    (horder : Nat.card Realization ≤ 967680) :
    PerfectCentralCovering.Cover Realization PSL3Four.PSL where
  toMonoidHom := realizationProjection
  surjective := realizationProjection_surjective
  isPerfect := inferInstance
  ker_le_center := kernel_central_of_embedding_and_order j hproj hj hcentral horder

end KernelModel

/-- The explicit perfect central extension of the simple matrix group is quasisimple. -/
instance realization_isQuasisimple : Theory.GroupTheory.IsQuasisimple Realization :=
  (KernelModel.perfectCoverOfEmbeddingAndOrder KernelModel.centralEmbedding
    KernelModel.projection_comp_centralEmbedding KernelModel.centralEmbedding_injective
    KernelModel.centralEmbedding_central KernelModel.realization_card_le).isQuasisimple

/-- The concrete finite quasisimple covering, with both finite certificates discharged. -/
noncomputable def realization : Theory.GroupTheory.Covering Realization PSL3Four.PSL where
  toMonoidHom := realizationProjection
  surjective := realizationProjection_surjective

/-- The covering retains the actual projective matrix projection. -/
theorem realization_toMonoidHom : realization.toMonoidHom = realizationProjection := rfl

theorem realization_surjective : Function.Surjective realization :=
  realization.surjective

/-- The full group structure of the kernel of the concrete exceptional covering. -/
noncomputable def realizationKernelEquiv : realization.toMonoidHom.ker ≃* Multiplier :=
  KernelModel.kernelEquivOfEmbeddingAndOrder KernelModel.centralEmbedding
    KernelModel.projection_comp_centralEmbedding KernelModel.centralEmbedding_injective
    KernelModel.realization_card_le

theorem card_realization_kernel : Nat.card realization.toMonoidHom.ker = 48 := by
  rw [Nat.card_congr realizationKernelEquiv.toEquiv, card_multiplier]

/-- The identified kernel is exactly the center, since the actual base group is simple. -/
theorem realization_ker_eq_center :
    realization.toMonoidHom.ker = Subgroup.center Realization := by
  let : IsSimpleGroup PSL3Four.PSL :=
    Atlas.psl_simple_high_rank (F := PSL3Four.F) 3 (by decide)
  exact realization.ker_eq_center_of_isSimple

/-- The concrete model attains its certified upper bound. -/
theorem card_realization : Nat.card Realization = 967680 := by
  have h := realization.toMonoidHom.ker.card_mul_index
  rw [Subgroup.index_eq_card,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
      realization.toMonoidHom realization.surjective).toEquiv,
    card_realization_kernel, PSL3Four.card_PSL] at h
  exact h.symm

end Matrix.PSL3.ExceptionalFourCover
