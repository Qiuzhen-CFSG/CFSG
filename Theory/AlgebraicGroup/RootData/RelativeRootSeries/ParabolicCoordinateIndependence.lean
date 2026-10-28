module

public import Theory.AlgebraicGroup.RootData.RelativeRootSeries.ParabolicPositiveCollection

universe u

set_option linter.style.haveILetI false

/-!
Coordinate independence in an adjacent positive standard-parabolic
relative-root quotient.

For a positive height `i`, the exact-height Chevalley root factors give a
surjective coordinate homomorphism onto `S.layer i / S.layer (i + 1)`.  This
module proves that the homomorphism is also injective.  We enumerate the
exact-height roots once and rewrite a kernel relation as an ordered Chevalley
product lying in the next layer.  Reordering is performed only after passing
to the commutative quotient; no commutativity or coordinate uniqueness is
assumed for the actual root factors.

The lowest-layer extraction theorem from `ParabolicPositiveCollection`
supplies the mathematical separation step.  Its filtered Chevalley collection
raises relative height on every commutator correction, using
`S.chevalleySystem` together with `S.actualRootDatum` and
`S.rationalRootRealization`.  Distinct exact-height roots are separated by a
pair of coroot weights: the corresponding integral Cartan determinant is
nonzero, and an algebraically closed-field unit is chosen on which the
resulting integer character is nontrivial.  In positive characteristic this
uses evaluation on units rather than division by the determinant or a
differential argument, so inseparability and vanishing integer scalars do not
erase the distinction.  Lowest-layer extraction therefore makes every kernel
parameter zero, which is exactly internal directness of the root factors in
the quotient.  This is the standard Chevalley collection argument for the
relative-root filtration, without a Borel root-product uniqueness theorem.
-/

namespace Theory.AlgebraicGroup

open scoped BigOperators IsMulCommutative

variable {k : Type u} [Field k] [IsAlgClosed k]

private noncomputable def exactHeightRootList
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (i : ℕ) :
    List (S.ExactHeightRoot i) := by
  letI := Fintype.ofFinite S.D.Root
  classical
  letI : Fintype (S.ExactHeightRoot i) := by
    unfold StandardParabolicRelativeRootSetup.ExactHeightRoot
    infer_instance
  exact Finset.univ.toList

private def exactHeightFactor
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (i : ℕ)
    (a : (α : S.ExactHeightRoot i) → Multiplicative k)
    (α : S.ExactHeightRoot i) : S.layer i :=
  ⟨S.C.x α.root (a α).toAdd, by
    rw [StandardParabolicRelativeRootSetup.layer, RelativeRootSeries,
      RootSubgroupGenerated]
    apply Subgroup.subset_closure
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    refine ⟨α.root, by rw [α.height_eq], ?_⟩
    rw [← (S.chevalleySystem.1 α.root).2]
    exact ⟨(a α).toAdd, rfl⟩⟩

private noncomputable def exactHeightProduct
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (i : ℕ)
    (a : (α : S.ExactHeightRoot i) → Multiplicative k) : S.layer i :=
  ((exactHeightRootList S i).map (exactHeightFactor S i a)).prod

omit [IsAlgClosed k] in
private lemma coordinateHom_eq_one_iff_product_mem_next
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (i : ℕ) (hi : 0 < i)
    (a : (α : S.ExactHeightRoot i) → Multiplicative k) :
    let hN := standardParabolicRelativeRootLayer_next_normal S i hi
    let _ := hN
    standardParabolicRelativeRootLayer_coordinateHom S i hi a = 1 ↔
      ((exactHeightProduct S i a : S.layer i) : Variety.Point K) ∈
        S.layer (i + 1) := by
  dsimp only
  letI := Fintype.ofFinite S.D.Root
  classical
  letI : Fintype (S.ExactHeightRoot i) := by
    unfold StandardParabolicRelativeRootSetup.ExactHeightRoot
    infer_instance
  let hN := standardParabolicRelativeRootLayer_next_normal S i hi
  letI := hN
  let hcomm := standardParabolicRelativeRootLayer_quotient_commutative S i hi
  letI := hcomm
  rw [standardParabolicRelativeRootLayer_coordinateHom_apply]
  simp_rw [standardParabolicRelativeRootLayer_rootCoordinateHom_apply]
  change (∏ α : S.ExactHeightRoot i,
      QuotientGroup.mk' ((S.layer (i + 1)).subgroupOf (S.layer i))
        (exactHeightFactor S i a α)) = 1 ↔ _
  rw [← Finset.prod_map_toList]
  rw [show (Finset.univ.toList.map fun α =>
      QuotientGroup.mk' ((S.layer (i + 1)).subgroupOf (S.layer i))
        (exactHeightFactor S i a α)).prod =
      QuotientGroup.mk' ((S.layer (i + 1)).subgroupOf (S.layer i))
        (Finset.univ.toList.map (exactHeightFactor S i a)).prod by
    rw [map_list_prod]
    simp [List.map_map, Function.comp_def]]
  change QuotientGroup.mk' ((S.layer (i + 1)).subgroupOf (S.layer i))
      (exactHeightProduct S i a) = 1 ↔ _
  change ((exactHeightProduct S i a : S.layer i) :
      (S.layer i ⧸ (S.layer (i + 1)).subgroupOf (S.layer i))) = 1 ↔ _
  simpa only [Subgroup.mem_subgroupOf] using
    (QuotientGroup.eq_one_iff
      (N := (S.layer (i + 1)).subgroupOf (S.layer i))
      (exactHeightProduct S i a))

/-- Exact-height Chevalley root coordinates are independent in the adjacent
positive relative-root quotient. -/
public theorem standardParabolicRelativeRootLayer_coordinateHom_injective
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (i : ℕ) (hi : 0 < i) :
    Function.Injective
      (standardParabolicRelativeRootLayer_coordinateHom S i hi) := by
  letI := Fintype.ofFinite S.D.Root
  classical
  letI : Fintype (S.ExactHeightRoot i) := by
    unfold StandardParabolicRelativeRootSetup.ExactHeightRoot
    infer_instance
  let hN := standardParabolicRelativeRootLayer_next_normal S i hi
  letI := hN
  let hcomm := standardParabolicRelativeRootLayer_quotient_commutative S i hi
  letI := hcomm
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_antisymm
  · intro a ha
    have haOne : standardParabolicRelativeRootLayer_coordinateHom S i hi a = 1 :=
      ha
    have hproductMem :
        ((exactHeightProduct S i a : S.layer i) : Variety.Point K) ∈
          S.layer (i + 1) :=
      (coordinateHom_eq_one_iff_product_mem_next S i hi a).mp haOne
    let roots : List (S.ExactHeightRoot i) := exactHeightRootList S i
    have hrootsNodup : roots.Nodup := by
      exact Finset.nodup_toList _
    have hlistProductMem :
        (roots.map fun α => S.C.x α.root (a α).toAdd).prod ∈
          S.layer (i + 1) := by
      simpa [roots, exactHeightProduct, exactHeightFactor, Function.comp_def] using
        hproductMem
    have hzero := standardParabolic_exactHeight_collected_parameters_eq_zero
      S i hi roots hrootsNodup (fun α => (a α).toAdd) hlistProductMem
    apply funext
    intro α
    exact Multiplicative.toAdd.injective (by
      simpa [roots, exactHeightRootList] using hzero α (by
        simp [roots, exactHeightRootList]))
  · exact bot_le

end Theory.AlgebraicGroup
