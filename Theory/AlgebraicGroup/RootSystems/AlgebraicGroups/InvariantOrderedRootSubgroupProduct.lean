module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.InvariantUnipotentSourceWordLayerBridge
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.InvariantRootList
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.theorem_1_9_5_h

/-!
This module supplies the pointwise part of the invariant-unipotent root-product
package.  The finite list of contained roots is obtained from the realized
torus-root set.  A Chevalley parameterization, a finite-degree exchange law,
and a source-word witness are kept as explicit hypotheses: the current
`RootGroupData.IsRealization` contract does not construct these data.  The
filtered collector then turns every source word into one factor for each root
in the fixed list, while the converse inclusion is the elementary subgroup
induction on `List.Forall₂`.

The retained hypotheses `hK`, `hT`, `hX`, `hXu`, and `hD` are exactly the
numbered theorem's invariant-unipotent interface.  The additional collection
package is the minimal extension needed for a pointwise theorem and is not a
disguised use of `RootSubgroupGenerated`.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
private theorem forall₂_map_chevalley_mem
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} {C : ChevalleyData K D}
    {roots : List D.Root}
    (hC : ∀ α, Set.range (C.x α) = D.rootSubgroup α)
    (params : D.Root → k) :
    List.Forall₂ (fun α y => y ∈ D.rootSubgroup α) roots
      (roots.map (fun α => C.x α (params α))) := by
  induction roots with
  | nil => exact .nil
  | cons α roots ih =>
      refine .cons ?_ ih
      change C.x α (params α) ∈ (D.rootSubgroup α : Set (Variety.Point K))
      rw [← hC α]
      exact Set.mem_range_self _

omit [IsAlgClosed k] in
private theorem list_prod_mem_of_forall₂_root_mem
    {K : Variety k} [AlgebraicGroup K] {T X : ClosedSubgroup K}
    {D : RootGroupData K T} {roots : List D.Root}
    (hcontains : ∀ α, α ∈ roots → D.rootSubgroup α ≤ X)
    {xs : List (Variety.Point K)}
    (hxs : List.Forall₂ (fun α y => y ∈ D.rootSubgroup α) roots xs) :
    xs.prod ∈ X.toSubgroup := by
  induction hxs with
  | nil =>
      exact X.toSubgroup.one_mem
  | @cons α y roots xs hy htail ih =>
      rw [List.prod_cons]
      exact X.toSubgroup.mul_mem
        ((hcontains α (by simp)) hy)
        (ih (fun β hβ => hcontains β (by simp [hβ])))

/--
Pointwise factorization from an explicit Chevalley collection package.

The `hcollection` premise is intentionally a minimal extension of the
invariant-unipotent hypotheses.  For the finite list supplied by
`finite_contained_root_list`, it gives a degree filtration, an adjacent
exchange law with strictly higher corrections, and a Chevalley source word for
each point of `X`.  In applications the exchange support is discharged from
`IsRootAdditionRealization` together with the chosen root-system/closedness
package; no abstract generated subgroup is used here.
-/
public theorem invariant_unipotent_pointwise_factorization_core
    {K : Variety k} [AlgebraicGroup K]
    (_hK : IsReductiveAlgebraicGroup K)
    (T X : ClosedSubgroup K) (_hT : IsMaximalTorus T)
    (_hX : IsClosedSubgroupInvariant T X)
    (_hXu : IsUnipotentAlgebraicGroup X.carrierVariety)
    (D : RootGroupData K T) (hD : D.IsRealization)
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (b : P.Base)
    (C : ChevalleyData K D)
    (hAdd : IsRootAdditionRealization D P e)
    (hC : IsChevalleySystem D C P e b)
    (hcollection :
      IsRootAdditionRealization D P e →
      ∀ (roots : List D.Root),
        roots.Nodup →
        (∀ α, α ∈ roots ↔ D.rootSubgroup α ≤ X) →
        ∃ (degree : D.Root → ℕ) (degreeBound : ℕ),
          (∀ α ∈ roots, degree α < degreeBound) ∧
          (∀ α β a c, α ∈ roots → β ∈ roots → α ≠ β →
            ∃ correction : List (D.Root × k),
              (∀ z ∈ correction,
                z.1 ∈ roots ∧
                  max (degree α) (degree β) < degree z.1) ∧
              C.x α a * C.x β c =
                C.x β c * C.x α a *
                  FilteredCollection.wordProduct
                    (fun γ t => C.x γ t) correction) ∧
          (∀ x : Variety.Point K, x ∈ X →
            ∃ word : List (D.Root × k),
              (∀ z ∈ word, z.1 ∈ roots) ∧
              FilteredCollection.wordProduct
                (fun γ t => C.x γ t) word = x)) :
    Nonempty (InvariantOrderedRootSubgroupProduct X D) := by
  classical
  obtain ⟨roots, hrootsNodup, hroots⟩ :=
    finite_contained_root_list T X D hD
  obtain ⟨degree, degreeBound, hdegreeBound, hswap, hword⟩ :=
    hcollection hAdd roots hrootsNodup hroots
  let factor : D.Root → k → Variety.Point K := fun α t => C.x α t
  have hadd : ∀ α a c, factor α a * factor α c = factor α (a + c) := by
    intro α a c
    exact hC.2.2.2.1 α a c
  refine ⟨{
    roots := roots
    nodup := hrootsNodup
    contains_iff := hroots
    mem_iff := ?_ }⟩
  intro x
  constructor
  · intro hx
    obtain ⟨word, hwordSupport, hwordEq⟩ := hword x hx
    obtain ⟨params, hparams⟩ :=
      FilteredCollection.filteredCollection_exists_params
        (degree := degree) factor roots hrootsNodup degreeBound hdegreeBound hadd
        (fun α β a c hα hβ hαβ => by
          obtain ⟨correction, hcorrection, hEq⟩ :=
            hswap α β a c hα hβ hαβ
          exact ⟨correction, hcorrection, hEq⟩)
        word (by
          intro z hz
          exact hwordSupport z hz)
    refine ⟨roots.map (fun α => C.x α (params α)),
      forall₂_map_chevalley_mem (fun α => (hC.1 α).2) params, ?_⟩
    exact hparams.symm.trans hwordEq
  · rintro ⟨xs, hxs, hprod⟩
    have hmem : xs.prod ∈ X.toSubgroup :=
      list_prod_mem_of_forall₂_root_mem (fun α hα => (hroots α).mp hα) hxs
    exact hprod ▸ hmem

end Theory.AlgebraicGroup
