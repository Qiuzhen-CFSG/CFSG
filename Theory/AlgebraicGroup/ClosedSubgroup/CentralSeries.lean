module

public import Mathlib.GroupTheory.Nilpotent
public import Theory.AlgebraicGroup.ClosedSubgroup.Closure
public import Theory.AlgebraicGroup.ClosedSubgroup.Connected

universe u

/-!
Connected closures of relative lower central series.

The key result `subgroupZariskiClosure_commutator_closedSubgroups_isConnected`
shows that, over an algebraically closed field, the Zariski closure of the
commutator of two closed subgroups is connected whenever the first subgroup
is connected.  Its proof maps the connected first subgroup through the
commutator morphism with a fixed point of the second subgroup, places the
resulting range in the identity component, and then identifies the closure
with that component.  The result is iterated by
`relativeLowerCentralSeries_closure_connected` for relative lower central
series arguments in the ClosedSubgroup and centralizer developments.
-/

namespace Theory.AlgebraicGroup

open scoped commutatorElement

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The Zariski closure of a mixed commutator of closed subgroups is connected
when the first subgroup is connected. -/
public lemma subgroupZariskiClosure_commutator_closedSubgroups_isConnected
    {G : Variety k} [AlgebraicGroup G]
    (H K : ClosedSubgroup G)
    (hHconn : _root_.IsConnected (H : Set (Variety.Point G))) :
    _root_.IsConnected
      ((subgroupZariskiClosure G ⁅H.toSubgroup, K.toSubgroup⁆) :
        Set (Variety.Point G)) := by
  let D : ClosedSubgroup G :=
    subgroupZariskiClosure G ⁅H.toSubgroup, K.toSubgroup⁆
  have hcomm : ⁅H.toSubgroup, K.toSubgroup⁆ ≤
      D.identityComponentAmbient.toSubgroup := by
    rw [Subgroup.commutator_def, Subgroup.closure_le]
    rintro z ⟨h, hh, q, hq, rfl⟩
    obtain ⟨h', rfl⟩ := H.range_inclusion.ge hh
    obtain ⟨q', rfl⟩ := K.range_inclusion.ge hq
    let base : Variety.Morphism H.carrierVariety G :=
      (AlgebraicGroup.commutatorMorphism G).comp
        (H.inclusion.toVariety.pair
          (Variety.Morphism.const H.carrierVariety G
            (K.inclusion.toVariety.toFun q')))
    have hbase_apply (x : Variety.Point H.carrierVariety) :
        base.toFun x =
          H.inclusion.toVariety.toFun x * K.inclusion.toVariety.toFun q' *
            (H.inclusion.toVariety.toFun x)⁻¹ *
              (K.inclusion.toVariety.toFun q')⁻¹ := by
      simp [base, Variety.Morphism.comp, Variety.Morphism.pair,
        Variety.Morphism.const, AlgebraicGroup.commutatorMorphism_apply]
    have hbase_mem (x : Variety.Point H.carrierVariety) :
        base.toFun x ∈ D.toSubgroup := by
      change base.toFun x ∈ closure
        (⁅H.toSubgroup, K.toSubgroup⁆ : Subgroup (Variety.Point G))
      apply subset_closure
      rw [hbase_apply]
      exact Subgroup.commutator_mem_commutator
        (H.pointEquiv x).property (K.pointEquiv q').property
    let r : Variety.Morphism H.carrierVariety D.carrierVariety :=
      { toFun := fun x ↦ D.pointEquiv.symm ⟨base.toFun x, hbase_mem x⟩
        regular := by
          intro i
          rcases base.regular i with ⟨p, hp⟩
          refine ⟨p, fun x ↦ ?_⟩
          change (D.pointEquiv
            (D.pointEquiv.symm ⟨base.toFun x, hbase_mem x⟩)).val.val i = _
          rw [D.pointEquiv.apply_symm_apply]
          exact hp x }
    have hr_inclusion (x : Variety.Point H.carrierVariety) :
        D.inclusion.onPoints (r.toFun x) = base.toFun x := by
      change (D.pointEquiv
        (D.pointEquiv.symm ⟨base.toFun x, hbase_mem x⟩)).val = _
      rw [D.pointEquiv.apply_symm_apply]
    have hsource : Variety.IsConnected H.carrierVariety := by
      let e := Variety.closedSubvarietyPointHomeomorph H.isZariskiClosed
      let : ConnectedSpace
          {x : Variety.Point G // x ∈ (H : Set (Variety.Point G))} :=
        Subtype.connectedSpace hHconn
      let : ConnectedSpace (Variety.Point H.carrierVariety) :=
        e.connectedSpace_iff.mpr inferInstance
      exact connectedSpace_iff_univ.mp inferInstance
    have hrange : _root_.IsConnected (Set.range r.toFun) := by
      rw [← Set.image_univ]
      exact hsource.image r.toFun r.continuous.continuousOn
    have hone : (1 : Variety.Point D.carrierVariety) ∈ Set.range r.toFun := by
      refine ⟨1, ?_⟩
      apply D.inclusion_injective
      rw [hr_inclusion, hbase_apply]
      change H.inclusion.onPoints 1 * K.inclusion.onPoints q' *
        (H.inclusion.onPoints 1)⁻¹ * (K.inclusion.onPoints q')⁻¹ =
          D.inclusion.onPoints 1
      simp
    have hrange0 : Set.range r.toFun ⊆
        AlgebraicGroup.identityComponent D.carrierVariety :=
      hrange.subset_connectedComponent hone
    apply (ClosedSubgroup.mem_identityComponentAmbient_iff D _).mpr
    refine ⟨r.toFun h', hrange0 ⟨h', rfl⟩, ?_⟩
    rw [hr_inclusion, hbase_apply]
    rfl
  have hDle : D ≤ D.identityComponentAmbient := by
    intro z hz
    change z ∈ closure
      (⁅H.toSubgroup, K.toSubgroup⁆ : Subgroup (Variety.Point G)) at hz
    exact closure_minimal hcomm
      (Variety.isClosed_iff_isZariskiClosed.mpr
        D.identityComponentAmbient.isZariskiClosed) hz
  have hEq : D = D.identityComponentAmbient := by
    apply SetLike.coe_injective
    exact Set.Subset.antisymm hDle D.identityComponentAmbient_le
  change _root_.IsConnected (D : Set (Variety.Point G))
  rw [hEq]
  exact D.identityComponentAmbient_isConnected

@[expose]
public def relativeLowerCentralSeries
    (G : Variety k) [AlgebraicGroup G]
    (S : Subgroup (Variety.Point G)) : ℕ → Subgroup (Variety.Point G)
  | 0 => S
  | n + 1 => ⁅relativeLowerCentralSeries G S n,
      (⊤ : Subgroup (Variety.Point G))⁆

omit [IsAlgClosed k] in
public lemma relativeLowerCentralSeries_le_lowerCentralSeries
    {G : Variety k} [AlgebraicGroup G]
    (S : Subgroup (Variety.Point G)) :
    ∀ n, relativeLowerCentralSeries G S n ≤
      Subgroup.lowerCentralSeries (⊤ : Subgroup (Variety.Point G)) n := by
  intro n
  induction n with
  | zero => exact le_top
  | succ n ih =>
      rw [relativeLowerCentralSeries, Subgroup.lowerCentralSeries_succ]
      exact Subgroup.commutator_mono ih le_top

public lemma relativeLowerCentralSeries_closure_connected
    {G : Variety k} [AlgebraicGroup G]
    (S : Subgroup (Variety.Point G))
    (hSconn : _root_.IsConnected (S : Set (Variety.Point G))) :
    ∀ n, _root_.IsConnected
      ((subgroupZariskiClosure G
        (relativeLowerCentralSeries G S n)) : Set (Variety.Point G)) := by
  intro n
  induction n with
  | zero =>
      change _root_.IsConnected (closure (S : Set (Variety.Point G)))
      exact hSconn.closure
  | succ n ih =>
      let H : ClosedSubgroup G :=
        subgroupZariskiClosure G (relativeLowerCentralSeries G S n)
      let K : ClosedSubgroup G :=
        subgroupZariskiClosure G (⊤ : Subgroup (Variety.Point G))
      let C : ClosedSubgroup G :=
        subgroupZariskiClosure G ⁅H.toSubgroup, K.toSubgroup⁆
      let L : ClosedSubgroup G := subgroupZariskiClosure G
        (relativeLowerCentralSeries G S (n + 1))
      have hCconn : _root_.IsConnected
          (C : Set (Variety.Point G)) :=
        subgroupZariskiClosure_commutator_closedSubgroups_isConnected H K ih
      have hC_le : C ≤ L := by
        intro x hx
        change x ∈ closure
          (⁅H.toSubgroup, K.toSubgroup⁆ : Subgroup (Variety.Point G)) at hx
        apply (closure_minimal ?_
          (Variety.isClosed_iff_isZariskiClosed.mpr L.isZariskiClosed)) hx
        exact commutator_subgroupZariskiClosure_le_two G
          (relativeLowerCentralSeries G S n)
          (⊤ : Subgroup (Variety.Point G))
      have hL_le : L ≤ C := by
        intro x hx
        change x ∈ closure
          (relativeLowerCentralSeries G S (n + 1) :
            Set (Variety.Point G)) at hx
        apply (closure_minimal ?_
          (Variety.isClosed_iff_isZariskiClosed.mpr C.isZariskiClosed)) hx
        rw [relativeLowerCentralSeries]
        have hmono :
            ⁅relativeLowerCentralSeries G S n,
              (⊤ : Subgroup (Variety.Point G))⁆ ≤
            ⁅H.toSubgroup, K.toSubgroup⁆ :=
          Subgroup.commutator_mono
            (fun _ hy ↦ subset_closure hy)
            (fun _ hy ↦ subset_closure hy)
        exact fun _ hz ↦ subset_closure (hmono hz)
      have hEq : C = L := by
        apply SetLike.coe_injective
        exact Set.Subset.antisymm hC_le hL_le
      change _root_.IsConnected (L : Set (Variety.Point G))
      rw [← hEq]
      exact hCconn

end Theory.AlgebraicGroup
