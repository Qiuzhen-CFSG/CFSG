module

public import Theory.AlgebraicGroup.ClosedSubgroup.FiniteGeneration
public import Theory.AlgebraicGroup.RootSubgroups.GeneratedSubgroup

universe u

/-!
Connected generation for the fixed-torus Borel-intersection argument.

Realized root subgroups are algebraic copies of the additive group and hence
connected. Adjoin them to any connected closed subgroup and apply finite-word
connected generation to the family indexed by `Option A`. Its abstractly
generated subgroup is precisely the supremum of the initial subgroup and the
root-generated subgroup. No connectedness assertion about arbitrary unipotent
subgroups is used.

This is the connected-generation step in GLS3, Theorem 1.11.4, and Borel,
*Linear Algebraic Groups*, §§14.3–14.5; the common-root intersection identity
is a separate geometric input.
-/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G] {T : ClosedSubgroup G}

private theorem realizedRoot_connected (D : RootGroupData G T) (hD : D.IsRealization)
    (a : D.Root) : _root_.IsConnected (D.rootSubgroup a : Set (Variety.Point G)) := by
  let : ConnectedSpace (Variety.Point (D.rootSubgroup a).carrierVariety) :=
    connectedSpace_iff_univ.mpr (hD.2.2.1 a).1.2.isConnected
  change _root_.IsConnected ((D.rootSubgroup a).toSubgroup : Set (Variety.Point G))
  rw [← (D.rootSubgroup a).range_inclusion]
  exact isConnected_range (D.rootSubgroup a).inclusion.toVariety.continuous

/-- A connected closed subgroup together with realized root groups generates
a connected subgroup of the ambient algebraic group. -/
public theorem isConnected_sup_rootSubgroupGenerated (S : ClosedSubgroup G)
    (hS : _root_.IsConnected (S : Set (Variety.Point G)))
    (D : RootGroupData G T) (hD : D.IsRealization) (A : Set D.Root) :
    _root_.IsConnected
      ((S.toSubgroup ⊔ RootSubgroupGenerated D A : Subgroup (Variety.Point G)) :
        Set (Variety.Point G)) := by
  let H : Option A → ClosedSubgroup G := fun i =>
    match i with
    | none => S
    | some a => D.rootSubgroup a.1
  have hc : ∀ i, _root_.IsConnected (H i : Set (Variety.Point G)) := by
    intro i
    cases i with
    | none => exact hS
    | some a => exact realizedRoot_connected D hD a.1
  have hu : (⋃ i, (H i : Set (Variety.Point G))) =
      (S : Set (Variety.Point G)) ∪
        ⋃ a ∈ A, (D.rootSubgroup a : Set (Variety.Point G)) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨i, hi⟩
      cases i with
      | none => exact Or.inl hi
      | some a => exact Or.inr ⟨a.1, a.2, hi⟩
    · rintro (hx | ⟨a, ha, hx⟩)
      · exact ⟨none, hx⟩
      · exact ⟨some ⟨a, ha⟩, hx⟩
  have h := closure_iUnion_connected_closedSubgroup_isConnected H hc
  rw [hu, Subgroup.closure_union] at h
  rw [show Subgroup.closure (S : Set (Variety.Point G)) = S.toSubgroup from
    Subgroup.closure_eq S.toSubgroup] at h
  exact h

end Theory.AlgebraicGroup
