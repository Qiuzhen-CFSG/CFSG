module

public import Theory.AlgebraicGroup.Reductive.ConnectedRadicalQuotient
public import Theory.AlgebraicGroup.Parabolic.Defs

/-!
The radical iteration in the connected case of Borel--Tits. The ascending
chain condition for connected closed subgroups produces a unipotent subgroup
which is the connected unipotent radical of its normalizer. Consequently the
saturated-normalizer case implies the connected existence theorem, including
properness in a reductive group when the starting subgroup is nonidentity.

The saturated-normalizer geometry is an explicit premise of the reduction
below; it is not asserted by this module. Source: GLS3, §3.1, Theorem 3.1.1.
-/

universe u
namespace Theory.AlgebraicGroup
variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The connected radical iteration terminates at a saturated normalizer.
The maximal-element argument is equivalent to stabilization of the ascending
sequence `X ↦ Rᵤ(N(X))`. -/
public theorem exists_saturated_unipotent_normalizer
    {G : Variety k} [AlgebraicGroup G] (X : ClosedSubgroup G)
    (hXc : _root_.IsConnected (X : Set (Variety.Point G)))
    (hXu : IsUnipotentAlgebraicGroup X.carrierVariety) :
    ∃ Y : ClosedSubgroup G, X ≤ Y ∧ X.normalizer ≤ Y.normalizer ∧
      IsConnectedUnipotentRadicalOf Y.normalizer Y := by
  let p : ClosedSubgroup G → Prop := fun Y =>
    _root_.IsConnected (Y : Set (Variety.Point G)) ∧
      IsUnipotentAlgebraicGroup Y.carrierVariety ∧
      X ≤ Y ∧ X.normalizer ≤ Y.normalizer
  obtain ⟨Y, hY, hmax⟩ := exists_maximal_connected_closedSubgroup G p
    ⟨X, hXc, hXu, (fun _ hx => hx), (fun _ hx => hx)⟩ (fun _ h => h.1)
  obtain ⟨U, hU⟩ := exists_connectedUnipotentRadicalOf Y.normalizer
  have hYU : Y ≤ U := hU.2.2.2.2 Y
    (fun _ hx => Subgroup.le_normalizer hx) hY.1 hY.2.1 (fun _ hx => hx)
  have hUp : p U := ⟨hU.2.1, hU.2.2.1,
    (fun _ hx => hYU (hY.2.2.1 hx)),
    (fun _ hx => hU.2.2.2.1 (hY.2.2.2 hx))⟩
  have hUY : U = Y := hmax U hUp hYU
  exact ⟨Y, hY.2.2.1, hY.2.2.2, hUY ▸ hU⟩

/-- A saturated-normalizer theorem implies connected Borel--Tits, including
properness for a nonidentity subgroup. The geometric premise is discharged
by the saturated case; all radical iteration is contained in this theorem. -/
public theorem exists_parabolic_of_saturated_normalizers
    {G : Variety k} [AlgebraicGroup G]
    (hG : IsReductiveAlgebraicGroup G)
    (hsaturated : ∀ Y : ClosedSubgroup G,
      IsConnectedUnipotentRadicalOf Y.normalizer Y →
        IsParabolicSubgroup Y.normalizer)
    (X : ClosedSubgroup G)
    (hXc : _root_.IsConnected (X : Set (Variety.Point G)))
    (hXu : IsUnipotentAlgebraicGroup X.carrierVariety) :
    ∃ P U : ClosedSubgroup G, IsParabolicSubgroup P ∧
      IsConnectedUnipotentRadicalOf P U ∧ X ≤ U ∧ X.normalizer ≤ P ∧
      (X.toSubgroup ≠ ⊥ → P ≠ ClosedSubgroup.top) := by
  obtain ⟨Y, hXY, hN, hY⟩ := exists_saturated_unipotent_normalizer X hXc hXu
  refine ⟨Y.normalizer, Y, hsaturated Y hY, hY, hXY, hN, ?_⟩
  intro hX htop
  have hntop : Subgroup.normalizer (Y.toSubgroup : Set (Variety.Point G)) = ⊤ :=
    congrArg (fun H : ClosedSubgroup G => H.toSubgroup) htop
  have hYn : Y.toSubgroup.Normal := Subgroup.normalizer_eq_top_iff.mp hntop
  have hYbot := connectedRadical_eq_bot_of_reductive hG Y hYn hY.2.1 hY.2.2.1
  apply hX
  apply le_antisymm
  · intro x hx
    have hy := hXY hx
    change x ∈ Y.toSubgroup at hy
    rwa [hYbot] at hy
  · exact bot_le

end Theory.AlgebraicGroup
