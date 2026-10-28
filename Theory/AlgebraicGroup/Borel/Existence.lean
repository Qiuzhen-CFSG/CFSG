module

public import Theory.AlgebraicGroup.Borel.Defs
public import Theory.AlgebraicGroup.ClosedSubgroup.Maximal

universe u

/-! Existence of Borel subgroups. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- Theorem 1.6.2(a): every algebraic group contains a Borel subgroup. -/
public theorem exists_borelSubgroup (G : Variety k) [AlgebraicGroup G] :
    ∃ B : ClosedSubgroup G, IsBorelSubgroup B := by
  obtain ⟨B, hB, hmax⟩ := exists_maximal_connected_closedSubgroup G
    (fun S =>
      _root_.IsConnected (S : Set (Variety.Point G)) ∧
        Group.IsSolvable (Variety.Point S.carrierVariety))
    (by
      let B : ClosedSubgroup G := ClosedSubgroup.bot
      refine ⟨B, ?_, ?_⟩
      · change _root_.IsConnected ({1} : Set (Variety.Point G))
        exact isConnected_singleton
      · let : Subsingleton B.toSubgroup := by
          constructor
          intro x y
          apply Subtype.ext
          have hx : (x : Variety.Point G) = 1 := by
            apply Subgroup.mem_bot.mp
            exact x.property
          have hy : (y : Variety.Point G) = 1 := by
            apply Subgroup.mem_bot.mp
            exact y.property
          exact hx.trans hy.symm
        let : Subsingleton (Variety.Point B.carrierVariety) :=
          B.pointEquiv.subsingleton
        exact (inferInstance : Group.IsSolvable (Variety.Point B.carrierVariety)))
    (fun _ hS => hS.1)
  refine ⟨B, hB.1, hB.2, ?_⟩
  intro S hconnected hsolvable hBS
  exact hmax S ⟨hconnected, hsolvable⟩ hBS

/-- Theorem 1.6.2(c): every connected solvable closed subgroup is contained
in a Borel subgroup. -/
public theorem exists_borelSubgroup_containing_connected_solvable
    {G : Variety k} [AlgebraicGroup G]
    (H : ClosedSubgroup G)
    (hconnected : _root_.IsConnected (H : Set (Variety.Point G)))
    (hsolvable : Group.IsSolvable (Variety.Point H.carrierVariety)) :
    ∃ B : ClosedSubgroup G, IsBorelSubgroup B ∧ H ≤ B := by
  obtain ⟨B, hB, hmax⟩ := exists_maximal_connected_closedSubgroup G
    (fun S =>
      _root_.IsConnected (S : Set (Variety.Point G)) ∧
        Group.IsSolvable (Variety.Point S.carrierVariety) ∧ H ≤ S)
    ⟨H, hconnected, hsolvable, fun _ hx => hx⟩
    (fun _ hS => hS.1)
  refine ⟨B, ⟨hB.1, hB.2.1, ?_⟩, hB.2.2⟩
  intro S hSconnected hSsolvable hBS
  exact hmax S
    ⟨hSconnected, hSsolvable, fun x hx => hBS (hB.2.2 hx)⟩ hBS

end Theory.AlgebraicGroup
