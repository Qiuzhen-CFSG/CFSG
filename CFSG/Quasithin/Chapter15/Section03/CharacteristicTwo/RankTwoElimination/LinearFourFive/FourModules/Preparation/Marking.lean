module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.ModuleCases
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.FlagGeometry.GraphDuality

/-!
# Independence of the plane-parabolic marking in 15.3.24

Every automorphism of the actual binary linear group in dimension four is
inner or inner followed by inverse transpose. Consequently it sends a plane
stabilizer to another plane stabilizer: the plane is moved linearly, and in
the graph case replaced by its orthogonal complement. Both operations
preserve dimension two. This transports the literal preimage in L between
arbitrary isomorphisms L/O₂(L) ≃ PSL₄(2).

This result supplies marking compatibility only. Construction of the first
plane parabolic from the source local hypotheses remains separate.

Source: Aschbacher–Smith, 15.3.24, printed pp.1129–1130;
GLS3, Theorem 2.5.12 and §2.7 for binary linear automorphisms.
-/

public section

open Subgroup BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Preparation

private theorem automorphism_plane (W : Submodule (ZMod 2) (Space 4))
    (hW : Module.finrank (ZMod 2) W = 2) (a : MulAut (LinearGroup 4)) :
    ∃ W' : Submodule (ZMod 2) (Space 4), Module.finrank (ZMod 2) W' = 2 ∧
      (parabolic W).map a.toMonoidHom = parabolic W' := by
  obtain ⟨g, rfl | rfl⟩ := inner_graph (Or.inl rfl) a
  · exact ⟨W.map g.toLinearMap, (g.finrank_map_eq W).trans hW, inner_map_parabolic W g⟩
  · refine ⟨flagOrthogonal (W.map g.toLinearMap), ?_, graph_inner_map_parabolic W g⟩
    rw [flagOrthogonal_finrank, g.finrank_map_eq, hW]

variable {G : Type*} [Group G] {d : LocalData G} {L : Subgroup G}

/-- A plane marking can be changed to any independently supplied quotient
isomorphism, including one chosen by module classification. -/
theorem planeParabolic_remark
    {e₀ : (L ⧸ pCore 2 L) ≃* Projective 4} (h : PlaneParabolic d L e₀)
    (e : (L ⧸ pCore 2 L) ≃* Projective 4) : Nonempty (PlaneParabolic d L e) := by
  let f := projectiveEquivLinear (by decide : 0 < 4)
  let a : MulAut (LinearGroup 4) := (e₀.trans f).symm.trans (e.trans f)
  obtain ⟨W, hW, hmap⟩ := automorphism_plane h.plane h.dimension a
  refine ⟨⟨W, hW, ?_⟩⟩
  have hact : linearAction (by decide) e =
      a.toMonoidHom.comp (linearAction (by decide) e₀) := by
    ext l
    simp [linearAction, a, f]
  rw [h.intersection, ← hmap, hact, ← comap_comap,
    comap_map_eq_self_of_injective a.injective]

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Preparation
