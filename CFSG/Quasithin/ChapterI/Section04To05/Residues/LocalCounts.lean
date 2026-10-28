module

public import CFSG.Quasithin.ChapterI.Section04To05.Residues.FanoPlanes

/-!
# Exact local incidence counts from the original D-system

The standard A₆/S₆ quotient parabolics have index fifteen. Transporting
these indices through the literal quotient and individual coset maps gives
fifteen lines and fifteen planes at every C₃ point. The line residue has
three actual points and three actual planes. Translation preserves the
specified incidence fibers, so these are statements about every original
vertex, not just about an abstract local model.

Source: Aschbacher–Smith I.5.3–4 and the local input to I.5.9(1), pp.420–421.
-/

@[expose] public noncomputable section
namespace Quasithin.I5.DSystem
open Subgroup
variable {G : Type*} [Group G] {D : Diagram} (S : DSystem D G)

def incidentFiberTranslation (i j : Fin 3) (x : G ⧸ S.family i) (g : G) :
    {y : G ⧸ S.family j // S.Inc x y} ≃
      {y : G ⧸ S.family j // S.Inc (g • x) y} where
  toFun y := ⟨g • y.val, y.property.smul S g⟩
  invFun y := ⟨g⁻¹ • y.val, by
    simpa only [inv_smul_smul] using y.property.smul S g⁻¹⟩
  left_inv y := Subtype.ext (inv_smul_smul g y.val)
  right_inv y := Subtype.ext (smul_inv_smul g y.val)

theorem incidentFiber_card (i j : Fin 3) (hji : j ≠ i) (x : G ⧸ S.family i) :
    Nat.card {y : G ⧸ S.family j // S.Inc x y} =
      (localParabolic S.family i j).index := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G ((1 : G) : G ⧸ S.family i) x
  rw [← Nat.card_congr (S.incidentFiberTranslation i j _ g)]
  exact S.pointedCoset_card i j hji

theorem line_points_card (l : S.Line) : Nat.card {x : S.Point // S.Inc x l} = 3 := by
  let e : {x : S.Point // S.Inc x l} ≃ {x : S.Point // S.Inc l x} :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun x =>
      ⟨CosetGeometry.Incident.symm S.family, CosetGeometry.Incident.symm S.family⟩)
  rw [Nat.card_congr e, S.incidentFiber_card 1 0 (by decide) l]
  exact S.line_parabolics_product_indices.1

theorem line_planes_card (l : S.Line) : Nat.card {π : S.Plane // S.Inc l π} = 3 := by
  rw [S.incidentFiber_card 1 2 (by decide) l]
  exact S.line_parabolics_product_indices.2.1

private theorem parabolic_pair_index {K : Type*} [Group K] (i j k : Fin 3)
    (e : (S.family i ⧸ pCore 2 (S.family i)) ≃* K) (A B : Subgroup K) (n : ℕ)
    (ha : A.index = n) (hb : B.index = n)
    (he : ((localParabolic S.family i j).map (S.localQuotientMap i e) = A ∧
        (localParabolic S.family i k).map (S.localQuotientMap i e) = B) ∨
      ((localParabolic S.family i j).map (S.localQuotientMap i e) = B ∧
        (localParabolic S.family i k).map (S.localQuotientMap i e) = A)) :
    (localParabolic S.family i j).index = n ∧
      (localParabolic S.family i k).index = n := by
  have hk (r : Fin 3) : (S.localQuotientMap i e).ker ≤ localParabolic S.family i r := by
    intro x hx
    exact S.T_le r (S.localQuotientMap_ker_le i e hx)
  rw [← (localParabolic S.family i j).index_map_eq (S.localQuotientMap_surjective i e) (hk j),
    ← (localParabolic S.family i k).index_map_eq (S.localQuotientMap_surjective i e) (hk k)]
  rcases he with h | h
  · exact ⟨h.1 ▸ ha, h.2 ▸ hb⟩
  · exact ⟨h.1 ▸ hb, h.2 ▸ ha⟩

variable (S₃ : DSystem .C3 G)

theorem c3_point_parabolic_indices :
    (localParabolic S₃.family 0 1).index = 15 ∧
      (localParabolic S₃.family 0 2).index = 15 := by
  rcases S₃.point_standard_quotientMark with ⟨e, he⟩ | ⟨e, he⟩
  · exact parabolic_pair_index S₃ 0 1 2 e _ _ 15
      Theory.SpecificGroups.SymmetricSix.a6DuadStabilizer_index
      Theory.SpecificGroups.SymmetricSix.a6SynthemeStabilizer_index he
  · exact parabolic_pair_index S₃ 0 1 2 e _ _ 15
      Theory.SpecificGroups.SymmetricSix.duadStabilizer_index
      Theory.SpecificGroups.SymmetricSix.synthemeStabilizer_index he

theorem c3_point_lines_card (x : S₃.Point) : Nat.card {l : S₃.Line // S₃.Inc x l} = 15 := by
  rw [S₃.incidentFiber_card 0 1 (by decide) x]
  exact S₃.c3_point_parabolic_indices.1

theorem c3_point_planes_card (x : S₃.Point) : Nat.card {π : S₃.Plane // S₃.Inc x π} = 15 := by
  rw [S₃.incidentFiber_card 0 2 (by decide) x]
  exact S₃.c3_point_parabolic_indices.2

end Quasithin.I5.DSystem
