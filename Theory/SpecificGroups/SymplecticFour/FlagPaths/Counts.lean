module
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.OuterQuotient.ParabolicClasses
public import Theory.SpecificGroups.SymplecticFour.Sylow.FlagCounts
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder
public import Theory.AtlasPort.LinearGroups.SL2Order
public import Theory.GroupAction.RankTwoCosetGeometry.PathCardinality
public import Theory.GroupAction.RankTwoCosetGeometry.PathOrderLowerBound
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.Torus
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
/-!
# Counts for the symplectic flag graph

The determinant character and the three-coordinate radical give the orders
of both actual parabolics. Dividing by the full Borel gives valence q + 1;
nonbacktracking paths of length k + 1 therefore number (q + 1)q^k.
These are the native counts in Aschbacher–Smith F.4.4–6, pp.274–277,
used in the five-path action and small-completion order argument.
-/

@[expose] public noncomputable section
open Matrix Subgroup
namespace Theory.SpecificGroups.SymplecticFour.FlagPaths
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private def pointRadicalCoordinates : pointRadical (F := F) ≃ F × F × F where
  toFun q := (q.val.val.val (.inl 1) (.inr 0), q.val.val.val (.inr 1) (.inr 0),
    q.val.val.val (.inl 0) (.inr 0))
  invFun x := ⟨pointRadicalElement x.1 x.2.1 x.2.2, pointRadicalElement_mem _ _ _⟩
  left_inv q := Subtype.ext (pointRadical_eq_element q.val q.property).symm
  right_inv _ := rfl

private theorem card_of_surjective {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) :
    Nat.card G = Nat.card H * Nat.card f.ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]

theorem card_pointParabolic : Nat.card (pointParabolic (F := F)) =
    Nat.card F ^ 4 * (Nat.card F - 1)^2 * (Nat.card F + 1) := by
  have hp : Function.Surjective (determinantCharacter (point F)) := by
    intro a
    exact ⟨⟨diagonalTorus a 1, (diagonalTorus_mem_borel a 1).1⟩,
      diagonalTorus_point_character a 1⟩
  have hk : Nat.card (determinantCharacter (point F)).ker = Nat.card (pointLocal (F := F)) :=
    (Subgroup.card_map_of_injective (stabilizer (point F)).subtype_injective).symm
  change Nat.card (stabilizer (point F)) = _
  rw [card_of_surjective _ hp, hk, card_of_surjective pointQuotient pointQuotient_surjective]
  change Nat.card Fˣ * (Nat.card (SpecialLinearGroup (Fin 2) F) * Nat.card (pointRadical (F := F))) = _
  rw [Atlas.card_sl_two, Nat.card_congr pointRadicalCoordinates, Nat.card_prod, Nat.card_prod,
    Nat.card_units]
  have hq := Finite.one_lt_card (α := F)
  have hsq : Nat.card F ^ 2 - 1 = (Nat.card F - 1) * (Nat.card F + 1) := by
    have h := Nat.sub_add_cancel (show 1 ≤ Nat.card F by omega)
    have he : (Nat.card F - 1) * (Nat.card F + 1) + 1 = Nat.card F ^ 2 := by
      nlinarith
    omega
  rw [hsq]
  ring

theorem card_planeParabolic : Nat.card (planeParabolic (F := F)) =
    Nat.card F ^ 4 * (Nat.card F - 1)^2 * (Nat.card F + 1) := by
  rw [← DiagramAutomorphisms.card_pointParabolic_eq_card_planeParabolic, card_pointParabolic]

abbrev family : Bool → Subgroup (Sp F) := fun i => if i then planeParabolic else pointParabolic

theorem card_endpoint (i : Bool) : Nat.card (family (F := F) i) =
    Nat.card F ^ 4 * (Nat.card F - 1)^2 * (Nat.card F + 1) := by
  cases i
  · exact card_pointParabolic
  · exact card_planeParabolic

theorem local_index (i : Bool) :
    ((family (F := F) (!i)).subgroupOf (family i)).index = Nat.card F + 1 := by
  have hi (i : Bool) : family (F := F) (!i) ⊓ family i = borel := by
    cases i
    · exact inf_comm _ _
    · rfl
  have hc : Nat.card ((family (F := F) (!i)).subgroupOf (family i)) = Nat.card (borel (F := F)) := by
    rw [← inf_subgroupOf_right, Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv, hi]
  have hh := ((family (F := F) (!i)).subgroupOf (family i)).card_mul_index
  rw [hc, card_endpoint, ← card_borel] at hh
  exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := borel (F := F))) hh

open Subgroup.CosetGeometry.RankTwo SimpleGraph

theorem card_neighbors (v : Vertex (family (F := F))) :
    Nat.card ((graph family).neighborSet v) = Nat.card F + 1 :=
  card_neighbors_of_indices family (fun _ => Nat.card F + 1) local_index v

theorem card_paths (k : ℕ) (v : Vertex (family (F := F))) :
    Nat.card {p : BasedWalk (graph family) (k+1) v // p.Nonbacktracking} =
      (Nat.card F + 1) * Nat.card F ^ k := by
  have hf {v w : Vertex (family (F := F))} (h : (graph family).Adj v w) : w.type = !v.type := by
    have hne := h.1
    cases hv : v.type <;> cases hw : w.type <;> simp_all
  have : ∀ v : Vertex (family (F := F)), Finite ((graph family).neighborSet v) :=
    fun v => Nat.finite_of_card_ne_zero (by rw [card_neighbors]; omega)
  rw [BasedWalk.card_nonbacktracking_succ (graph family) (fun v => v.type)
    (fun _ => Nat.card F + 1) hf card_neighbors]
  congr 1
  generalize (!v.type) = b
  induction k generalizing b with
  | zero => rfl
  | succ k ih => simp [BasedWalk.forwardCount, ih, pow_succ, mul_comm]
end Theory.SpecificGroups.SymplecticFour.FlagPaths
