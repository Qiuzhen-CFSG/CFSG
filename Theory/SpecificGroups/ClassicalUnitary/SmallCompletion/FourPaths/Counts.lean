module
public import Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FourValence
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.Torus
public import Theory.GroupAction.RankTwoCosetGeometry.PathCardinality
public import Theory.GroupAction.RankTwoCosetGeometry.PathOrderLowerBound

/-!
# Native Hermitian four-space path counts

The two flag indices give the unequal vertex degrees. The exact torus
quotient and unitriangular order give each endpoint order, which equals
the nonbacktracking five-path count times the diagonal torus order.
This is the orbit–stabilizer census used in the native five-path action.

Source: Aschbacher–Smith F.4.5(7), printed p.275 of `refs/quasithin.pdf`.
-/

@[expose] public noncomputable section
open Matrix BenderSuzuki.MatrixGroups Subgroup
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourSylow
namespace Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FourPaths
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "J" => form F σ hσ
local notation "B" => borelSU F J
local notation "K" => FixedField F σ

abbrev family (i : Bool) : Subgroup (SU F J) :=
  if i then planeParabolicSU F J else pointParabolicSU F J

def degree (i : Bool) : ℕ := if i then Nat.card F + 1 else Nat.card K + 1

theorem borel_card : Nat.card B =
    Nat.card F ^ 2 * Nat.card K ^ 2 * ((Nat.card F - 1) * (Nat.card K - 1)) := by
  have h := ((upper F σ hσ).subgroupOf B).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (upper_le_borel F σ hσ)).toEquiv,
    upper_card, index_eq_card, borel_quotient_card] at h
  exact h.symm

theorem local_index (i : Bool) :
    ((family F σ hσ (!i)).subgroupOf (family F σ hσ i)).index = degree F σ i := by
  cases i
  · change ((planeParabolicSU F J).subgroupOf (pointParabolicSU F J)).index = _
    rw [← inf_subgroupOf_left]
    exact FourValence.point_index F σ hσ
  · change ((pointParabolicSU F J).subgroupOf (planeParabolicSU F J)).index = _
    rw [← inf_subgroupOf_right]
    exact FourValence.plane_index F σ hσ

theorem card_endpoint (i : Bool) : Nat.card (family F σ hσ i) =
    degree F σ i * (Nat.card F ^ 2 * Nat.card K ^ 2) *
      ((Nat.card F - 1) * (Nat.card K - 1)) := by
  have hi : family F σ hσ (!i) ⊓ family F σ hσ i = B := by
    cases i
    · exact inf_comm _ _
    · rfl
  have h := ((family F σ hσ (!i)).subgroupOf (family F σ hσ i)).card_mul_index
  rw [← inf_subgroupOf_right, Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv,
    hi, borel_card] at h
  rw [← hi, inf_subgroupOf_right, local_index] at h
  exact h.symm.trans (by ring)

open Subgroup.CosetGeometry.RankTwo SimpleGraph

theorem card_neighbors (v : Vertex (family F σ hσ)) :
    Nat.card ((graph (family F σ hσ)).neighborSet v) = degree F σ v.type :=
  card_neighbors_of_indices _ (degree F σ) (local_index F σ hσ) v

theorem card_five_paths (v : Vertex (family F σ hσ)) :
    Nat.card {p : BasedWalk (graph (family F σ hσ)) 5 v // p.Nonbacktracking} =
      degree F σ v.type * (Nat.card F ^ 2 * Nat.card K ^ 2) := by
  have hc := card_neighbors F σ hσ
  have (v : Vertex (family F σ hσ)) : Finite ((graph (family F σ hσ)).neighborSet v) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; cases v.type <;> simp [degree])
  have hf : ∀ {v w : Vertex (family F σ hσ)}, (graph (family F σ hσ)).Adj v w →
      w.type = !v.type := by
    intro v w h
    have hh := h.1
    cases hv : v.type <;> cases hw : w.type <;> simp_all
  have h := BasedWalk.card_nonbacktracking_succ (graph (family F σ hσ))
    (fun v => v.type) (degree F σ) hf hc 4 v
  change Nat.card {p : BasedWalk (graph (family F σ hσ)) (4+1) v // p.Nonbacktracking} = _
  rw [h]
  cases v.type <;> simp [degree, BasedWalk.forwardCount] <;> ring
end Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FourPaths
