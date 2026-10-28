module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.Planes
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.Representative
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.Marking

/-!
# Words for the inner actions of the four Held pairs

Each transporter is an actual Held word. Forward and inverse generator words
will certify conjugacy with the fixed representative. The two actor words are
products in the literal candidate two-group. No identity is asserted by the data.
Sources: ATLAS HeG1-p2058B0, max3/max4; GLS3 Table 5.3p. Discovery words are
retained in `source/conjugators.g` and the parent's `source/actors.json`.
-/

@[expose] public section
namespace Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.InnerImages
open Subgroup

def twoGenerator (i : Bool) (j : Fin 2) (k : Fin 4) : He :=
  evalLocalWord i (twoWord i j k)

theorem twoGenerator_mem (i : Bool) (j : Fin 2) (k : Fin 4) :
    twoGenerator i j k ∈ candidateTwo i j := subset_closure ⟨k, rfl⟩

def evalPowers {G : Type*} [Group G] {n : ℕ} (g : Fin n → G)
    (w : List (Fin n × ℤ)) : G := (w.map (fun t => g t.1 ^ t.2)).prod

theorem evalPowers_mem {G : Type*} [Group G] {n : ℕ} (H : Subgroup G)
    (g : Fin n → G) (h : ∀ k, g k ∈ H) (w : List (Fin n × ℤ)) :
    evalPowers g w ∈ H := by
  apply H.list_prod_mem
  intro x hx
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp hx
  exact H.zpow_mem (h t.1) t.2

def bridge : He := evalLocalWord false
  [(true, 1), (false, 1), (true, -2), (false, 1), (true, -4), (false, 1),
    (true, -1), (false, -1), (true, -1), (false, -1), (true, 1)]

def transporterWord : Bool → Fin 2 → List (Bool × ℤ)
  | false, 0 => [(true, 2), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 4), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1)]
  | false, 1 => [(true, 2), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 2), (false, 1), (true, 1), (false, 1)]
  | true, 0 => [(true, -1), (false, 1), (true, -3), (false, 1), (true, -2), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1)]
  | true, 1 => [(false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -3), (false, 1), (true, 2), (false, 1), (true, 1)]

/-- Conjugation by this element sends the fixed representative to the candidate. -/
def transporter (i : Bool) (j : Fin 2) : He :=
  ((if i then bridge⁻¹ * SylowOvergroups.alignment⁻¹ else 1) *
    evalLocalWord i (transporterWord i j))⁻¹

def forwardWord : Bool → Fin 2 → Fin 4 → List (Fin 4 × ℤ)
  | false, 0, 0 => [(0, 1), (2, 1), (3, 1), (1, 1), (3, 1), (2, 1), (0, 1)]
  | false, 0, 1 => [(0, 1), (2, 1), (3, 1), (2, 1), (0, 1)]
  | false, 0, 2 => [(1, 1), (2, 1), (3, 1), (2, 1), (0, 1), (2, 1), (3, 1), (2, 1), (1, 1)]
  | false, 0, 3 => [(2, 1), (1, 1), (3, 1), (2, 1), (3, 1), (2, 1), (1, 1), (0, 1)]
  | false, 1, 0 => [(3, 1), (1, 1), (2, -1), (1, 1), (0, 1)]
  | false, 1, 1 => [(1, 1), (3, 1), (1, 1)]
  | false, 1, 2 => [(2, 1), (0, 1), (2, 1), (3, 1), (1, 1), (2, 1), (1, 1), (0, 1)]
  | false, 1, 3 => [(1, 1), (0, 1), (2, -1), (0, 1), (3, 1)]
  | true, 0, 0 => [(3, 1), (2, 1), (3, 1), (0, 1), (3, 1), (2, 1), (3, 1)]
  | true, 0, 1 => [(3, 1), (1, 1), (3, 1), (2, 1), (1, 1)]
  | true, 0, 2 => [(2, 1), (3, 1), (1, 1), (0, 1), (3, 1), (2, 1)]
  | true, 0, 3 => [(3, 1), (2, 1), (1, 1), (0, 1), (2, 1)]
  | true, 1, 0 => [(3, 1), (1, 1), (3, 1), (2, 1), (0, 1), (3, 1), (1, 1), (3, 1)]
  | true, 1, 1 => [(2, 1), (0, 1), (3, 1), (1, 1), (3, 1), (2, 1), (0, 1)]
  | true, 1, 2 => [(3, 1), (1, 1), (3, 1), (0, 1), (3, 1), (2, 1), (1, 1), (3, 1), (2, 1)]
  | true, 1, 3 => [(3, 1), (0, 1), (3, 1), (2, 1), (1, 1), (3, 1), (2, 1), (1, 1)]

def backwardWord : Bool → Fin 2 → Fin 4 → List (Fin 4 × ℤ)
  | false, 0, 0 => [(0, 1), (1, 1), (2, 1), (1, 1), (0, 1)]
  | false, 0, 1 => [(0, 1), (1, 1), (3, 2), (0, 1), (1, 1), (0, 1)]
  | false, 0, 2 => [(0, 1), (1, 1), (3, -1), (2, 1), (1, 1), (0, 1)]
  | false, 0, 3 => [(3, 1), (1, 1), (3, -1)]
  | false, 1, 0 => [(0, 1), (1, 1), (2, 1), (0, 1), (1, 1), (0, 1)]
  | false, 1, 1 => [(0, 1), (1, 1), (3, 1), (2, 1), (1, 1), (0, 1)]
  | false, 1, 2 => [(1, 1), (3, -1), (1, 1), (0, 1), (1, 1), (3, 1), (2, 1), (0, 1)]
  | false, 1, 3 => [(3, 1), (1, 1), (3, -1)]
  | true, 0, 0 => [(3, 1), (1, 1), (2, 1), (0, 1), (1, 1), (3, -1), (2, 1)]
  | true, 0, 1 => [(3, 1), (1, 1), (0, 1), (1, 1), (3, -1), (2, 1)]
  | true, 0, 2 => [(1, 1), (3, -1), (1, 1), (0, 1), (1, 1), (3, -1), (0, 1)]
  | true, 0, 3 => [(3, -1), (0, 1), (1, 1), (2, 1), (1, 1), (0, 1)]
  | true, 1, 0 => [(3, 1), (1, 1), (0, 1), (1, 1), (3, 1), (2, 1), (0, 1)]
  | true, 1, 1 => [(3, -1), (0, 1), (1, 1), (3, -1), (0, 1)]
  | true, 1, 2 => [(2, 1), (1, 1), (3, 1), (1, 1), (0, 1), (1, 1), (3, 1), (1, 1)]
  | true, 1, 3 => [(0, 1), (1, 1), (3, -1), (2, 1), (1, 1), (0, 1)]

def actorWord : Bool → Fin 2 → Fin 2 → List (Fin 4 × ℤ)
  | false, 0, 0 => [(0, 1), (2, 1), (3, 1), (1, 1), (2, 1), (3, 1), (1, 1), (2, 1), (3, 1), (1, 1), (2, 1), (3, 1)]
  | false, 0, 1 => [(0, 1)]
  | false, 1, 0 => [(0, 1), (2, 1), (2, 1)]
  | false, 1, 1 => [(1, 1)]
  | true, 0, 0 => [(1, 1)]
  | true, 0, 1 => [(0, 1), (1, 1)]
  | true, 1, 0 => [(0, 1)]
  | true, 1, 1 => [(1, 1)]

def actor (i : Bool) (j k : Fin 2) : He :=
  evalPowers (twoGenerator i j) (actorWord i j k)

theorem actor_mem (i : Bool) (j k : Fin 2) : actor i j k ∈ candidateTwo i j :=
  evalPowers_mem _ _ (twoGenerator_mem i j) _

/-- Power products in the marked, rather than original, basis. -/
def markedEmbedding (i : Bool) (j : Fin 2) : Plane →* He :=
  (oddEmbedding i j).comp (basisChange i j).toMonoidHom

theorem markedEmbedding_eq (i : Bool) (j : Fin 2) (v : Plane) :
    markedEmbedding i j v = ((candidateOddEquiv i j).symm v : He) := rfl

end Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.InnerImages
