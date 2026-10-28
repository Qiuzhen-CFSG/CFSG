module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers.OrbitCounts.Algebra

/-!
# Soundness of finite plane conjugation trees

Each step decreases an explicit natural depth and preserves the proposed rank
by an actual conjugation and basis change. Strong induction reaches the literal
representative pairs. This is the finite coverage step for Aschbacher–Smith
A.3.12, pp.47–48; Kleidman–Wilson (1988), pp.484–510.
-/

@[expose] public section
open Janko4 Janko4.LocalStructure.SylowNormalEights
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.MatrixCertificates.PairCountFibers
attribute [local irreducible] modelGroup matrixA matrixB pairRank point
/-- Depth in a checked finite tree of plane conjugations. -/
def orbitDepth (w : ℕ) : ℕ := w / 128 % 16

def orbitLabel (t : ℕ) [NeZero t] (w : ℕ) : Fin t := Fin.ofNat t (w % 128)

def orbitCoord (i : Fin 9) (w : ℕ) : Fin (candidateOrder i) :=
  ⟨w % candidateOrder i, Nat.mod_lt _ ((by decide +kernel :
    ∀ i : Fin 9, 0 < candidateOrder i) i)⟩

def orbitParent (i : Fin 9) (w : ℕ) : Fin (candidateOrder i) × Fin (candidateOrder i) :=
  (orbitCoord i (w / 65536 % 256), orbitCoord i (w / 16777216 % 256))

def orbitGenerator (w : ℕ) : Fin 21 := Fin.ofNat 21 (w / 2048 % 32)

def orbitDependent (i : Fin 9) (a b : Fin (candidateOrder i)) : Prop :=
  a.val = 0 ∨ b.val = 0 ∨ a = b
instance (i : Fin 9) (a b : Fin (candidateOrder i)) : Decidable (orbitDependent i a b) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

def orbitCode (i : Fin 9) (data : Fin (candidateOrder i) → Fin (candidateOrder i) → ℕ)
    (a b : Fin (candidateOrder i)) : ℕ :=
  data (orbitPlane i a b).1 (orbitPlane i a b).2

/-- The numeric table proposed by a plane-tree witness; it has no rank assertion. -/
def orbitTable (i : Fin 9) {t : ℕ} [NeZero t]
    (values : Fin t → ℕ) (data : Fin (candidateOrder i) → Fin (candidateOrder i) → ℕ)
    (a b : Fin (candidateOrder i)) : ℕ :=
  if orbitDependent i a b then 0 else values (orbitLabel t (orbitCode i data a b))

/-- A local certificate either reaches a specified representative, or gives an
actual generator action from a plane of strictly smaller depth. -/
def OrbitStep (i : Fin 9) {t : ℕ} [NeZero t]
    (left right : Fin t → Fin (candidateOrder i)) (values : Fin t → ℕ)
    (action : Fin 21 → Fin (candidateOrder i) → Fin (candidateOrder i))
    (data : Fin (candidateOrder i) → Fin (candidateOrder i) → ℕ)
    (a b : Fin (candidateOrder i)) : Prop :=
  if orbitDependent i a b then True else
  let w := orbitCode i data a b
  let k := orbitLabel t w
  if orbitDepth w = 0 then orbitPlane i a b = (left k, right k) else
    let p := orbitParent i w
    orbitDepth (orbitCode i data p.1 p.2) < orbitDepth w ∧
    orbitTable i values data p.1 p.2 = orbitTable i values data a b ∧
    orbitPlane i (action (orbitGenerator w) p.1) (action (orbitGenerator w) p.2) =
      orbitPlane i a b

instance (i : Fin 9) {t : ℕ} [NeZero t]
    (left right : Fin t → Fin (candidateOrder i)) (values : Fin t → ℕ)
    (action : Fin 21 → Fin (candidateOrder i) → Fin (candidateOrder i))
    (data : Fin (candidateOrder i) → Fin (candidateOrder i) → ℕ)
    (a b : Fin (candidateOrder i)) :
    Decidable (OrbitStep i left right values action data a b) := by
  unfold OrbitStep
  infer_instance

/-- Boolean form keeps finite checking independent of instance-search transparency
at the concrete coordinate dimensions. Its truth is converted back to the
mathematical step proposition by `orbitStep_of_check`. -/
def orbitCheck (i : Fin 9) {t : ℕ} [NeZero t]
    (left right : Fin t → Fin (candidateOrder i)) (values : Fin t → ℕ)
    (action : Fin 21 → Fin (candidateOrder i) → Fin (candidateOrder i))
    (data : Fin (candidateOrder i) → Fin (candidateOrder i) → ℕ)
    (a b : Fin (candidateOrder i)) : Bool :=
  decide (OrbitStep i left right values action data a b)

theorem orbitStep_of_check (i : Fin 9) {t : ℕ} [NeZero t]
    (left right : Fin t → Fin (candidateOrder i)) (values : Fin t → ℕ)
    (action : Fin 21 → Fin (candidateOrder i) → Fin (candidateOrder i))
    (data : Fin (candidateOrder i) → Fin (candidateOrder i) → ℕ)
    (a b : Fin (candidateOrder i))
    (h : orbitCheck i left right values action data a b = true) :
    OrbitStep i left right values action data a b := of_decide_eq_true h

/-- Soundness of finite plane trees. Only the representative ranks remain as
mathematical inputs after the coordinate actions and finite steps are checked. -/
theorem pairRank_eq_orbitTable (i : Fin 9) (hi : 5 ≤ i.val) {t : ℕ} [NeZero t]
    (left right : Fin t → Fin (candidateOrder i)) (values : Fin t → ℕ)
    (action : Fin 21 → Fin (candidateOrder i) → Fin (candidateOrder i))
    (data : Fin (candidateOrder i) → Fin (candidateOrder i) → ℕ)
    (hact : ∀ j n, (MatrixWords.pcGenerator j : Model)⁻¹ * point i n *
      (MatrixWords.pcGenerator j : Model) = point i (action j n))
    (hstep : ∀ a b, OrbitStep i left right values action data a b)
    (hrep : ∀ k, pairRank (point i (left k)) (point i (right k)) = values k)
    (a b : Fin (candidateOrder i)) :
    pairRank (point i a) (point i b) = orbitTable i values data a b := by
  have main : ∀ d a b, orbitDepth (orbitCode i data a b) = d →
      pairRank (point i a) (point i b) = orbitTable i values data a b := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro a b hd
      by_cases hdep : orbitDependent i a b
      · rw [orbitTable, if_pos hdep]
        rcases hdep with ha | hb | hab
        · have hp : point i a = 1 := by
            have he : a = ⟨0, (by decide +kernel : ∀ i : Fin 9, 0 < candidateOrder i) i⟩ :=
              Fin.ext ha
            rw [he, point_zero]
          rw [hp, pairRank_one_left]
        · have hp : point i b = 1 := by
            have he : b = ⟨0, (by decide +kernel : ∀ i : Fin 9, 0 < candidateOrder i) i⟩ :=
              Fin.ext hb
            rw [he, point_zero]
          rw [hp, pairRank_one_right]
        · subst b
          exact pairRank_point_self i hi a
      · have hs := hstep a b
        simp only [OrbitStep, if_neg hdep] at hs
        by_cases hz : orbitDepth (orbitCode i data a b) = 0
        · rw [if_pos hz] at hs
          calc
            pairRank (point i a) (point i b) =
                pairRank (point i (orbitPlane i a b).1)
                  (point i (orbitPlane i a b).2) := (pairRank_orbitPlane i hi a b).symm
            _ = values (orbitLabel t (orbitCode i data a b)) := by rw [hs]; exact hrep _
            _ = orbitTable i values data a b := by rw [orbitTable, if_neg hdep]
        · rw [if_neg hz] at hs
          let w := orbitCode i data a b
          let p := orbitParent i w
          have hr := ih (orbitDepth (orbitCode i data p.1 p.2))
            (by simpa only [← hd] using hs.1) p.1 p.2 rfl
          calc
            pairRank (point i a) (point i b) =
                pairRank (point i (orbitPlane i (action (orbitGenerator w) p.1)
                  (action (orbitGenerator w) p.2)).1)
                  (point i (orbitPlane i (action (orbitGenerator w) p.1)
                    (action (orbitGenerator w) p.2)).2) := by
              rw [hs.2.2]
              exact (pairRank_orbitPlane i hi a b).symm
            _ = pairRank (point i (action (orbitGenerator w) p.1))
                (point i (action (orbitGenerator w) p.2)) := pairRank_orbitPlane i hi _ _
            _ = pairRank (point i p.1) (point i p.2) := by
              rw [← hact, ← hact]
              simpa only [inv_inv] using pairRank_conjugate
                (MatrixWords.pcGenerator (orbitGenerator w) : Model)⁻¹ (point i p.1) (point i p.2)
            _ = orbitTable i values data p.1 p.2 := hr
            _ = orbitTable i values data a b := hs.2.1
  exact main _ a b rfl

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.MatrixCertificates.PairCountFibers
