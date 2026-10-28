module
public import Glauberman.FixedNormalPairTripleLattice
public import Glauberman.FixedNormalPairDegreeLattice

/-!
# The last lattice index at the original degree

The full center-covering identity identifies the depth-3v index with
|Z(S):Z(G)|. This argument is independent of the field size. The original
SL₂ consumer proves that index is q and hence reconstructs every row
through depth 3v-1, retaining the original intersection and centers.

Source: Niles, *Pushing-up in finite groups* (1979), Proposition 4.6(g),
printed p.47.
-/

public section
open Subgroup Theory.GroupTheory.SubgroupTransport
namespace Glauberman
variable {G : Type*} [Group G] [Finite G]

/-- Natural commutator covering and the shifted-center estimate force the
intersection index at depth 3v to equal the original index q. -/
theorem IntersectionPair.rectangleStepIndex_triple_eq_index (P : IntersectionPair G)
    (q v : ℕ) (hv : 0 < v)
    (hn : P.left ≤ normalizer (P.left ⊓ P.right : Set G))
    (hgen : ∀ a b : ℕ, 1 ≤ a + b → a + b < 2 * v →
      intervalCell P.equiv a (b + 1) ⊔ intervalCell P.equiv (a + 1) b =
        intervalCell P.equiv a b)
    (hzS : centerIn P.left = intervalCell P.equiv v (v + 1))
    (hzQ : centerIn (P.left ⊓ P.right) = intervalCell P.equiv v v)
    (hzG : center G = intervalCell P.equiv (v + 1) (v + 1))
    (hcomm : ⁅intervalCell P.equiv 0 (2 * v), intervalCell P.equiv v v⁆ ≤
      intervalCell P.equiv v (2 * v))
    (hcover : ⁅centerIn (P.left ⊓ P.right), P.left⁆ ⊔ center G = centerIn P.left)
    (hindex : (center G).relIndex (centerIn P.left) = q) :
    rectangleStepIndex P.equiv (3 * v) = q := by
  have hsupp := intervalCell_left_supplement P.equiv (2 * v) (by omega)
    (fun b hb hw => hgen 0 b (by omega) (by omega))
  have hecomm := commutator_eq_of_centralizing_sup
    ((sup_comm _ _).trans hsupp)
    (le_centralizer_iff.mp (show centerIn (P.left ⊓ P.right) ≤
      centralizer (P.left ⊓ P.right : Set G) from inf_le_right))
    ((show intervalCell P.equiv 0 (2 * v) ≤ P.left from
      le_sup_left.trans hsupp.le).trans
        (normalizes_centerIn (S := P.left ⊓ P.right) (A := P.left) hn))
  have hfull : ⁅centerIn (P.left ⊓ P.right), P.left⁆ ≤ intervalCell P.equiv v (2 * v) := by
    calc
      ⁅centerIn (P.left ⊓ P.right), P.left⁆ =
          ⁅centerIn (P.left ⊓ P.right), intervalCell P.equiv 0 (2 * v)⁆ := hecomm.symm
      _ = ⁅intervalCell P.equiv 0 (2 * v), intervalCell P.equiv v v⁆ := by
        rw [hzQ, commutator_comm]
      _ ≤ _ := hcomm
  have he : intervalCell P.equiv v (2 * v) ⊔ center G = centerIn P.left := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · rw [hzS]
        exact intervalCell_antitone P.equiv le_rfl (by omega)
      · rw [hzS, hzG]
        exact intervalCell_antitone P.equiv (by omega) le_rfl
    · rw [← hcover]
      exact sup_le_sup_right hfull _
  have hi := relIndex_sup_right (intervalCell P.equiv v (2 * v)) (center G)
  rw [he, hindex] at hi
  rw [← inf_relIndex_right, hzG, intervalCell_inf,
    max_eq_left (show v ≤ v + 1 by omega), max_eq_right (show v + 1 ≤ 2 * v by omega),
    intervalCell_relIndex P.equiv v (2 * v) (v + 1) (2 * v)
      (by omega) le_rfl (by omega)] at hi
  simpa only [show v + 2 * v = 3 * v by omega] using hi.symm


end Glauberman
