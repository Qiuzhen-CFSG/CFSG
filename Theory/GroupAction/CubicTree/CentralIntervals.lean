module

public import Theory.GroupAction.CubicTree.Tracks
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Data.Set.Finite.Lemmas

/-!
# Fixed intervals and central edge intervals on a track

An involution central in an edge stabilizer fixes that edge. When its fixed
locus on the track is finite, there is a longest consecutive interval of edges
whose stabilizers it centralizes. This constructs the two intervals used by
Goldschmidt without assuming that the central interval is unique. Uniqueness is
a later conclusion of the commutator argument.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), Section 6,
printed pp.395--397.
-/

@[expose] public section
namespace Theory.GroupAction.CubicTree
open SimpleGraph Subgroup
universe u v
variable {V : Type u} {G : Type v} {Γ : SimpleGraph V} [Group G] [MulAction G V]
namespace Track

/-- The literal pointwise stabilizer of the edge at positions `i,i+1`. -/
def edgeStabilizer (t : Track Γ G) (i : ℤ) : Subgroup G :=
  MulAction.stabilizer G (t.vertex i) ⊓ MulAction.stabilizer G (t.vertex (i + 1))

/-- Membership in the center of the actual edge stabilizer. -/
def CentralEdge (t : Track Γ G) (z : G) (i : ℤ) : Prop :=
  z ∈ t.edgeStabilizer i ∧ ∀ x ∈ t.edgeStabilizer i, Commute z x

/-- Goldschmidt's `Z(T)`: an involution central in some edge stabilizer. -/
def CentralInvolution (t : Track Γ G) (z : G) : Prop :=
  orderOf z = 2 ∧ ∃ i : ℤ, t.CentralEdge z i

theorem CentralEdge.fixes_left {t : Track Γ G} {z : G} {i : ℤ}
    (hz : t.CentralEdge z i) : z • t.vertex i = t.vertex i := hz.1.1

theorem CentralEdge.fixes_right {t : Track Γ G} {z : G} {i : ℤ}
    (hz : t.CentralEdge z i) : z • t.vertex (i + 1) = t.vertex (i + 1) := hz.1.2

theorem centralEdge_reverse_iff (t : Track Γ G) (z : G) (i : ℤ) :
    t.reverse.CentralEdge z i ↔ t.CentralEdge z (-i - 1) := by
  have he : t.reverse.edgeStabilizer i = t.edgeStabilizer (-i - 1) := by
    change MulAction.stabilizer G (t.vertex (-i)) ⊓
      MulAction.stabilizer G (t.vertex (-(i + 1))) =
      MulAction.stabilizer G (t.vertex (-i - 1)) ⊓
      MulAction.stabilizer G (t.vertex (-i - 1 + 1))
    have h₁ : -(i + 1) = -i - 1 := by omega
    have h₂ : -i - 1 + 1 = -i := by omega
    rw [h₁, h₂, inf_comm]
  simp only [CentralEdge, he]

/-- The fixed interval and a longest central edge interval, with their actual
endpoint indices. Maximality is by length, as in the source. -/
structure CentralInterval (t : Track Γ G) (z : G) where
  fixedLeft : ℤ
  fixedRight : ℤ
  centralLeft : ℤ
  centralRight : ℤ
  fixed_iff : ∀ i, z • t.vertex i = t.vertex i ↔ fixedLeft ≤ i ∧ i ≤ fixedRight
  central_lt : centralLeft < centralRight
  central : ∀ i, centralLeft ≤ i → i < centralRight → t.CentralEdge z i
  maximal : ∀ a b : ℤ, a < b →
    (∀ i, a ≤ i → i < b → t.CentralEdge z i) → b - a ≤ centralRight - centralLeft

namespace CentralInterval
variable {t : Track Γ G} {z : G} (d : t.CentralInterval z)

theorem centralLeft_mem : d.fixedLeft ≤ d.centralLeft ∧ d.centralLeft ≤ d.fixedRight :=
  (d.fixed_iff _).1 (d.central d.centralLeft le_rfl d.central_lt).fixes_left

theorem centralRight_mem : d.fixedLeft ≤ d.centralRight ∧ d.centralRight ≤ d.fixedRight := by
  have hlt := d.central_lt
  have hh := (d.central (d.centralRight - 1) (by omega) (by omega)).fixes_right
  have he : d.centralRight - 1 + 1 = d.centralRight := by omega
  rw [he] at hh
  exact (d.fixed_iff _).1 hh

theorem not_central_right : ¬ t.CentralEdge z d.centralRight := by
  have hlt := d.central_lt
  intro hr
  have hbound := d.maximal d.centralLeft (d.centralRight + 1) (by omega)
    (fun i hi hir => by
      by_cases he : i = d.centralRight
      · exact he ▸ hr
      · exact d.central i hi (by omega))
  omega

theorem not_central_left : ¬ t.CentralEdge z (d.centralLeft - 1) := by
  have hlt := d.central_lt
  intro hl
  have hbound := d.maximal (d.centralLeft - 1) d.centralRight (by omega)
    (fun i hi hir => by
      by_cases he : i = d.centralLeft - 1
      · exact he ▸ hl
      · exact d.central i (by omega) hir)
  omega

def leftMargin : ℕ := (d.centralLeft - d.fixedLeft).toNat
def rightMargin : ℕ := (d.fixedRight - d.centralRight).toNat

@[simp] theorem leftMargin_cast : (d.leftMargin : ℤ) = d.centralLeft - d.fixedLeft :=
  Int.toNat_of_nonneg (sub_nonneg.mpr d.centralLeft_mem.1)

@[simp] theorem rightMargin_cast : (d.rightMargin : ℤ) = d.fixedRight - d.centralRight :=
  Int.toNat_of_nonneg (sub_nonneg.mpr d.centralRight_mem.2)

/-- The same source intervals viewed with the track orientation reversed. -/
def reverse : t.reverse.CentralInterval z where
  fixedLeft := -d.fixedRight
  fixedRight := -d.fixedLeft
  centralLeft := -d.centralRight
  centralRight := -d.centralLeft
  fixed_iff i := by
    change z • t.vertex (-i) = t.vertex (-i) ↔ _
    rw [d.fixed_iff]
    omega
  central_lt := neg_lt_neg d.central_lt
  central i hi hir := (centralEdge_reverse_iff t z i).2
    (d.central (-i - 1) (by omega) (by omega))
  maximal a b hab hcentral := by
    have hh := d.maximal (-b) (-a) (by omega) (fun i hi hir => by
      have he : -(-i - 1) - 1 = i := by omega
      have hh := (centralEdge_reverse_iff t z (-i - 1)).1
        (hcentral (-i - 1) (by omega) (by omega))
      simpa only [he] using hh)
    omega

end CentralInterval

/-- Finite fixed-locus geometry constructs the source's longest central block. -/
theorem exists_centralInterval (t : Track Γ G) (z : G)
    (hz : ∃ i : ℤ, t.CentralEdge z i)
    (hfixed : ∃ a b : ℤ, ∀ i, z • t.vertex i = t.vertex i ↔ a ≤ i ∧ i ≤ b) :
    Nonempty (t.CentralInterval z) := by
  classical
  obtain ⟨a, b, hfixed⟩ := hfixed
  let C : Set (ℤ × ℤ) := {lr | a ≤ lr.1 ∧ lr.1 < lr.2 ∧ lr.2 ≤ b ∧
    ∀ i, lr.1 ≤ i → i < lr.2 → t.CentralEdge z i}
  have hCfin : C.Finite := ((Set.finite_Icc a b).prod (Set.finite_Icc a b)).subset (by
    intro lr hlr
    exact ⟨⟨hlr.1, le_trans hlr.2.1.le hlr.2.2.1⟩,
      ⟨le_trans hlr.1 hlr.2.1.le, hlr.2.2.1⟩⟩)
  have hCne : C.Nonempty := by
    obtain ⟨i, hi⟩ := hz
    refine ⟨(i, i + 1), (hfixed i).1 hi.fixes_left |>.1, by omega,
      (hfixed (i + 1)).1 hi.fixes_right |>.2, ?_⟩
    intro j hij hji
    have he : j = i := by omega
    exact he ▸ hi
  obtain ⟨lr, hlr, hmax⟩ := Set.exists_max_image C (fun lr => lr.2 - lr.1) hCfin hCne
  refine ⟨⟨a, b, lr.1, lr.2, hfixed, hlr.2.1, hlr.2.2.2, ?_⟩⟩
  intro l r hlr' hcentral
  have hleft : a ≤ l := (hfixed l).1 (hcentral l le_rfl hlr').fixes_left |>.1
  have hright : r ≤ b := by
    have hh := (hcentral (r - 1) (by omega) (by omega)).fixes_right
    have he : r - 1 + 1 = r := by omega
    rw [he] at hh
    exact (hfixed r).1 hh |>.2
  exact hmax (l, r) ⟨hleft, hlr', hright, hcentral⟩

end Track
end Theory.GroupAction.CubicTree
