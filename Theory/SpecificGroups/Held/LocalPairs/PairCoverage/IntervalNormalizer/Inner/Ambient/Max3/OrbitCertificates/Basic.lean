module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.OrbitData
import Mathlib.Tactic.FinCases
/-!
# Checking orbit partitions of the literal max3 entries

A certificate labels each vertex by a component and supplies a rooted spanning
forest using the eight Schreier generators. Generator invariance extends to the
subgroup closure. Decreasing depth proves that every vertex is reached from its
component representative, so the actual orbits are exactly the component fibers.
Counting these fibers then identifies the published size labels.

The four generator lookup permutations are already proved equal to the actual
Held words in `TwoGroup.Tables`. In particular the finite checks use the original
GAP-inversion convention and certify the action of `selectedEntry`, without any
hypothesis about simplicity, normalizers, or the representative orbit sizes.

Sources: the literal ATLAS HeG1-p2058B0/max3 permutations and representative
words, accompanying the max3 local calculation of GLS3 Table 5.3p.
-/

@[expose] public section

open Subgroup
open Held.LocalPairs.SylowGeometry.Calculations
namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.OrbitCertificates

def lookup : Fin 4 → Equiv.Perm (Fin 2058)
  | 0 => TwoGroup.Tables.g0
  | 1 => TwoGroup.Tables.g1
  | 2 => TwoGroup.Tables.g2
  | 3 => TwoGroup.Tables.g3

theorem lookup_eq (j : Fin 4) : lookup j = representation (fixedGenerator false j) := by
  rw [fixedGenerator_false]
  fin_cases j
  · exact TwoGroup.Tables.g0_eq
  · exact TwoGroup.Tables.g1_eq
  · exact TwoGroup.Tables.g2_eq
  · exact TwoGroup.Tables.g3_eq

def wordAction (t : Fin 7) (e : Bool) (j : Fin 4) : Equiv.Perm (Fin 2058) :=
  indexTwoGenerator lookup (labelPivot t) (labelMask t) e j

def actor (t : Fin 7) (e : Bool) (j : Fin 4) : selectedEntry t :=
  ⟨indexTwoGenerator (fixedGenerator false) (labelPivot t) (labelMask t) e j,
    subset_closure ⟨e, j, rfl⟩⟩

theorem actor_smul (t : Fin 7) (e : Bool) (j : Fin 4) (x : Fin 2058) :
    actor t e j • x = wordAction t e j x := by
  change representation (indexTwoGenerator (fixedGenerator false) _ _ e j) x = _
  simp only [wordAction, indexTwoGenerator, map_mul, map_inv, apply_ite, map_one, lookup_eq]

structure Data where
  componentCode : ℕ
  rootCode : ℕ
  treeCode : ℕ
  sizeCode : ℕ

def Data.component (d : Data) (x : Fin 2058) : Fin 36 :=
  ⟨(d.componentCode >>> (6 * x.val)) % 64 % 36, Nat.mod_lt _ (by decide)⟩
def Data.root (d : Data) (c : Fin 36) : Fin 2058 :=
  ⟨(d.rootCode >>> (12 * c.val)) % 4096 % 2058, Nat.mod_lt _ (by decide)⟩
def Data.parent (d : Data) (x : Fin 2058) : Fin 2058 :=
  ⟨(d.treeCode >>> (20 * x.val)) % 4096 % 2058, Nat.mod_lt _ (by decide)⟩
def Data.edgeSide (d : Data) (x : Fin 2058) : Bool :=
  (d.treeCode >>> (20 * x.val)).testBit 14
def Data.edgeIndex (d : Data) (x : Fin 2058) : Fin 4 :=
  ⟨(d.treeCode >>> (20 * x.val + 12)) % 4, Nat.mod_lt _ (by decide)⟩
def Data.depth (d : Data) (x : Fin 2058) : ℕ :=
  (d.treeCode >>> (20 * x.val + 15)) % 32
def Data.size (d : Data) (c : Fin 36) : ℕ :=
  (d.sizeCode >>> (10 * c.val)) % 1024

structure Valid (t : Fin 7) (d : Data) : Prop where
  invariant : ∀ (e : Bool) (j : Fin 4) (x : Fin 2058),
    d.component (wordAction t e j x) = d.component x
  tree : ∀ x : Fin 2058, x = d.root (d.component x) ∨
    (d.depth (d.parent x) < d.depth x ∧ d.component (d.parent x) = d.component x ∧
      wordAction t (d.edgeSide x) (d.edgeIndex x) (d.parent x) = x)
  sizes : ∀ c : Fin 36,
    (List.finRange 2058).countP (fun x => d.component x == c) = d.size c
  labels : ∀ x : Fin 2058, orbitSizeLabel t x = d.size (d.component x)

variable {t : Fin 7} {d : Data}

theorem reach (h : Valid t d) (x : Fin 2058) :
    ∃ g : selectedEntry t, g • d.root (d.component x) = x := by
  suffices hreach : ∀ n : ℕ, ∀ y, d.depth y = n →
      ∃ g : selectedEntry t, g • d.root (d.component y) = y from
    hreach (d.depth x) x rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro y hy
    rcases h.tree y with he | ⟨hd, hc, hs⟩
    · exact ⟨1, by simpa using he.symm⟩
    · obtain ⟨g, hg⟩ := ih (d.depth (d.parent y)) (by omega) (d.parent y) rfl
      rw [hc] at hg
      exact ⟨actor t (d.edgeSide y) (d.edgeIndex y) * g,
        by rw [mul_smul, hg, actor_smul, hs]⟩

theorem invariant (h : Valid t d) (g : selectedEntry t) (x : Fin 2058) :
    d.component (g • x) = d.component x := by
  have hh : ∀ (g : He), g ∈ selectedEntry t → ∀ x : Fin 2058,
      d.component (g • x) = d.component x := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨e, j, rfl⟩ := hg
      intro x
      exact (actor_smul t e j x) ▸ h.invariant e j x
    | one => intro x; rw [one_smul]
    | mul a b ha hb ia ib => intro x; rw [mul_smul, ia, ib]
    | inv a ha ia =>
      intro x
      simpa only [smul_inv_smul] using (ia (a⁻¹ • x)).symm
  exact hh g g.property x

theorem orbit_eq (h : Valid t d) (x : Fin 2058) :
    MulAction.orbit (selectedEntry t) x = {y | d.component y = d.component x} := by
  ext y
  constructor
  · rintro ⟨g, rfl⟩
    exact invariant h g x
  · intro hy
    obtain ⟨gx, hx⟩ := reach h x
    obtain ⟨gy, hgy⟩ := reach h y
    rw [hy] at hgy
    exact ⟨gy * gx⁻¹, by change (gy * gx⁻¹) • x = y; rw [mul_smul, ← hx, inv_smul_smul, hgy]⟩

theorem label_eq_card (h : Valid t d) (x : Fin 2058) :
    orbitSizeLabel t x = Nat.card (MulAction.orbit (selectedEntry t) x) := by
  rw [orbit_eq h x, h.labels x, Nat.card_eq_fintype_card, Fintype.card_subtype,
    ← List.toFinset_finRange 2058, (List.nodup_finRange 2058).card_eq_countP]
  exact (h.sizes (d.component x)).symm
end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.OrbitCertificates
