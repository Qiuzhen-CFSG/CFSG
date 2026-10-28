module

public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Algebra.Ring.Parity

/-!+# Geometric inputs for the rank-two normalizer argument

The incidence graph of a split group of type G₂ has diameter six, no cycles
shorter than twelve, and odd-order pointwise apartment stabilizers in
characteristic two. These are geometric and stabilizer statements, not a
normalizer-cover assumption. A nonidentity two-subgroup cannot fix an apartment.
Its normalizer preserves its fixed vertices.

The finite-tree argument and the verification for the octonion model are
separate from this interface. The application is the Borel--Tits step in the
generic case of Aschbacher--Smith, *The Classification of Quasithin Groups*,
Theorem 0.1.2(1), printed pp.3--4 (repeated on pp.481--482).
-/

@[expose] public section

namespace Atlas.G2.EvenLocal.NormalizerCover

variable {G X : Type*} [Group G] [MulAction G X]

/-- Vertices fixed by every element of the indicated ambient subgroup. -/
def fixedVertices (R : Subgroup G) : Set X := {x | ∀ r ∈ R, r • x = x}

/-- The structural properties used from the split generalized hexagon.
In particular, this record contains no normalizer fixed-point assertion. -/
structure HexagonData (Γ : SimpleGraph X) (color : X → Bool) : Prop where
  adjacent_color : ∀ {x y}, Γ.Adj x y → color x ≠ color y
  smul_adj : ∀ (g : G) {x y}, Γ.Adj x y → Γ.Adj (g • x) (g • y)
  smul_color : ∀ (g : G) (x : X), color (g • x) = color x
  diameter_bound : ∀ x y, ∃ w : Γ.Walk x y, w.length ≤ 6
  cycle_bound : ∀ x (w : Γ.Walk x x), w.IsCycle → 12 ≤ w.length
  apartment_stabilizer_odd : ∀ x (w : Γ.Walk x x), w.IsCycle → w.length = 12 →
    Odd (Nat.card (fixingSubgroup G {v | v ∈ w.support}))

/-- Normalization, rather than centralization, suffices to preserve the full
fixed vertex set. -/
theorem normalizer_smul_mem_fixedVertices (R : Subgroup G)
    {g : G} (hg : g ∈ Subgroup.normalizer (R : Set G))
    {x : X} (hx : x ∈ fixedVertices R) : g • x ∈ fixedVertices R := by
  intro r hr
  have hc : g⁻¹ * r * g ∈ R := by
    simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (R : Set G)).inv_mem hg) r).mp hr
  calc
    r • (g • x) = g • ((g⁻¹ * r * g) • x) := by simp [mul_smul]
    _ = g • x := congrArg (g • ·) (hx _ hc)

/-- A nonidentity two-subgroup cannot fix a twelve-cycle pointwise when its
pointwise stabilizer has odd order. -/
theorem not_fixed_apartment [Finite G] {Γ : SimpleGraph X} {color : X → Bool}
    (hΓ : HexagonData (G := G) Γ color) (R : Subgroup G)
    (hR : R ≠ ⊥) (hp : IsPGroup 2 R)
    (x : X) (w : Γ.Walk x x) (hw : w.IsCycle) (hl : w.length = 12) :
    ¬ ∀ v ∈ w.support, v ∈ fixedVertices R := by
  intro hfix
  have hle : R ≤ fixingSubgroup G {v | v ∈ w.support} := by
    intro r hr
    exact (fun v => hfix v.val v.property r hr)
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hn0 : n ≠ 0 := by
    intro h
    apply hR
    apply Subgroup.card_eq_one.mp
    simpa [h] using hn
  have hd : 2 ∣ Nat.card R := by
    rw [hn]
    exact dvd_pow_self 2 hn0
  exact (hΓ.apartment_stabilizer_odd x w hw hl).not_two_dvd_nat
    (hd.trans (Subgroup.card_dvd_of_le hle))

end Atlas.G2.EvenLocal.NormalizerCover
