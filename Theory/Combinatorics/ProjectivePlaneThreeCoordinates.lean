module
public import Theory.Combinatorics.ProjectivePlaneThreeQuadrangle
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

/-!
# Coordinates for the projective plane of order three

A labeling of the six sides of a quadrangle determines the full thirteen-line
incidence table. Matching these labels in two planes gives incidence-preserving
equivalences. The canonical orthogonality plane over `ZMod 3` has thirteen points
and four points on each line, by the projectivization cardinality formula.

The geometric application is Wong, Theorem 6(b), printed p.111,
DOI 10.1017/S1446788700022771.
-/

@[expose] public section

namespace Configuration.Three

/-- The canonical plane over the field with three elements, equipped with
`Configuration.ofField`'s orthogonality incidence. -/
abbrev PG := Projectivization (ZMod 3) (Fin 3 → ZMod 3)

theorem card_pg : Nat.card PG = 13 := by
  rw [Projectivization.card'']
  norm_num [Nat.card_fun, Nat.card_eq_fintype_card]

theorem pointCount_pg (l : PG) : pointCount PG l = 4 := by
  classical
  let : Fintype PG := Fintype.ofFinite PG
  have h := ProjectivePlane.card_points PG PG
  rw [← Nat.card_eq_fintype_card, card_pg] at h
  rw [ProjectivePlane.pointCount_eq]
  have : ProjectivePlane.order PG PG = 3 := by
    nlinarith [sq_nonneg (Int.ofNat (ProjectivePlane.order PG PG) - 3)]
  omega

variable {P L : Type*} [Membership P L] [Finite P] [Finite L]
  [ProjectivePlane P L] (h : ∀ l : L, pointCount P l = 4)

include h

namespace SideChart

variable (c : SideChart P L)

/-- The point labels of a side chart exhaust an order-three plane. -/
noncomputable def pointEquiv : Fin 13 ≃ P :=
  Equiv.ofBijective c.point ((Nat.bijective_iff_injective_and_card c.point).mpr
    ⟨c.point_injective, by simp [card_points h]⟩)

@[simp] theorem pointEquiv_apply (i : Fin 13) : c.pointEquiv h i = c.point i := rfl

/-- The point labels lying on a given line. -/
noncomputable def lineSet (l : L) : Finset (Fin 13) := by
  classical
  exact Finset.univ.filter (fun i => c.point i ∈ l)

omit h [Finite P] [Finite L] [ProjectivePlane P L] in
@[simp] theorem mem_lineSet (i : Fin 13) (l : L) : i ∈ c.lineSet l ↔ c.point i ∈ l := by
  classical
  simp [lineSet]

theorem lineSet_card (l : L) : (c.lineSet l).card = 4 := by
  classical
  have e : {i // i ∈ c.lineSet l} ≃ {p : P // p ∈ l} :=
    (c.pointEquiv h).subtypeEquiv (fun i => by simp)
  have hc := Nat.card_congr e
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hc.trans (h l)

omit h [Finite P] [Finite L] [ProjectivePlane P L] in
theorem lineSet_side (j : Fin 6) : c.lineSet (c.side j) = line (j.castLE (by decide)) := by
  ext i
  simp [c.incident]

theorem lineSet_inter_card {l m : L} (hlm : l ≠ m) :
    (c.lineSet l ∩ c.lineSet m).card = 1 := by
  classical
  obtain ⟨p, hp, hu⟩ := HasPoints.existsUnique_point P L l m hlm
  obtain ⟨i, hi⟩ := (c.pointEquiv h).surjective p
  change c.point i = p at hi
  apply Finset.card_eq_one_iff_existsUnique.mpr
  refine ⟨i, ?_, ?_⟩
  · simp [hi, hp]
  · intro k hk
    apply c.point_injective
    rw [hi]
    exact hu (c.point k) (by simpa using hk)

theorem lineSet_eq_table (l : L) : ∃ i, c.lineSet l = line i := by
  apply classify _ (c.lineSet_card h l)
  intro j
  by_cases hj : l = c.side j
  · left
    rw [hj, c.lineSet_side]
  · right
    rw [← c.lineSet_side]
    exact c.lineSet_inter_card h hj

theorem lineSet_injective : Function.Injective c.lineSet := by
  intro l m hlm
  classical
  have hc := c.lineSet_card h l
  obtain ⟨i, hi, k, hk, hik⟩ := Finset.one_lt_card.mp (show 1 < (c.lineSet l).card by omega)
  have him : c.point i ∈ m := (c.mem_lineSet i m).mp (hlm ▸ hi)
  have hkm : c.point k ∈ m := (c.mem_lineSet k m).mp (hlm ▸ hk)
  exact (Nondegenerate.eq_or_eq ((c.mem_lineSet i l).mp hi)
    ((c.mem_lineSet k l).mp hk) him hkm).resolve_left (fun he => hik (c.point_injective he))

/-- A line is identified by its row in the forced incidence table. -/
noncomputable def lineIndex (l : L) : Fin 13 := (c.lineSet_eq_table h l).choose

theorem lineIndex_spec (l : L) : c.lineSet l = line (c.lineIndex h l) :=
  (c.lineSet_eq_table h l).choose_spec

theorem lineIndex_injective : Function.Injective (c.lineIndex h) := by
  intro l m hlm
  apply c.lineSet_injective h
  rw [c.lineIndex_spec h, c.lineIndex_spec h, hlm]

/-- Every row of the table occurs exactly once among the lines. -/
noncomputable def lineEquiv : L ≃ Fin 13 :=
  Equiv.ofBijective (c.lineIndex h) ((Nat.bijective_iff_injective_and_card _).mpr
    ⟨c.lineIndex_injective h, by simp [card_lines h]⟩)

theorem incident_iff (i : Fin 13) (l : L) :
    c.pointEquiv h i ∈ l ↔ i ∈ line (c.lineEquiv h l) := by
  change c.point i ∈ l ↔ i ∈ line (c.lineIndex h l)
  rw [← c.lineIndex_spec h, c.mem_lineSet]

end SideChart

/-- Two projective planes with four points on every line are isomorphic as
point-line incidence structures. -/
theorem exists_incidence_equiv {P' L' : Type*} [Membership P' L']
    [Finite P'] [Finite L'] [ProjectivePlane P' L']
    (h' : ∀ l : L', pointCount P' l = 4) :
    ∃ (ep : P ≃ P') (el : L ≃ L'), ∀ p l, ep p ∈ el l ↔ p ∈ l := by
  obtain ⟨c⟩ := exists_sideChart h
  obtain ⟨d⟩ := exists_sideChart h'
  refine ⟨(c.pointEquiv h).symm.trans (d.pointEquiv h'),
    (c.lineEquiv h).trans (d.lineEquiv h').symm, ?_⟩
  intro p l
  change d.pointEquiv h' ((c.pointEquiv h).symm p) ∈
    (d.lineEquiv h').symm (c.lineEquiv h l) ↔ p ∈ l
  rw [d.incident_iff, Equiv.apply_symm_apply, ← c.incident_iff, Equiv.apply_symm_apply]

/-- Every abstract projective plane with four points on each line has coordinates
over `ZMod 3`, preserving the canonical orthogonality incidence. -/
theorem exists_coordinates :
    ∃ (ep : P ≃ PG) (el : L ≃ PG), ∀ p l, ep p ∈ el l ↔ p ∈ l :=
  exists_incidence_equiv h pointCount_pg

end Configuration.Three
