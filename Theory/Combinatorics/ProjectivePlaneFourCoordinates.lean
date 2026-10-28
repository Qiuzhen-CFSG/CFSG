module
public import Theory.Combinatorics.ProjectivePlaneFourGrid
public import Theory.Combinatorics.ProjectivePlaneFourTable

/-!
# Uniqueness of the projective plane of order four

The affine grid normalizes one diagonal. The next diagonal has two possible
labelings, interchanged by swapping the remaining ideal points. The small table
certificate then forces every line. Matching this table gives actual incidence
equivalences between any two planes of order four.

This is the elementary plane-recognition input used in the PSL₃(4) branch of
Aschbacher–Smith F.4.8(2), printed p.278, and F.4.26, printed p.288.
-/
section
noncomputable section
namespace Configuration.Four

def label : Fin 21 ≃ ((Fin 4 × Fin 4) ⊕ Fin 5) := Equiv.ofBijective
  ![.inl (0,0),.inl (0,1),.inl (0,2),.inl (0,3),
    .inl (1,0),.inl (1,1),.inl (1,2),.inl (1,3),
    .inl (2,0),.inl (2,1),.inl (2,2),.inl (2,3),
    .inl (3,0),.inl (3,1),.inl (3,2),.inl (3,3),
    .inr 0,.inr 1,.inr 2,.inr 3,.inr 4] (by decide +kernel)

structure GridChart (P L : Type*) [Membership P L] where
  point : Fin 21 ≃ P
  side : Fin 10 → L
  incident : ∀ i j, point i ∈ side j ↔ i ∈ line (j.castLE (by decide))

structure SideChart (P L : Type*) [Membership P L] extends GridChart P L where
  extra : L
  extra_incident : (∀ i, point i ∈ extra ↔ i ∈ line 10) ∨
    (∀ i, point i ∈ extra ↔ i ∈ line 11)

variable {P L : Type*} [Membership P L]

private def gridIncidence (x : ((Fin 4 × Fin 4) ⊕ Fin 5)) (j : Fin 10) : Prop :=
  (match x with
    | .inl (a,b) => ![false, decide (a=0), decide (a=1), decide (a=2), decide (a=3),
        decide (b=0), decide (b=1), decide (b=2), decide (b=3), decide (a=b)] j
    | .inr a => ![true, decide (a=0), decide (a=0), decide (a=0), decide (a=0),
        decide (a=1), decide (a=1), decide (a=1), decide (a=1), decide (a=2)] j) = true
private instance (x : ((Fin 4 × Fin 4) ⊕ Fin 5)) (j : Fin 10) :
    Decidable (gridIncidence x j) := inferInstanceAs (Decidable (_ = true))
private theorem label_incidence : ∀ (i : Fin 21) (j : Fin 10),
    gridIncidence (label i) j ↔ i ∈ line (j.castLE (by decide)) := by decide +kernel

/-- Convert the geometric grid to the finite labels of the incidence table. -/
def Grid.toChart (g : Grid (P := P) (L := L)) : GridChart P L where
  point := label.trans g.point
  side := ![g.infinity, g.vertical 0, g.vertical 1, g.vertical 2, g.vertical 3,
    g.horizontal 0, g.horizontal 1, g.horizontal 2, g.horizontal 3, g.diagonal]
  incident i j := by
    rw [← label_incidence]
    change g.point (label i) ∈ _ ↔ _
    generalize label i = x
    rcases x with ⟨a,b⟩ | k <;> fin_cases j <;>
      simp [gridIncidence, g.infinity_affine, g.infinity_ideal, g.vertical_affine,
        g.vertical_ideal, g.horizontal_affine, g.horizontal_ideal, g.diagonal_affine,
        g.diagonal_ideal]

namespace GridChart
variable (c : GridChart P L)

def lineSet (l : L) : Finset (Fin 21) := by
  classical
  exact Finset.univ.filter (fun i => c.point i ∈ l)

@[simp] theorem mem_lineSet (i : Fin 21) (l : L) : i ∈ c.lineSet l ↔ c.point i ∈ l := by
  classical
  simp [lineSet]

theorem lineSet_side (j : Fin 10) : c.lineSet (c.side j) = line (j.castLE (by decide)) := by
  ext i; simp [c.incident]

variable [Finite P] [Finite L] [ProjectivePlane P L]
variable (h : ∀ l : L, pointCount P l = 5)
include h

omit [Finite P] [Finite L] [ProjectivePlane P L] in
theorem lineSet_card (l : L) : (c.lineSet l).card = 5 := by
  classical
  have e : {i // i ∈ c.lineSet l} ≃ {p : P // p ∈ l} :=
    c.point.subtypeEquiv (fun i => by simp)
  have hc := Nat.card_congr e
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hc.trans (h l)

omit h [Finite P] [Finite L] in
theorem lineSet_compatible (l m : L) : compatible (c.lineSet l) (c.lineSet m) := by
  classical
  by_cases he : l = m
  · exact Or.inl (congrArg c.lineSet he)
  right
  obtain ⟨p,hp,hu⟩ := HasPoints.existsUnique_point P L l m he
  apply Finset.card_eq_one_iff_existsUnique.mpr
  refine ⟨c.point.symm p, ?_, ?_⟩
  · simp [hp]
  · intro i hi
    apply c.point.injective
    rw [Equiv.apply_symm_apply]
    exact hu (c.point i) (by simpa using hi)

omit h [Finite P] [Finite L] in
theorem lineSet_firstTen (l : L) : firstTen (c.lineSet l) := by
  intro j
  rw [← c.lineSet_side]
  exact c.lineSet_compatible l (c.side j)

end GridChart

private def swap : Equiv.Perm (Fin 21) := Equiv.swap 19 20
private theorem swap_firstTen : ∀ (i : Fin 21) (j : Fin 10),
    swap i ∈ line (j.castLE (by decide)) ↔ i ∈ line (j.castLE (by decide)) := by
  decide +kernel
private theorem swap_extra : ∀ i : Fin 21,
    swap i ∈ ({0,7,9,14,19} : Finset (Fin 21)) ↔ i ∈ line 11 := by
  decide +kernel

variable [Finite P] [Finite L] [ProjectivePlane P L]
variable (h : ∀ l : L, pointCount P l = 5)
include h

/-- Extend a grid by a second diagonal, normalizing its ideal-point labeling. -/
theorem exists_sideChart : Nonempty (SideChart P L) := by
  classical
  obtain ⟨g⟩ := exists_grid h
  let c := g.toChart
  have hne : c.point 0 ≠ c.point 19 := c.point.injective.ne (by decide)
  let e : L := HasLines.mkLine hne
  obtain ⟨h0,h19⟩ := HasLines.mkLine_ax (L := L) hne
  change c.point 0 ∈ e at h0
  change c.point 19 ∈ e at h19
  have hc := extra_cases (c.lineSet e) (c.lineSet_card h e) (c.lineSet_firstTen e)
    ((c.mem_lineSet 0 e).mpr h0) ((c.mem_lineSet 19 e).mpr h19)
  rcases hc with hc | hc
  · refine ⟨{ toGridChart := c, extra := e, extra_incident := Or.inl ?_ }⟩
    intro i
    rw [← c.mem_lineSet, hc]
  · let d : GridChart P L := {
      point := swap.trans c.point
      side := c.side
      incident i j := (c.incident (swap i) j).trans (swap_firstTen i j) }
    refine ⟨{ toGridChart := d, extra := e, extra_incident := Or.inr ?_ }⟩
    intro i
    change c.point (swap i) ∈ e ↔ i ∈ line 11
    rw [← c.mem_lineSet, hc, swap_extra]

namespace SideChart
variable (c : SideChart P L)

omit [Finite P] [Finite L] in
theorem lineSet_eq_table (l : L) : ∃ i, c.lineSet l = line i := by
  apply classify _ (c.toGridChart.lineSet_card h l) (c.toGridChart.lineSet_firstTen l)
  have he := c.toGridChart.lineSet_compatible l c.extra
  rcases c.extra_incident with hi | hi
  · have hc : c.lineSet c.extra = line 10 := by ext i; simp [hi]
    exact Or.inl (hc ▸ he)
  · have hc : c.lineSet c.extra = line 11 := by ext i; simp [hi]
    exact Or.inr (hc ▸ he)

omit [Finite P] [Finite L] in
theorem lineSet_injective : Function.Injective c.lineSet := by
  intro l m hlm
  classical
  have hc := c.toGridChart.lineSet_card h l
  obtain ⟨i,hi,k,hk,hik⟩ := Finset.one_lt_card.mp (show 1 < (c.lineSet l).card by omega)
  have him : c.point i ∈ m := (c.toGridChart.mem_lineSet i m).mp (hlm ▸ hi)
  have hkm : c.point k ∈ m := (c.toGridChart.mem_lineSet k m).mp (hlm ▸ hk)
  exact (Nondegenerate.eq_or_eq ((c.toGridChart.mem_lineSet i l).mp hi)
    ((c.toGridChart.mem_lineSet k l).mp hk) him hkm).resolve_left
      (fun he => hik (c.point.injective he))

def lineIndex (l : L) : Fin 21 := (c.lineSet_eq_table h l).choose

omit [Finite P] [Finite L] in
theorem lineIndex_spec (l : L) : c.lineSet l = line (c.lineIndex h l) :=
  (c.lineSet_eq_table h l).choose_spec

omit [Finite P] [Finite L] in
theorem lineIndex_injective : Function.Injective (c.lineIndex h) := by
  intro l m he
  apply c.lineSet_injective h
  rw [c.lineIndex_spec h, c.lineIndex_spec h, he]

def lineEquiv : L ≃ Fin 21 := Equiv.ofBijective (c.lineIndex h)
  ((Nat.bijective_iff_injective_and_card _).mpr
    ⟨c.lineIndex_injective h, by rw [card_lines h, Nat.card_fin]⟩)

theorem incident_iff (i : Fin 21) (l : L) :
    c.point i ∈ l ↔ i ∈ line (c.lineEquiv h l) := by
  change c.point i ∈ l ↔ i ∈ line (c.lineIndex h l)
  rw [← c.lineIndex_spec h, c.toGridChart.mem_lineSet]
end SideChart

/-- Any two finite projective planes with five points on each line are isomorphic
as their actual point-line incidence structures. -/
public theorem exists_incidence_equiv {P' L' : Type*} [Membership P' L']
    [Finite P'] [Finite L'] [ProjectivePlane P' L']
    (h' : ∀ l : L', pointCount P' l = 5) :
    ∃ (ep : P ≃ P') (el : L ≃ L'), ∀ p l, ep p ∈ el l ↔ p ∈ l := by
  obtain ⟨c⟩ := exists_sideChart h
  obtain ⟨d⟩ := exists_sideChart h'
  refine ⟨c.point.symm.trans d.point,
    (c.lineEquiv h).trans (d.lineEquiv h').symm, ?_⟩
  intro p l
  change d.point (c.point.symm p) ∈ (d.lineEquiv h').symm (c.lineEquiv h l) ↔ p ∈ l
  rw [d.incident_iff h', Equiv.apply_symm_apply, ← c.incident_iff h, Equiv.apply_symm_apply]
end Configuration.Four
