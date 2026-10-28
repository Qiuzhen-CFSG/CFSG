module

public import Theory.Representation.PSL3Two.FanoCoreStructure

/-!
# Literal Fano-core subsets and pencil geometry

The four families in H.5.3 are defined as literal point complements, line
complements, subsets of size two, and complements of bases. The determinant
criterion for a basis is proved equivalent to linear independence. Point and
line transitivity identify the first two orbits and give their cardinalities.
Adding the normals of two distinct lines constructs their third concurrent
line and proves the corresponding addition identity in the core. A point
outside any three chosen points detects a nonzero sum of their complements.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.5.2(1),
H.5.3(3–4), and H.5.4(3), printed pp.385–386. Only the first two orbit
calculations are asserted here.
-/

@[expose] public section

open Matrix Representation BinaryLinearThree BinaryLinearThree.FanoDecomposition
open BinaryLinearThree.FanoCoreStructure
set_option synthInstance.maxSize 256
namespace BinaryLinearThree.FanoLocalStructure

/-- The literal support in the seven-point permutation module. -/
def support (a : Core) : Finset Point := Finset.univ.filter (fun p => a.val p ≠ 0)

/-- The complements of single points. -/
def pointComplements : Set Core := Set.range pointSpike

/-- The complements of projective lines. -/
def lineComplements : Set Core := Set.range lineComplement

/-- The subsets of size two. -/
def weightTwo : Set Core := {a | (support a).card = 2}

/-- An ordered basis, represented by its three nonzero column vectors. -/
def IsBasisTriple (b : Fin 3 → Point) : Prop := Matrix.det (fun i j => (b j).val i) = 1

instance (b : Fin 3 → Point) : Decidable (IsBasisTriple b) :=
  inferInstanceAs (Decidable (_ = _))

/-- The complements of three-element bases of the natural vector space. -/
def basisComplements : Set Core := {a | ∃ b : Fin 3 → Point, IsBasisTriple b ∧
  ∀ p : Point, a.val p = if ∃ i, b i = p then 0 else 1}

/-- The determinant criterion really supplies a basis of the natural module. -/
noncomputable def basisOfTriple (b : Fin 3 → Point) (hb : IsBasisTriple b) :
    Module.Basis (Fin 3) (ZMod 2) Vector := by
  have hi : LinearIndependent (ZMod 2) (fun i => (b i).val) :=
    Matrix.linearIndependent_cols_of_det_ne_zero (by rw [show Matrix.det (fun i j => (b j).val i) = 1 from hb]; exact one_ne_zero)
  exact Module.Basis.mk hi (hi.span_eq_top_of_card_eq_finrank (by simp)).ge

@[simp] theorem basisOfTriple_apply (b : Fin 3 → Point) (hb : IsBasisTriple b) (i : Fin 3) :
    basisOfTriple b hb i = (b i).val := by
  unfold basisOfTriple
  exact Module.Basis.mk_apply _ _ _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem determinant_certificate : ∀ b : Fin 3 → Point,
    IsBasisTriple b ↔ ∀ c : Vector, (∑ i, c i • (b i).val) = 0 → ∀ i, c i = 0 := by
  simp only [IsBasisTriple]
  decide +kernel

/-- Thus the finite predicate is equivalent to linear independence, with no extra hypothesis. -/
theorem isBasisTriple_iff (b : Fin 3 → Point) :
    IsBasisTriple b ↔ LinearIndependent (ZMod 2) (fun i => (b i).val) := by
  rw [Fintype.linearIndependent_iff]
  exact determinant_certificate b

/-- An orbit for the actual six-dimensional core representation. -/
def orbit (a : Core) : Set Core := {b | ∃ g : Group, U₂ g a = b}

theorem pointSpike_injective : Function.Injective pointSpike := by
  intro p q h
  by_contra hpq
  have hh := congrArg (fun a : Core => a.val p) h
  simp only [pointSpike_apply, Pi.single_apply, if_neg hpq] at hh
  exact one_ne_zero (add_right_cancel hh)

theorem lineComplement_injective : Function.Injective lineComplement := by
  intro r s h
  have hf := pointEvaluation_injective h
  have hv := (dotProductEquiv (ZMod 2) (Fin 3)).injective hf
  exact congrArg Matrix.PSL3Two.Fano.Line.mk (Subtype.ext hv)

/-- The line complements transform by the actual contragredient Fano action. -/
theorem lineComplement_action (g : Group) (l : Line) :
    lineComplement (linePerm g l) = U₂ g (lineComplement l) := by
  change pointEvaluation (lineFunctional (linePerm g l)) = _
  rw [lineFunctional_action, pointEvaluation.isIntertwining]
  rfl

/-- The point-complement family is one orbit of the actual core representation. -/
theorem pointComplements_eq_orbit :
    pointComplements = orbit (pointSpike Matrix.PSL3Two.flagPoint) := by
  ext a
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨g, hg⟩ := SimpleHeadQuotientObstruction.point_reachable p
    exact ⟨g, by rw [← pointSpike_action, hg]⟩
  · rintro ⟨g, rfl⟩
    exact ⟨pointPerm g Matrix.PSL3Two.flagPoint, pointSpike_action _ _⟩

/-- Every literal Fano line is reached from the marked line. -/
theorem line_reachable (l : Line) :
    ∃ g : Group, linePerm g Matrix.PSL3Two.flagLine = l := by
  have hp : 0 < Fintype.card {p : Point // Matrix.PSL3Two.Fano.Incident p l} := by
    rw [Matrix.PSL3Two.Fano.points_on_line]
    decide
  obtain ⟨⟨p, hp⟩⟩ := Fintype.card_pos_iff.mp hp
  obtain ⟨g, hg⟩ := markedFlag_reachable ⟨(p, l), hp⟩
  exact ⟨g, congrArg (fun f : Flag => f.val.2) hg⟩

/-- The line-complement family is one orbit of the actual core representation. -/
theorem lineComplements_eq_orbit :
    lineComplements = orbit (lineComplement Matrix.PSL3Two.flagLine) := by
  ext a
  constructor
  · rintro ⟨l, rfl⟩
    obtain ⟨g, hg⟩ := line_reachable l
    exact ⟨g, by rw [← lineComplement_action, hg]⟩
  · rintro ⟨g, rfl⟩
    exact ⟨linePerm g Matrix.PSL3Two.flagLine, lineComplement_action _ _⟩

/-- The first literal family has seven elements. -/
theorem card_pointComplements : Nat.card pointComplements = 7 := by
  change Nat.card (Set.range pointSpike) = 7
  rw [← Nat.card_congr (Equiv.ofInjective pointSpike pointSpike_injective),
    Nat.card_eq_fintype_card, Matrix.PSL3Two.Fano.card_point]

/-- The second literal family has seven elements. -/
theorem card_lineComplements : Nat.card lineComplements = 7 := by
  change Nat.card (Set.range lineComplement) = 7
  rw [← Nat.card_congr (Equiv.ofInjective lineComplement lineComplement_injective),
    Nat.card_eq_fintype_card, Matrix.PSL3Two.Fano.card_line]

/-- The third line in the pencil generated by two distinct lines. -/
def thirdLine (r s : Line) (hrs : r ≠ s) : Line :=
  ⟨⟨r.normal.val + s.normal.val, by
    intro h
    have hn : r.normal.val = s.normal.val := by
      have ht : ∀ v w : Vector, v + w = 0 → v = w := by decide
      exact ht _ _ h
    exact hrs (congrArg Matrix.PSL3Two.Fano.Line.mk (Subtype.ext hn))⟩⟩

theorem lineComplement_add (r s : Line) (hrs : r ≠ s) :
    lineComplement r + lineComplement s = lineComplement (thirdLine r s hrs) := by
  change pointEvaluation (lineFunctional r) + pointEvaluation (lineFunctional s) = _
  rw [← map_add]
  change pointEvaluation (_ + _) = pointEvaluation ((dotProductEquiv (ZMod 2) (Fin 3)) (_ + _))
  rw [LinearEquiv.map_add]
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem pencil_certificate : ∀ r s t : Line, r ≠ s → t ≠ r → t ≠ s →
    ((∃ p : Point, Matrix.PSL3Two.Fano.Incident p r ∧
      Matrix.PSL3Two.Fano.Incident p s ∧ Matrix.PSL3Two.Fano.Incident p t) ↔
    t.normal.val = r.normal.val + s.normal.val) := by decide +kernel

/-- The constructed line is distinct from both inputs and passes through their common point. -/
theorem thirdLine_pencil (r s : Line) (hrs : r ≠ s) :
    thirdLine r s hrs ≠ r ∧ thirdLine r s hrs ≠ s ∧
      ∃ p : Point, Matrix.PSL3Two.Fano.Incident p r ∧
        Matrix.PSL3Two.Fano.Incident p s ∧
        Matrix.PSL3Two.Fano.Incident p (thirdLine r s hrs) := by
  have hr : thirdLine r s hrs ≠ r := by
    intro h
    have hh := congrArg (fun l : Line => l.normal.val) h
    exact s.normal.property (add_eq_left.mp hh)
  have hs : thirdLine r s hrs ≠ s := by
    intro h
    have hh := congrArg (fun l : Line => l.normal.val) h
    exact r.normal.property (add_eq_right.mp hh)
  exact ⟨hr, hs, (pencil_certificate r s _ hrs hr hs).mpr rfl⟩

/-- H.5.2(1), for any third distinct line through the intersection. -/
theorem concurrent_lineComplement_add (r s t : Line) (hrs : r ≠ s)
    (htr : t ≠ r) (hts : t ≠ s)
    (h : ∃ p : Point, Matrix.PSL3Two.Fano.Incident p r ∧
      Matrix.PSL3Two.Fano.Incident p s ∧ Matrix.PSL3Two.Fano.Incident p t) :
    lineComplement r + lineComplement s = lineComplement t := by
  have ht : t = thirdLine r s hrs :=
    congrArg Matrix.PSL3Two.Fano.Line.mk (Subtype.ext
      ((pencil_certificate r s t hrs htr hts).mp h))
  rw [ht]
  exact lineComplement_add r s hrs

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem triple_certificate : ∀ p q r : Point,
    ∃ s : Point, s ≠ p ∧ s ≠ q ∧ s ≠ r := by decide +kernel

/-- H.5.4(3): three distinct point complements never sum to zero. -/
theorem three_pointComplements_ne_zero (a b c : Core)
    (ha : a ∈ pointComplements) (hb : b ∈ pointComplements) (hc : c ∈ pointComplements)
    : a + b + c ≠ 0 := by
  obtain ⟨p, rfl⟩ := ha
  obtain ⟨q, rfl⟩ := hb
  obtain ⟨r, rfl⟩ := hc
  obtain ⟨s, hs⟩ := triple_certificate p q r
  intro h
  have hh := congrArg (fun a : Core => a.val s) h
  change (pointSpike p).val s + (pointSpike q).val s + (pointSpike r).val s = 0 at hh
  simp only [pointSpike_apply, Pi.single_apply, if_neg hs.1, if_neg hs.2.1, if_neg hs.2.2, zero_add] at hh
  exact (by decide : (1 : ZMod 2) + 1 + 1 ≠ 0) hh

end BinaryLinearThree.FanoLocalStructure
