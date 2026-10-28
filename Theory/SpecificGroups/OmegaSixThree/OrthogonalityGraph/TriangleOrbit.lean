module
public import Theory.SpecificGroups.OmegaSixThree.OrthogonalityGraph.Action
public import Theory.SpecificGroups.OmegaSixThree.OrthogonalityGraph.Coordinates
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.LinearCombination
/-!
# One orbit on ternary orthogonal triangles

Every ordered triangle in the literal quotient graph is an image of the
standard points represented by `e₅`, `e₀-e₁`, and `e₀+e₁`. We first move a
point, then move its neighbor while fixing that point, and finally move a
common neighbor while fixing both earlier points. Each move is a commutator
of two norm-one reflections, so it belongs to the actual derived orthogonal
group by construction.

The three short coordinate tables supply reflection vectors for 117 points,
36 neighbors, and 15 common neighbors. Lean's kernel checks their norms,
fixed vectors, and action on the existing exhaustive point coordinates.
Only these witnesses are finite computations; the isometry, group membership,
quotient action, and assembly arguments are structural.

Source: Aschbacher–Smith, Lemma F.5.8(1), printed pp.303–304. The tables give
an explicit version of the source's Witt-lemma transport in this six-space.
-/

section
namespace OmegaSixThree.OrthogonalityGraph.TriangleCertificate
open SixTernaryCoordinates
private theorem pairing_add_right (a x y : Space) :
    pairing a (x+y) = pairing a x + pairing a y := by
  simp only [pairing, Pi.add_apply]
  ring
private theorem pairing_smul_right (a x : Space) (c : ZMod 3) :
    pairing a (c • x) = c * pairing a x := by
  rw [pairing_symm, pairing_smul_left, pairing_symm]
def reflect (a x : Space) : Space := x + pairing a x • a
private theorem reflect_involutive (a : Space) (ha : quadratic a = 1) :
    Function.Involutive (reflect a) := by
  intro x
  ext i
  simp only [reflect, pairing_add_right, pairing_smul_right, pairing_self, ha,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring_nf
  simp [show (3 : ZMod 3) = 0 by decide]
private theorem quadratic_smul (c : ZMod 3) (a : Space) :
    quadratic (c • a) = c^2 * quadratic a := by
  simp only [quadratic, Pi.smul_apply, smul_eq_mul]
  ring
private theorem reflect_norm (a : Space) (ha : quadratic a = 1) (x : Space) :
    quadratic (reflect a x) = quadratic x := by
  have h := polar_eq x (pairing a x • a)
  rw [quadratic_smul, ha, pairing_smul_right, pairing_symm x a] at h
  have hc : (3 : ZMod 3) = 0 := by decide
  change quadratic (x + pairing a x • a) = quadratic x
  linear_combination h + (pairing a x)^2 * hc

def reflection (a : Space) (ha : quadratic a = 1) : LinearGroup where
  toFun := reflect a
  invFun := reflect a
  left_inv := reflect_involutive a ha
  right_inv := reflect_involutive a ha
  map_add' x y := by
    simp only [reflect, pairing_add_right, add_smul]
    abel
  map_smul' c x := by
    simp only [reflect, pairing_smul_right, smul_add, smul_smul, RingHom.id_apply]

theorem reflection_mem (a : Space) (ha : quadratic a = 1) :
    reflection a ha ∈ orthogonalGroup := reflect_norm a ha

def mover (a b : Space) (ha : quadratic a = 1) (hb : quadratic b = 1) : omegaPlusSixThree :=
  ⟨commutatorWord (reflection a ha) (reflection b hb),
    commutatorWord_mem_omegaPlusSixThree (reflection_mem a ha) (reflection_mem b hb)⟩

theorem mover_apply (a b : Space) (ha : quadratic a = 1) (hb : quadratic b = 1) (x : Space) :
    (mover a b ha hb).val x = reflect a (reflect b (reflect a (reflect b x))) := rfl

private def vector (n : Nat) : Space := fun k => (n / 3 ^ k.val : Nat)
private def baseVector (k : Fin 3) : Space :=
  ![![0,0,0,0,0,1], ![1,2,0,0,0,0], ![1,1,0,0,0,0]] k
private def Moves (a b x y : Space) : Prop :=
  reflect a (reflect b (reflect a (reflect b x))) = y ∨
  reflect a (reflect b (reflect a (reflect b x))) = -y

private def codes0 (i : Fin 117) : Nat × Nat :=
  (#[(81,81),(81,351),(81,432),(81,333),(81,414),(27,279),(432,306),(432,657),(351,306),(351,576),(27,306),(351,414),(351,522),(432,333),(432,522),(81,327),(81,408),(27,273),(432,300),(432,651),(351,300),(351,570),(27,300),(351,408),(351,516),(432,327),(432,516),(351,120),(414,264),(414,651),(333,264),(333,570),(306,264),(306,543),(279,264),(279,516),(351,129),(333,408),(333,498),(414,327),(414,498),(279,300),(279,498),(306,273),(306,498),(81,325),(81,406),(27,271),(432,298),(432,649),(351,298),(351,568),(27,298),(351,406),(351,514),(432,325),(432,514),(351,118),(414,262),(414,649),(333,262),(333,568),(306,262),(306,541),(279,262),(279,514),(351,127),(333,406),(333,496),(414,325),(414,496),(279,298),(279,496),(306,271),(306,496),(351,112),(279,364),(279,643),(279,445),(279,724),(333,364),(333,697),(333,391),(333,724),(351,364),(351,715),(81,364),(81,445),(81,391),(81,472),(351,373),(351,724),(81,373),(81,454),(81,400),(81,481),(351,115),(279,367),(279,646),(279,448),(279,727),(333,367),(333,700),(333,394),(333,727),(351,367),(351,718),(81,367),(81,448),(81,394),(81,475),(351,376),(351,727),(81,376),(81,457),(81,403),(81,484)] : Array (Nat × Nat))[i]
private theorem checked0 : ∀ i : Fin 117,
    quadratic (vector (codes0 i).1) = 1 ∧ quadratic (vector (codes0 i).2) = 1 ∧
    Moves (vector (codes0 i).1) (vector (codes0 i).2) (baseVector 0) (Certificate.coords i) := by
  unfold Moves
  decide +kernel

private def codes1 (i : Fin 117) : Nat × Nat :=
  (#[(81,81),(81,115),(81,196),(81,97),(81,178),(27,43),(81,81),(81,81),(81,81),(81,81),(27,70),(81,81),(81,81),(81,81),(81,81),(120,154),(201,235),(120,208),(81,81),(81,81),(81,81),(81,81),(147,235),(81,81),(81,81),(81,81),(81,81),(120,226),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(129,235),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(120,43),(201,43),(120,97),(81,81),(81,81),(81,81),(81,81),(147,97),(81,81),(81,81),(81,81),(81,81),(120,115),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(129,115),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(3,115),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,237),(81,156),(81,210),(81,129),(81,81),(81,81),(81,228),(81,147),(81,201),(81,120),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(3,120),(3,201),(3,147),(3,228),(81,81),(81,81),(3,129),(3,210),(3,156),(3,237)] : Array (Nat × Nat))[i]
private theorem checked1 : ∀ i : Fin 117,
    pairing (baseVector 0) (Certificate.coords i) = 0 →
    quadratic (vector (codes1 i).1) = 1 ∧ quadratic (vector (codes1 i).2) = 1 ∧
    pairing (vector (codes1 i).1) (baseVector 0) = 0 ∧
    pairing (vector (codes1 i).2) (baseVector 0) = 0 ∧
    Moves (vector (codes1 i).1) (vector (codes1 i).2) (baseVector 1) (Certificate.coords i) := by
  unfold Moves
  decide +kernel

private def codes2 (i : Fin 117) : Nat × Nat :=
  (#[(81,81),(81,112),(81,193),(81,94),(81,175),(27,40),(81,81),(81,81),(81,81),(81,81),(27,67),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(193,67),(112,67),(112,175),(193,94),(81,81),(81,81),(193,76),(112,76),(112,184),(193,103),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81),(81,81)] : Array (Nat × Nat))[i]
private theorem checked2 : ∀ i : Fin 117,
    pairing (baseVector 0) (Certificate.coords i) = 0 →
    pairing (baseVector 1) (Certificate.coords i) = 0 →
    quadratic (vector (codes2 i).1) = 1 ∧ quadratic (vector (codes2 i).2) = 1 ∧
    pairing (vector (codes2 i).1) (baseVector 0) = 0 ∧
    pairing (vector (codes2 i).2) (baseVector 0) = 0 ∧
    pairing (vector (codes2 i).1) (baseVector 1) = 0 ∧
    pairing (vector (codes2 i).2) (baseVector 1) = 0 ∧
    Moves (vector (codes2 i).1) (vector (codes2 i).2) (baseVector 2) (Certificate.coords i) := by
  unfold Moves
  decide +kernel


private theorem baseVector_norm : ∀ k, quadratic (baseVector k) = -1 := by decide +kernel
private def basePoint (k : Fin 3) : Point := point (baseVector k) (baseVector_norm k)
private def indexedPoint (i : Fin 117) : Point := point (Certificate.coords i) (Certificate.coords_norm i)
private theorem indexedPoint_surjective : Function.Surjective indexedPoint := by
  intro x
  induction x using Quotient.inductionOn with | h v =>
    obtain ⟨i, hi⟩ := Certificate.coords_complete v.val v.property
    exact ⟨i, (point_eq_iff _ _ _ _).mpr hi⟩

private theorem mover_point (a b : Space) (ha : quadratic a = 1) (hb : quadratic b = 1)
    (x y : Space) (hx : quadratic x = -1) (hy : quadratic y = -1) (h : Moves a b x y) :
    mover a b ha hb • point x hx = point y hy := by
  rw [omega_smul_point]
  exact (point_eq_iff _ _ _ _).mpr h

private theorem mover_fix (a b : Space) (ha : quadratic a = 1) (hb : quadratic b = 1)
    (x : Space) (hx : quadratic x = -1) (hax : pairing a x = 0) (hbx : pairing b x = 0) :
    mover a b ha hb • point x hx = point x hx := by
  apply mover_point
  left
  simp only [reflect, hax, hbx, zero_smul, add_zero]

private theorem first_transport (x : Point) : ∃ g : omegaPlusSixThree, g • basePoint 0 = x := by
  obtain ⟨i, rfl⟩ := indexedPoint_surjective x
  have h := checked0 i
  exact ⟨mover _ _ h.1 h.2.1, mover_point _ _ h.1 h.2.1 _ _ _ _ h.2.2⟩

private theorem second_transport (x : Point) (hx : graph.Adj (basePoint 0) x) :
    ∃ g : omegaPlusSixThree, g • basePoint 0 = basePoint 0 ∧ g • basePoint 1 = x := by
  obtain ⟨i, rfl⟩ := indexedPoint_surjective x
  have h := checked1 i hx
  exact ⟨mover _ _ h.1 h.2.1,
    mover_fix _ _ h.1 h.2.1 _ _ h.2.2.1 h.2.2.2.1,
    mover_point _ _ h.1 h.2.1 _ _ _ _ h.2.2.2.2⟩

private theorem third_transport (x : Point)
    (hx : graph.Adj (basePoint 0) x) (hy : graph.Adj (basePoint 1) x) :
    ∃ g : omegaPlusSixThree, g • basePoint 0 = basePoint 0 ∧
      g • basePoint 1 = basePoint 1 ∧ g • basePoint 2 = x := by
  obtain ⟨i, rfl⟩ := indexedPoint_surjective x
  have h := checked2 i hx hy
  exact ⟨mover _ _ h.1 h.2.1,
    mover_fix _ _ h.1 h.2.1 _ _ h.2.2.1 h.2.2.2.1,
    mover_fix _ _ h.1 h.2.1 _ _ h.2.2.2.2.1 h.2.2.2.2.2.1,
    mover_point _ _ h.1 h.2.1 _ _ _ _ h.2.2.2.2.2.2⟩

private theorem transport (a b c : Point)
    (hab : graph.Adj a b) (hbc : graph.Adj b c) (hca : graph.Adj c a) :
    ∃ g : omegaPlusSixThree, g • basePoint 0 = a ∧
      g • basePoint 1 = b ∧ g • basePoint 2 = c := by
  obtain ⟨g, hg⟩ := first_transport a
  have hb : graph.Adj (basePoint 0) (g⁻¹ • b) := by
    simpa only [← hg, inv_smul_smul] using omega_preserves g⁻¹ hab
  obtain ⟨h, hh0, hh1⟩ := second_transport (g⁻¹ • b) hb
  have hc0 : graph.Adj (basePoint 0) (h⁻¹ • g⁻¹ • c) := by
    have ht := omega_preserves h⁻¹ (omega_preserves g⁻¹ hca.symm)
    have hga : g⁻¹ • a = basePoint 0 := by rw [← hg, inv_smul_smul]
    have hfix : h⁻¹ • basePoint 0 = basePoint 0 := by
      rw [inv_smul_eq_iff, hh0]
    simpa only [hga, hfix] using ht
  have hc1 : graph.Adj (basePoint 1) (h⁻¹ • g⁻¹ • c) := by
    simpa only [← hh1, inv_smul_smul] using omega_preserves h⁻¹ (omega_preserves g⁻¹ hbc)
  obtain ⟨k, hk0, hk1, hk2⟩ := third_transport (h⁻¹ • g⁻¹ • c) hc0 hc1
  refine ⟨g * h * k, ?_, ?_, ?_⟩
  · simp only [mul_smul, hk0, hh0, hg]
  · simp only [mul_smul, hk1, hh1, smul_inv_smul]
  · simp only [mul_smul, hk2, smul_inv_smul]

end OmegaSixThree.OrthogonalityGraph.TriangleCertificate

namespace OmegaSixThree.OrthogonalityGraph
open SixTernaryCoordinates
open TriangleCertificate

/-- The point `⟨e₅⟩` of the standard F.5 triangle, in zero-based coordinates. -/
@[expose] public def standardFirst : Point := point (e 5) quadratic_e5
/-- The point `⟨e₀-e₁⟩` of the standard F.5 triangle. -/
@[expose] public def standardSecond : Point :=
  point (e 0 - e 1) standardTriple_mem_normMinusOne.2.1
/-- The point `⟨e₀+e₁⟩` of the standard F.5 triangle. -/
@[expose] public def standardThird : Point :=
  point (e 0 + e 1) standardTriple_mem_normMinusOne.2.2

private theorem basePoint_zero : basePoint 0 = standardFirst := by
  apply (point_eq_iff _ _ _ _).mpr
  left
  decide +kernel
private theorem basePoint_one : basePoint 1 = standardSecond := by
  apply (point_eq_iff _ _ _ _).mpr
  left
  decide +kernel
private theorem basePoint_two : basePoint 2 = standardThird := by
  apply (point_eq_iff _ _ _ _).mpr
  left
  decide +kernel

/-- The three literal standard projective points form a triangle. -/
public theorem standard_adjacent : graph.Adj standardFirst standardSecond ∧
    graph.Adj standardSecond standardThird ∧ graph.Adj standardThird standardFirst := by
  change pairing (e 5) (e 0 - e 1) = 0 ∧
    pairing (e 0 - e 1) (e 0 + e 1) = 0 ∧ pairing (e 0 + e 1) (e 5) = 0
  decide +kernel

/-- Every ordered graph triangle is the image of the standard triangle under
an element of the literal derived orthogonal group. This proves F.5.8(1). -/
public theorem exists_triangle_transport (a b c : Point)
    (hab : graph.Adj a b) (hbc : graph.Adj b c) (hca : graph.Adj c a) :
    ∃ g : omegaPlusSixThree, g • standardFirst = a ∧
      g • standardSecond = b ∧ g • standardThird = c := by
  simpa only [basePoint_zero, basePoint_one, basePoint_two] using transport a b c hab hbc hca

end OmegaSixThree.OrthogonalityGraph
