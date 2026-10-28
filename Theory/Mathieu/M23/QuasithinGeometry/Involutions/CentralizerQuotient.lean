module

public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.CentralizerKernel
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import Mathlib.Logic.Equiv.Option

/-!
# The M23 involution centralizer quotient is PSL₃(2)

The seven fixed points of the chosen involution carry the Fano plane certified
in `Representative.Fano`. We identify those points with the nonzero vectors of
F₂³, matching each three-point line with a triple whose vector sum is zero.
Every element of the actual centralizer action image therefore extends, by
fixing zero, to an invertible linear map. This gives an injective homomorphism
from the action image into GL₃(2). Both groups have order 168, so it is an
isomorphism. The canonical comparisons GL₃(2) ≃ SL₃(2) ≃ PSL₃(2) give the
required quotient identification for the extension in `CentralizerKernel`.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 16.1.5(6),
printed p.1171; the fixed-point geometry also occurs in 5.2.21, printed p.657.
-/

open scoped Pointwise
namespace Sporadic.Mathieu.M23Geometry.InvolutionCentralizer

private abbrev V := Fin 3 → ZMod 2

/-- Binary coordinates for the fixed points labelled 1, 2, 3, 4, 5, 11, 17. -/
private def coord : Fin 7 → V :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, 0, 1], ![1, 1, 0], ![1, 1, 1], ![0, 1, 1]]

private def vectorOf : Option (Fin 7) → V
  | none => 0
  | some i => coord i

private noncomputable def vectorEquiv : Option (Fin 7) ≃ V :=
  Equiv.ofBijective vectorOf (by decide +kernel)

private theorem coord_injective : Function.Injective coord := by decide +kernel

private theorem vector_double : ∀ v : V, v + v = 0 := by decide +kernel

private theorem coord_add_exists : ∀ i j : Fin 7, i ≠ j →
    ∃ k : Fin 7, coord k = coord i + coord j := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
/-- Three distinct fixed points form a line exactly when their coordinates sum to zero. -/
private theorem coord_add_iff : ∀ i j k : Fin 7, i ≠ j →
    (coord k = coord i + coord j ↔
      {label i, label j, label k} ∈ involutionLines) := by decide +kernel

/-- The inherited action preserves the explicit three-point lines. -/
private theorem action_preserves_lines (g : action.range) (i j k : Fin 7)
    (h : {label i, label j, label k} ∈ involutionLines) :
    {label (g.val i), label (g.val j), label (g.val k)} ∈ involutionLines := by
  obtain ⟨c, hc⟩ := g.property
  rw [← hc]
  have hm : (c.val • ({label i, label j, label k} : Finset (Fin 23))) ∈
      c.val • involutionLines := Finset.smul_mem_smul_finset h
  rw [centralizer_preserves_involutionLines c.val c.property] at hm
  have happ (a : Fin 7) : label (action c a) = c.val • label a :=
    heptadAction_apply (toHeptad c) a
  simpa only [Finset.smul_finset_insert, Finset.smul_finset_singleton, ← happ] using hm

/-- Extend the permutation of nonzero vectors by fixing zero. -/
private noncomputable def vectorPerm (g : Equiv.Perm (Fin 7)) : Equiv.Perm V :=
  vectorEquiv.permCongr (Equiv.optionCongr g)

private theorem vectorPerm_zero (g : Equiv.Perm (Fin 7)) : vectorPerm g 0 = 0 := by
  change vectorPerm g (vectorEquiv none) = vectorEquiv none
  simp [vectorPerm, Equiv.permCongr_apply]

private theorem vectorPerm_coord (g : Equiv.Perm (Fin 7)) (i : Fin 7) :
    vectorPerm g (coord i) = coord (g i) := by
  change vectorPerm g (vectorEquiv (some i)) = vectorEquiv (some (g i))
  simp [vectorPerm, Equiv.permCongr_apply]

/-- Line preservation is precisely what is needed for additivity away from zero. -/
private theorem vectorPerm_add (g : action.range) (x y : V) :
    vectorPerm g.val (x + y) = vectorPerm g.val x + vectorPerm g.val y := by
  obtain ⟨x, rfl⟩ := vectorEquiv.surjective x
  obtain ⟨y, rfl⟩ := vectorEquiv.surjective y
  cases x with
  | none =>
    change vectorPerm g.val (0 + _) = vectorPerm g.val 0 + _
    rw [zero_add, vectorPerm_zero, zero_add]
  | some i =>
    cases y with
    | none =>
      change vectorPerm g.val (_ + 0) = _ + vectorPerm g.val 0
      rw [add_zero, vectorPerm_zero, add_zero]
    | some j =>
      change vectorPerm g.val (coord i + coord j) =
        vectorPerm g.val (coord i) + vectorPerm g.val (coord j)
      by_cases hij : i = j
      · subst j
        rw [vector_double, vectorPerm_zero, vector_double]
      · obtain ⟨k, hk⟩ := coord_add_exists i j hij
        rw [← hk, vectorPerm_coord, vectorPerm_coord, vectorPerm_coord]
        exact (coord_add_iff _ _ _ (fun h => hij (g.val.injective h))).mpr
          (action_preserves_lines g i j k ((coord_add_iff i j k hij).mp hk))

/-- The faithful linear action obtained from the actual seven-point action image. -/
private noncomputable def linearAction : action.range →* (V ≃ₗ[ZMod 2] V) where
  toFun g :=
    { vectorPerm g.val with
      map_add' := vectorPerm_add g
      map_smul' := by
        intro c v
        have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide +kernel
        rcases hc c with rfl | rfl
        · simp only [zero_smul, RingHom.id_apply]
          exact vectorPerm_zero g.val
        · simp only [one_smul, RingHom.id_apply] }
  map_one' := by
    apply LinearEquiv.ext
    intro x
    obtain ⟨x, rfl⟩ := vectorEquiv.surjective x
    cases x with
    | none => exact vectorPerm_zero 1
    | some i => exact vectorPerm_coord 1 i
  map_mul' g h := by
    apply LinearEquiv.ext
    intro x
    obtain ⟨x, rfl⟩ := vectorEquiv.surjective x
    cases x with
    | none =>
      change vectorPerm (g.val * h.val) 0 = vectorPerm g.val (vectorPerm h.val 0)
      simp only [vectorPerm_zero]
    | some i =>
      change vectorPerm (g.val * h.val) (coord i) =
        vectorPerm g.val (vectorPerm h.val (coord i))
      simp only [vectorPerm_coord, Equiv.Perm.mul_apply]

private theorem linearAction_injective : Function.Injective linearAction := by
  intro g h heq
  apply Subtype.ext
  apply Equiv.ext
  intro i
  apply coord_injective
  have hh := congrArg (fun e : V ≃ₗ[ZMod 2] V => e (coord i)) heq
  exact (vectorPerm_coord g.val i).symm.trans (hh.trans (vectorPerm_coord h.val i))

private noncomputable def linearEquivPSL : (V ≃ₗ[ZMod 2] V) ≃* Matrix.PSL3Two.PSL :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).symm.trans
    (Matrix.GeneralLinearGroup.toLin.symm.trans
      (Matrix.PSL3Two.equivGL.symm.trans Matrix.PSL3Two.equiv))

/-- The actual seven-point image of the involution centralizer is PSL₃(2). -/
public noncomputable def actionEquivPSL :
    action.range ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) :=
  MulEquiv.ofBijective (linearEquivPSL.toMonoidHom.comp linearAction)
    ((linearEquivPSL.injective.comp linearAction_injective).bijective_of_nat_card_le
      (by rw [Matrix.PSL3Two.card_PSL, action_range_card]))

end Sporadic.Mathieu.M23Geometry.InvolutionCentralizer
