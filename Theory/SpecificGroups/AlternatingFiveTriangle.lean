module

public import Theory.Alternating.Theorem523A6

/-!
# Embedding A₅ from a (2,3,5) pair

The classical icosahedral presentation gives an embedding of `A₅` in any group
containing a nonidentity `x` with `x² = y³ = (xy)⁵ = 1`.

We construct a homomorphism using Suzuki's alternating-group presentation
(2.15), as formalized in `Theory.Alternating.Theorem523A6`. Its generators are
sent to `yxyxy⁻¹`, `x`, and `xyxyxy⁻¹xy`. Explicit word equalities establish
all six defining relations. The second generator has nonidentity image, so
simplicity of `A₅` makes the homomorphism injective. Thus no sufficiency claim
is inferred merely from element orders.
-/

namespace alternatingGroup

open GLS3.Chapter5.SchurPresentation

set_option maxHeartbeats 800000

variable {G : Type*} [Group G]

private theorem triangle_suzuki_relations (x y : G) (hx : x ^ 2 = 1) (hy : y ^ 3 = 1)
    (hxy : (x * y) ^ 5 = 1) :
    let a := y * x * y * x * y⁻¹
    let c := x * y * x * y * x * y⁻¹ * x * y
    a ^ 3 = 1 ∧ c ^ 2 = 1 ∧ (a * x) ^ 3 = 1 ∧
      (x * c) ^ 3 = 1 ∧ (a * c) ^ 2 = 1 := by
  let z := y⁻¹
  -- Consequences of the three triangle relations, used in the reductions below.
  have r0 : x * x = 1 := by simpa [pow_two] using hx
  have r1 : y * y = z := by
    apply (eq_inv_iff_mul_eq_one).mpr
    simpa [pow_succ, mul_assoc] using hy
  have r2 : y * z = 1 := mul_inv_cancel y
  have r3 : z * y = 1 := inv_mul_cancel y
  have r5 : x * y * x * y * x * y * x * y * x * y = 1 := by
    simpa [pow_succ, mul_assoc] using hxy
  have r6 : y * x * y * x * y * x * y * x * y = x := by
    calc
      y * x * y * x * y * x * y * x * y = x * x * y * x * y * x * y * x * y * x * y := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (1) * t * (y * x * y * x * y * x * y * x * y)) r0.symm
      _ = x := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (x) * t * (1)) r5
  have r9 : y * x * y * x * y * x * y * x * z = x * y := by
    calc
      y * x * y * x * y * x * y * x * z = y * x * y * x * y * x * y * x * y * y := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (y * x * y * x * y * x * y * x) * t * (1)) r1.symm
      _ = x * y := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (1) * t * (y)) r6
  have r11 : y * x * y * x * y * x * y * x = x * z := by
    calc
      y * x * y * x * y * x * y * x = y * x * y * x * y * x * y * x * y * z := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (y * x * y * x * y * x * y * x) * t * (1)) r2.symm
      _ = x * z := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (1) * t * (z)) r6
  have r13 : z * x * y * x * y * x * y * x * z = y * x * y := by
    calc
      z * x * y * x * y * x * y * x * z = y * y * x * y * x * y * x * y * x * z := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (1) * t * (x * y * x * y * x * y * x * z)) r1.symm
      _ = y * x * y := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (y) * t * (1)) r9
  have r14 : x * y * x * y * x * y * x * z = z * x * y := by
    calc
      x * y * x * y * x * y * x * z = z * y * x * y * x * y * x * y * x * z := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (1) * t * (x * y * x * y * x * y * x * z)) r3.symm
      _ = z * x * y := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (z) * t * (1)) r9
  have r16 : y * x * y * x * y * x * y = x * z * x := by
    calc
      y * x * y * x * y * x * y = y * x * y * x * y * x * y * x * x := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (y * x * y * x * y * x * y) * t * (1)) r0.symm
      _ = x * z * x := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (1) * t * (x)) r11
  have r18 : y * x * y * x * y * x * z = x * z * x * y := by
    calc
      y * x * y * x * y * x * z = x * x * y * x * y * x * y * x * z := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (1) * t * (y * x * y * x * y * x * z)) r0.symm
      _ = x * z * x * y := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (x) * t * (1)) r14
  have r20 : y * x * y * x * y * x = x * z * x * z := by
    calc
      y * x * y * x * y * x = y * x * y * x * y * x * y * z := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (y * x * y * x * y * x) * t * (1)) r2.symm
      _ = x * z * x * z := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (1) * t * (z)) r16
  have r22 : z * x * y * x * y * x * z = y * x * z * x * y := by
    calc
      z * x * y * x * y * x * z = y * y * x * y * x * y * x * z := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (1) * t * (x * y * x * y * x * z)) r1.symm
      _ = y * x * z * x * y := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (y) * t * (1)) r18
  have r23 : x * y * x * y * x * z = z * x * z * x * y := by
    calc
      x * y * x * y * x * z = z * y * x * y * x * y * x * z := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (1) * t * (x * y * x * y * x * z)) r3.symm
      _ = z * x * z * x * y := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (z) * t * (1)) r18
  have r26 : z * x * z * x * z = x * y * x * y * x := by
    calc
      z * x * z * x * z = z * y * x * y * x * y * x := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (z) * t * (1)) r20.symm
      _ = x * y * x * y * x := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (1) * t * (x * y * x * y * x)) r3
  have r27 : x * z * x * z * x * y = y * x * y * x * z := by
    calc
      x * z * x * z * x * y = x * x * y * x * y * x * z := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (x) * t * (1)) r23.symm
      _ = y * x * y * x * z := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (1) * t * (y * x * y * x * z)) r0
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · calc
      _ = y * x * y * x * z * y * x * y * x * z * y * x * y * x * z := by
        simp only [z, pow_succ, pow_zero, one_mul, mul_assoc]
      _ = y * x * y * x * x * y * x * z * y * x * y * x * z := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (y * x * y * x) * t * (x * y * x * z * y * x * y * x * z)) r3
      _ = y * x * y * y * x * z * y * x * y * x * z := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (y * x * y) * t * (y * x * z * y * x * y * x * z)) r0
      _ = y * x * z * x * z * y * x * y * x * z := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (y * x) * t * (x * z * y * x * y * x * z)) r1
      _ = y * x * z * x * x * y * x * z := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (y * x * z * x) * t * (x * y * x * z)) r3
      _ = y * x * z * y * x * z := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (y * x * z) * t * (y * x * z)) r0
      _ = y * x * x * z := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (y * x) * t * (x * z)) r3
      _ = y * z := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (y) * t * (z)) r0
      _ = 1 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (1) * t * (1)) r2
  · calc
      _ = x * y * x * y * x * z * x * y * x * y * x * y * x * z * x * y := by
        simp only [z, pow_succ, pow_zero, one_mul, mul_assoc]
      _ = x * y * x * y * x * y * x * y * x * y := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (x * y * x * y * x) * t * (x * y)) r13
      _ = 1 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (1) * t * (1)) r5
  · calc
      _ = y * x * y * x * z * x * y * x * y * x * z * x * y * x * y * x * z * x := by
        simp only [z, pow_succ, pow_zero, one_mul, mul_assoc]
      _ = y * x * y * x * y * x * z * x * y * x * y * x * y * x * z * x := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (y * x * y * x) * t * (x * y * x * y * x * z * x)) r22
      _ = y * x * y * x * y * x * y * x * y * x := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (y * x * y * x * y * x) * t * (x)) r13
      _ = x * x := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (1) * t * (x)) r6
      _ = 1 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (1) * t * (1)) r0
  · calc
      _ = x * x * y * x * y * x * z * x * y * x * x * y * x * y * x * z * x * y * x * x * y * x * y * x * z * x * y := by
        simp only [z, pow_succ, pow_zero, one_mul, mul_assoc]
      _ = y * x * y * x * z * x * y * x * x * y * x * y * x * z * x * y * x * x * y * x * y * x * z * x * y := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (1) * t * (y * x * y * x * z * x * y * x * x * y * x * y * x * z * x * y * x * x * y * x * y * x * z * x * y)) r0
      _ = y * x * y * x * z * x * y * y * x * y * x * z * x * y * x * x * y * x * y * x * z * x * y := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (y * x * y * x * z * x * y) * t * (y * x * y * x * z * x * y * x * x * y * x * y * x * z * x * y)) r0
      _ = y * x * y * x * z * x * y * y * x * y * x * z * x * y * y * x * y * x * z * x * y := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (y * x * y * x * z * x * y * y * x * y * x * z * x * y) * t * (y * x * y * x * z * x * y)) r0
      _ = y * x * y * x * z * x * z * x * y * x * z * x * y * y * x * y * x * z * x * y := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (y * x * y * x * z * x) * t * (x * y * x * z * x * y * y * x * y * x * z * x * y)) r1
      _ = y * x * y * x * z * x * z * x * y * x * z * x * z * x * y * x * z * x * y := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (y * x * y * x * z * x * z * x * y * x * z * x) * t * (x * y * x * z * x * y)) r1
      _ = y * x * y * y * x * y * x * z * x * z * x * z * x * y * x * z * x * y := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (y * x * y) * t * (x * z * x * z * x * y * x * z * x * y)) r27
      _ = y * x * z * x * y * x * z * x * z * x * z * x * y * x * z * x * y := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (y * x) * t * (x * y * x * z * x * z * x * z * x * y * x * z * x * y)) r1
      _ = y * x * z * x * y * x * x * y * x * y * x * x * y * x * z * x * y := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (y * x * z * x * y * x) * t * (x * y * x * z * x * y)) r26
      _ = y * x * z * x * y * y * x * y * x * x * y * x * z * x * y := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (y * x * z * x * y) * t * (y * x * y * x * x * y * x * z * x * y)) r0
      _ = y * x * z * x * y * y * x * y * y * x * z * x * y := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (y * x * z * x * y * y * x * y) * t * (y * x * z * x * y)) r0
      _ = y * x * z * x * z * x * y * y * x * z * x * y := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (y * x * z * x) * t * (x * y * y * x * z * x * y)) r1
      _ = y * x * z * x * z * x * z * x * z * x * y := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (y * x * z * x * z * x) * t * (x * z * x * y)) r1
      _ = y * x * x * y * x * y * x * x * z * x * y := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (y * x) * t * (x * z * x * y)) r26
      _ = y * y * x * y * x * x * z * x * y := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (y) * t * (y * x * y * x * x * z * x * y)) r0
      _ = y * y * x * y * z * x * y := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (y * y * x * y) * t * (z * x * y)) r0
      _ = z * x * y * z * x * y := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (1) * t * (x * y * z * x * y)) r1
      _ = z * x * x * y := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (z * x) * t * (x * y)) r2
      _ = z * y := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (z) * t * (y)) r0
      _ = 1 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (1) * t * (1)) r3
  · calc
      _ = y * x * y * x * z * x * y * x * y * x * z * x * y * y * x * y * x * z * x * y * x * y * x * z * x * y := by
        simp only [z, pow_succ, pow_zero, one_mul, mul_assoc]
      _ = y * x * y * x * z * x * y * x * y * x * z * x * z * x * y * x * z * x * y * x * y * x * z * x * y := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (y * x * y * x * z * x * y * x * y * x * z * x) * t * (x * y * x * z * x * y * x * y * x * z * x * y)) r1
      _ = y * x * y * x * y * x * z * x * y * x * z * x * y * x * z * x * y * x * y * x * z * x * y := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (y * x * y * x) * t * (x * z * x * y * x * z * x * y * x * y * x * z * x * y)) r22
      _ = x * z * x * y * x * y * x * z * x * y * x * z * x * y * x * y * x * z * x * y := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (1) * t * (x * y * x * z * x * y * x * z * x * y * x * y * x * z * x * y)) r18
      _ = x * y * x * z * x * y * x * y * x * z * x * y * x * y * x * z * x * y := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (x) * t * (x * y * x * z * x * y * x * y * x * z * x * y)) r22
      _ = x * y * x * y * x * z * x * y * x * y * x * y * x * z * x * y := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (x * y * x) * t * (x * y * x * y * x * z * x * y)) r22
      _ = x * y * x * y * x * y * x * y * x * y := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (x * y * x * y * x) * t * (x * y)) r13
      _ = 1 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun t : G => (1) * t * (1)) r5

private def triangleGenerator (x y : G) : Fin 3 → G :=
  ![y * x * y * x * y⁻¹, x, x * y * x * y * x * y⁻¹ * x * y]

private theorem triangleGenerator_relator (x y : G)
    (hx : x ^ 2 = 1) (hy : y ^ 3 = 1) (hxy : (x * y) ^ 5 = 1)
    (r : SuzukiRelator 0) :
    FreeGroup.lift (triangleGenerator x y) r.word = 1 := by
  obtain ⟨ha, hc, hax, hxc, hac⟩ := triangle_suzuki_relations x y hx hy hxy
  cases r with
  | rootCube =>
      simpa [SuzukiRelator.word, suzukiFreeGenerator, triangleGenerator] using ha
  | tailSquare i hi =>
      fin_cases i
      · exact (hi rfl).elim
      · simpa [SuzukiRelator.word, suzukiFreeGenerator, triangleGenerator] using hx
      · simpa [SuzukiRelator.word, suzukiFreeGenerator, triangleGenerator] using hc
  | rootAdjacentCube =>
      simpa [SuzukiRelator.word, suzukiFreeGenerator, triangleGenerator] using hax
  | tailAdjacentCube i hi =>
      fin_cases i
      · exact (hi rfl).elim
      · simpa [SuzukiRelator.word, suzukiFreeGenerator, triangleGenerator] using hxc
  | rootFarSquare j hj =>
      fin_cases j
      · simp at hj
      · simp at hj
      · simpa [SuzukiRelator.word, suzukiFreeGenerator, triangleGenerator] using hac
  | tailFarCommutator i j hi hj hfar =>
      have hi' : i.val ≠ 0 := fun h => hi (Fin.ext h)
      have hj' : j.val ≠ 0 := fun h => hj (Fin.ext h)
      omega

/-- The icosahedral `(2,3,5)` relations with a nontrivial involution give an
embedding of the alternating group on five letters. -/
public theorem exists_injective_hom_of_triangle (x y : G)
    (hne : x ≠ 1) (hx : x ^ 2 = 1) (hy : y ^ 3 = 1)
    (hxy : (x * y) ^ 5 = 1) :
    ∃ f : alternatingGroup (Fin 5) →* G, Function.Injective f := by
  classical
  let h : SuzukiPresentedGroup 0 →* G := PresentedGroup.toGroup (by
    rintro _ ⟨r, rfl⟩
    exact triangleGenerator_relator x y hx hy hxy r)
  let e : SuzukiPresentedGroup 0 ≃* alternatingGroup (Fin 5) :=
    MulEquiv.ofBijective (suzukiPresentedProjection 0)
      ⟨suzukiPresentedProjection_injective 0, suzukiPresentedProjection_surjective 0⟩
  let f : alternatingGroup (Fin 5) →* G := h.comp e.symm.toMonoidHom
  have hfx : f (e (PresentedGroup.of (1 : Fin 3))) = x := by
    simp [f, h, triangleGenerator]
  refine ⟨f, ?_⟩
  rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with hbot | htop
  · exact f.ker_eq_bot_iff.mp hbot
  · exfalso
    apply hne
    rw [← hfx]
    exact MonoidHom.mem_ker.mp (by rw [htop]; trivial)

end alternatingGroup
