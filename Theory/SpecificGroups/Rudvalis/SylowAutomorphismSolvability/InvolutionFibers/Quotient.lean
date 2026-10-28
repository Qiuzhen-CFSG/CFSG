module

public import Theory.SpecificGroups.Rudvalis.SylowAutomorphismSolvability.FrattiniCoordinates
public import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.Ring

/-!
# A small cocycle quotient detecting Rudvalis involution fibers

Six binary coordinates form a group through the bilinear central cocycle
(bA,cA,cB). Its square map (ab,ac,bc) distinguishes the three coordinate
axes. Checking the fourteen square and ninety-one conjugation rows gives
a homomorphism from the original Rudvalis Sylow candidate, using the graph
collection theorem and its proved order. Only that theorem reverses the
generators; the exported tags retain their original order.

The projection (c,b,a+c) agrees with the established Frattini coordinates.
Thus only three nonidentity coordinate fibers can contain square-one
elements; the first three original generators supply all three witnesses.

Source: the original RuG1-max4W1 words and left-action convention in
Model.SylowOvergroups.RadicalCoverage.Sylow.Candidate, the square rows in
Sylow/source/witnesses.json, and the checked LocalOrder.Collection rows.
The intended source application is Aschbacher--Smith A.3.9, pp.45--46.
-/

namespace Rudvalis.SylowAutomorphismSolvability.InvolutionFibers
open Subgroup FrattiniCoordinates
open Rudvalis.SylowOvergroups.RadicalCoverage.SylowCertificate
open Rudvalis.SylowOvergroups.RadicalCoverage.SylowCertificate.LocalOrder

@[ext] public structure SmallGroup where
  a : ZMod 2
  b : ZMod 2
  c : ZMod 2
  d : ZMod 2
  e : ZMod 2
  f : ZMod 2
  deriving DecidableEq

public instance : Finite SmallGroup :=
  Finite.of_injective (fun x : SmallGroup => ![x.a, x.b, x.c, x.d, x.e, x.f])
    (by
      intro x y h
      exact SmallGroup.ext (congrFun h 0) (congrFun h 1) (congrFun h 2)
        (congrFun h 3) (congrFun h 4) (congrFun h 5))

public instance smallMul : Mul SmallGroup := ⟨fun x y =>
  ⟨x.a + y.a, x.b + y.b, x.c + y.c,
    x.d + y.d + x.b * y.a, x.e + y.e + x.c * y.a, x.f + y.f + x.c * y.b⟩⟩
public instance smallOne : One SmallGroup := ⟨⟨0, 0, 0, 0, 0, 0⟩⟩
public instance smallInv : Inv SmallGroup := ⟨fun x =>
  ⟨-x.a, -x.b, -x.c, -x.d + x.b * x.a,
    -x.e + x.c * x.a, -x.f + x.c * x.b⟩⟩
public instance : Group SmallGroup where
  mul_assoc x y z := by
    apply SmallGroup.ext
    · exact add_assoc _ _ _
    · exact add_assoc _ _ _
    · exact add_assoc _ _ _
    · change (x.d + y.d + x.b * y.a) + z.d + (x.b + y.b) * z.a =
        x.d + (y.d + z.d + y.b * z.a) + x.b * (y.a + z.a)
      ring
    · change (x.e + y.e + x.c * y.a) + z.e + (x.c + y.c) * z.a =
        x.e + (y.e + z.e + y.c * z.a) + x.c * (y.a + z.a)
      ring
    · change (x.f + y.f + x.c * y.b) + z.f + (x.c + y.c) * z.b =
        x.f + (y.f + z.f + y.c * z.b) + x.c * (y.b + z.b)
      ring
  one_mul x := by
    apply SmallGroup.ext
    · change 0 + x.a = x.a
      ring
    · change 0 + x.b = x.b
      ring
    · change 0 + x.c = x.c
      ring
    · change 0 + x.d + 0 * x.a = x.d
      ring
    · change 0 + x.e + 0 * x.a = x.e
      ring
    · change 0 + x.f + 0 * x.b = x.f
      ring
  mul_one x := by
    apply SmallGroup.ext
    · change x.a + 0 = x.a
      ring
    · change x.b + 0 = x.b
      ring
    · change x.c + 0 = x.c
      ring
    · change x.d + 0 + x.b * 0 = x.d
      ring
    · change x.e + 0 + x.c * 0 = x.e
      ring
    · change x.f + 0 + x.c * 0 = x.f
      ring
  inv_mul_cancel x := by
    apply SmallGroup.ext
    · change -x.a + x.a = 0
      ring
    · change -x.b + x.b = 0
      ring
    · change -x.c + x.c = 0
      ring
    · change (-x.d + x.b * x.a) + x.d + (-x.b) * x.a = 0
      ring
    · change (-x.e + x.c * x.a) + x.e + (-x.c) * x.a = 0
      ring
    · change (-x.f + x.c * x.b) + x.f + (-x.c) * x.b = 0
      ring

/-- The diagonal of the bilinear cocycle is the square map. -/
public theorem small_square (x : SmallGroup) :
    x ^ 2 = ⟨0, 0, 0, x.a * x.b, x.a * x.c, x.b * x.c⟩ := by
  rw [pow_two]
  apply SmallGroup.ext
  · exact CharTwo.add_self_eq_zero x.a
  · exact CharTwo.add_self_eq_zero x.b
  · exact CharTwo.add_self_eq_zero x.c
  · change x.d + x.d + x.b * x.a = x.a * x.b
    rw [CharTwo.add_self_eq_zero, zero_add, mul_comm]
  · change x.e + x.e + x.c * x.a = x.a * x.c
    rw [CharTwo.add_self_eq_zero, zero_add, mul_comm]
  · change x.f + x.f + x.c * x.b = x.b * x.c
    rw [CharTwo.add_self_eq_zero, zero_add, mul_comm]

@[expose] public def smallOfMask (n : ℕ) : SmallGroup :=
  ⟨(n % 2 : ℕ), (n / 2 % 2 : ℕ), (n / 4 % 2 : ℕ),
    (n / 8 % 2 : ℕ), (n / 16 % 2 : ℕ), (n / 32 % 2 : ℕ)⟩

@[expose] public def smallTag (i : Fin 14) : SmallGroup :=
  smallOfMask (![1,2,4,20,52,36,0,8,0,8,8,0,0,0] i)

private def sqWord (i : Fin 14) : List (Fin 14) :=
  if i = 7 then [11] else if i = 9 ∨ i = 10 then [11,12,13] else []

private theorem square_check : ∀ (i : Fin 14) (k : Fin 5),
    (generatorMap i)^[2] (k.castLE (by decide)) =
      evalWord generatorMap (sqWord i) (k.castLE (by decide)) := by
  decide +kernel

private theorem square_actual (i : Fin 14) :
    candidateGenerator i ^ 2 = ((sqWord i).map candidateGenerator).prod := by
  apply Rudvalis.eq_of_smul_first_five
  intro k
  rw [generator_pow_smul, prod_smul candidateGenerator generatorMap generator_smul]
  exact square_check i k

private theorem square_tag : ∀ i : Fin 14,
    smallTag i ^ 2 = ((sqWord i).map smallTag).prod := by decide +kernel
private theorem conjugate_tag : ∀ i j : Fin 14, i < j →
    smallTag i * smallTag j * (smallTag i)⁻¹ =
      ((conjugateWord i j).map smallTag).prod := by decide +kernel
private theorem square_support : ∀ i j : Fin 14, j ∈ sqWord i → i.val < j.val := by
  decide +kernel

private theorem pair_prod (l : List (Fin 14)) :
    (l.map (fun j => (pcElement j, smallTag j))).prod =
      ((l.map pcElement).prod, (l.map smallTag).prod) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
      simp only [List.map_cons, List.prod_cons, ih]
      rfl

private theorem pair_square (i : Fin 14) :
    (pcElement i.rev, smallTag i.rev) ^ 2 ∈
      generatorPrefix (fun j => (pcElement j.rev, smallTag j.rev)) i.val := by
  have he : (pcElement i.rev, smallTag i.rev) ^ 2 =
      ((sqWord i.rev).map (fun j => (pcElement j, smallTag j))).prod := by
    rw [pair_prod]
    apply Prod.ext
    · apply Subtype.ext
      simpa [pcElement, Subgroup.val_list_prod, List.map_map, Function.comp_def] using square_actual i.rev
    · exact square_tag i.rev
  rw [he]
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
  have h := square_support i.rev j hj
  have hmem := (generatorPrefix_le (fun j => (pcElement j.rev, smallTag j.rev)) i.val _).mp le_rfl j.rev (by simp only [Fin.val_rev] at *; omega)
  simpa only [Fin.rev_rev] using hmem

private theorem pair_normalizes (i : Fin 14) :
    (pcElement i.rev, smallTag i.rev) ∈ normalizer
      (generatorPrefix (fun j => (pcElement j.rev, smallTag j.rev)) i.val :
        Set (Representative × SmallGroup)) := by
  unfold generatorPrefix
  apply mem_normalizer_closure_of_conjugates
  rintro _ ⟨j, hj, rfl⟩
  change j.val < i.val at hj
  have hij : i.rev < j.rev := by
    change i.rev.val < j.rev.val
    simp only [Fin.val_rev]
    omega
  have he : (pcElement i.rev, smallTag i.rev) *
      (pcElement j.rev, smallTag j.rev) * (pcElement i.rev, smallTag i.rev)⁻¹ =
      ((conjugateWord i.rev j.rev).map (fun k => (pcElement k, smallTag k))).prod := by
    rw [pair_prod]
    apply Prod.ext
    · apply Subtype.ext
      simpa [pcElement, Subgroup.val_list_prod, List.map_map, Function.comp_def] using
        generator_conjugate i.rev j.rev hij
    · exact conjugate_tag i.rev j.rev hij
  rw [he]
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
  have ht := conjugateWord_tail i.rev j.rev k hk
  exact subset_closure ⟨k.rev, by
    change k.rev.val < i.val
    simp only [Fin.val_rev] at *
    omega, by simp⟩

public theorem exists_small_hom :
    ∃ f : Representative →* SmallGroup, ∀ i, f (pcElement i) = smallTag i := by
  have hrev : closure (Set.range (fun i : Fin 14 => pcElement i.rev)) = ⊤ := by
    have he : Set.range (fun i : Fin 14 => pcElement i.rev) = Set.range pcElement := by
      ext x
      exact ⟨fun ⟨i, h⟩ => ⟨i.rev, h⟩, fun ⟨i, h⟩ => ⟨i.rev, by simpa using h⟩⟩
    rw [he, generators_top]
  obtain ⟨f, hf⟩ := Theory.GroupTheory.BinaryGraph.exists_hom_of_graph_collection
    (fun i : Fin 14 => pcElement i.rev) (fun i : Fin 14 => smallTag i.rev)
    hrev (by rw [candidate_card]; decide) pair_square pair_normalizes
  exact ⟨f, fun i => by simpa only [Fin.rev_rev] using hf i.rev⟩



@[expose] public def smallProjection : SmallGroup →* Coordinate where
  toFun x := Multiplicative.ofAdd ![x.c, x.b, x.a + x.c]
  map_one' := by
    change (![0, 0, 0 + 0] : Fin 3 → ZMod 2) = 0
    funext i
    fin_cases i <;> rfl
  map_mul' x y := by
    change (![(x * y).c, (x * y).b, (x * y).a + (x * y).c] : Fin 3 → ZMod 2) =
      ![x.c, x.b, x.a + x.c] + ![y.c, y.b, y.a + y.c]
    funext i
    fin_cases i
    · rfl
    · rfl
    · change (x.a + y.a) + (x.c + y.c) = (x.a + x.c) + (y.a + y.c)
      ring

private theorem projection_tag : ∀ i, smallProjection (smallTag i) = coordinateGenerator i := by
  decide +kernel

/-- The new quotient projection is the existing coordinate map on every
original generator, hence on the actual candidate. -/
public theorem smallProjection_comp (h : Representative →* SmallGroup)
    (hh : ∀ i, h (pcElement i) = smallTag i)
    (f : Representative →* Coordinate) (hf : ∀ i, f (pcElement i) = coordinateGenerator i) :
    smallProjection.comp h = f := by
  apply MonoidHom.eq_of_eqOn_dense generators_top
  rintro _ ⟨i, rfl⟩
  change smallProjection (h (pcElement i)) = f (pcElement i)
  rw [hh, hf, projection_tag]

private theorem small_square_projection (x : SmallGroup) (hx : x ^ 2 = 1) :
    smallProjection x = 1 ∨ smallProjection x = coordinateGenerator 0 ∨
      smallProjection x = coordinateGenerator 1 ∨ smallProjection x = coordinateGenerator 2 := by
  rcases x with ⟨a,b,c,d,e,f⟩
  revert hx a b c d e f
  decide +kernel

/-- Actual square-one witnesses, checked through the faithful five-point action. -/
public theorem first_three_square : ∀ i : Fin 3,
    pcElement (i.castLE (by decide)) ^ 2 = 1 := by
  intro i
  apply Subtype.ext
  fin_cases i
  · simpa [pcElement, sqWord] using square_actual (0 : Fin 14)
  · simpa [pcElement, sqWord] using square_actual (1 : Fin 14)
  · simpa [pcElement, sqWord] using square_actual (2 : Fin 14)

/-- Precisely the three independent marked coordinates have square-one lifts.
This is a property of the original candidate and its actual coordinate fibers. -/
public theorem involution_fiber_iff (f : Representative →* Coordinate)
    (hf : ∀ i, f (pcElement i) = coordinateGenerator i)
    (v : Coordinate) (hv : v ≠ 1) :
    (∃ x : Representative, f x = v ∧ x ^ 2 = 1) ↔
      v = coordinateGenerator 0 ∨ v = coordinateGenerator 1 ∨ v = coordinateGenerator 2 := by
  constructor
  · rintro ⟨x, rfl, hx⟩
    obtain ⟨h, hh⟩ := exists_small_hom
    have he : smallProjection (h x) = f x := DFunLike.congr_fun (smallProjection_comp h hh f hf) x
    have hx' : h x ^ 2 = 1 := by rw [← map_pow, hx, map_one]
    have hs := small_square_projection (h x) hx'
    rw [he] at hs
    exact hs.resolve_left hv
  · intro h
    rcases h with rfl | rfl | rfl
    · exact ⟨pcElement 0, hf 0, first_three_square 0⟩
    · exact ⟨pcElement 1, hf 1, first_three_square 1⟩
    · exact ⟨pcElement 2, hf 2, first_three_square 2⟩

end Rudvalis.SylowAutomorphismSolvability.InvolutionFibers
