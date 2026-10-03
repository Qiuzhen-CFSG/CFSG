module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenTwoAutCoordinatesBFour
public import Theory.SpecificGroups.ReeTwo.EvenCoordinates
public import Theory.Frattini.BinarySquares
/-!
# Carrier equations and Frattini kernels for the rank-four even candidates

The internal carriers are parametrized by binary coordinates. Polynomial
multiplication verifies that right multiplication by each original generator
preserves its carrier and adds the four quotient coordinates. Induction on
positive generator words extends these identities to the generated subgroup.

Products of squares give four kernel generators in rows 0–4 and three in
rows 5–6. The carrier equations and vanishing quotient coordinates give a
normal form in those generators. Surjectivity then proves carrier equality,
and the square-closure description of the Frattini subgroup proves the kernel
identity. Every finite equation is checked by Lean's kernel.

Source: Shinoda (1975), (2.3), pp. 81–82, through the verified multiplication
in `Core`, `Sylow`, and `EvenCoordinates`. The square words are extracted from
the root-word enumerations for original indices 18,19,20,21,22,26,37; the
coordinate and generator conventions are those of `SmallEvenTwoAutCoordinatesBFour`.
-/

namespace ReeTwo.SylowModel.SmallEvenAutB
open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration
set_option maxRecDepth 32768
private def parameter (i : Fin 7) (v : Fin 8 → ZMod 2) : SylowModel :=
  (![evenElement 0 ⟨v 0,v 1,v 2,0,v 2,v 3,v 4,v 5,v 6,v 7⟩,
    evenElement 0 ⟨v 0,v 1,0,v 2,0,v 3,v 4,v 5,v 6,v 7⟩,
    evenElement 0 ⟨v 0,v 1,v 1,v 2,v 1,v 3,v 4,v 5,v 6,v 7⟩,
    evenElement 0 ⟨v 0,v 1,v 0,v 2,v 0,v 3,v 4,v 5,v 6,v 7⟩,
    evenElement 0 ⟨v 0,v 1,v 2,v 1,v 1,v 3,v 4,v 5,v 6,v 7⟩,
    evenElement (v 1 + v 2) ⟨v 0,0,v 1,v 2,v 1,v 3,v 0+v 1+v 2+v 3,v 4,v 5,v 6⟩,
    evenElement (v 0) ⟨0,v 0,0,v 1,v 2,v 2,v 3,v 4,v 5,v 6⟩]) i

set_option maxHeartbeats 800000 in
private theorem exists_parameter (i : Fin 7) (x : SylowModel)
    (hx : rankFourCarrier i x) : ∃ v, parameter i v = x := by
  rcases x with ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩,t⟩
  fin_cases i
  all_goals dsimp only [rankFourCarrier] at hx
  all_goals rcases hx with ⟨ht, hx⟩
  all_goals change t = _ at ht
  all_goals subst t
  · refine ⟨![b0,b1,b2,b5,b6,b7,b8,b9], ?_⟩
    apply SemidirectProduct.ext
    · apply Core.ext <;> simp_all [parameter, evenElement]
    · rfl
  · refine ⟨![b0,b1,b3,b5,b6,b7,b8,b9], ?_⟩
    apply SemidirectProduct.ext
    · apply Core.ext <;> simp_all [parameter, evenElement]
    · rfl
  · refine ⟨![b0,b1,b3,b5,b6,b7,b8,b9], ?_⟩
    apply SemidirectProduct.ext
    · apply Core.ext <;> simp_all [parameter, evenElement]
    · rfl
  · refine ⟨![b0,b1,b3,b5,b6,b7,b8,b9], ?_⟩
    apply SemidirectProduct.ext
    · apply Core.ext <;> simp_all [parameter, evenElement]
    · rfl
  · refine ⟨![b0,b1,b2,b5,b6,b7,b8,b9], ?_⟩
    apply SemidirectProduct.ext
    · apply Core.ext <;> simp_all [parameter, evenElement]
    · rfl
  · refine ⟨![b0,b2,b3,b5,b7,b8,b9,0], ?_⟩
    apply SemidirectProduct.ext
    · apply Core.ext <;> simp_all [parameter, evenElement]
    · rfl
  · refine ⟨![b1,b3,b4,b6,b7,b8,b9,0], ?_⟩
    apply SemidirectProduct.ext
    · apply Core.ext <;> simp_all [parameter, evenElement]
    · rfl

private def generatorCore : Fin 7 → Fin 8 → Core :=
  ![![⟨1,0,0,0,0,0,0,0,0,0⟩, ⟨1,0,1,0,1,1,1,1,1,0⟩, ⟨0,1,1,0,1,1,1,1,1,1⟩, ⟨0,0,0,0,0,1,1,1,0,0⟩, ⟨0,0,0,0,0,0,1,1,1,1⟩, ⟨0,0,0,0,0,0,0,1,0,1⟩, ⟨0,0,0,0,0,0,0,0,1,1⟩, ⟨0,0,0,0,0,0,0,0,0,1⟩],
    ![⟨1,0,0,0,0,0,0,0,0,0⟩, ⟨1,0,0,1,0,1,1,0,0,1⟩, ⟨0,1,0,1,0,1,1,1,0,1⟩, ⟨0,0,0,0,0,1,1,1,0,0⟩, ⟨0,0,0,0,0,0,1,1,1,1⟩, ⟨0,0,0,0,0,0,0,1,0,1⟩, ⟨0,0,0,0,0,0,0,0,1,1⟩, ⟨0,0,0,0,0,0,0,0,0,1⟩],
    ![⟨1,0,0,0,0,0,0,0,0,0⟩, ⟨1,0,0,1,0,1,1,0,0,1⟩, ⟨0,1,1,0,1,1,1,1,1,1⟩, ⟨0,0,0,0,0,1,1,1,0,0⟩, ⟨0,0,0,0,0,0,1,1,1,1⟩, ⟨0,0,0,0,0,0,0,1,0,1⟩, ⟨0,0,0,0,0,0,0,0,1,1⟩, ⟨0,0,0,0,0,0,0,0,0,1⟩],
    ![⟨1,0,1,1,1,0,0,1,0,0⟩, ⟨1,0,1,0,1,1,1,1,1,0⟩, ⟨0,1,0,1,0,1,1,1,0,1⟩, ⟨0,0,0,0,0,1,1,1,0,0⟩, ⟨0,0,0,0,0,0,1,1,1,1⟩, ⟨0,0,0,0,0,0,0,1,0,1⟩, ⟨0,0,0,0,0,0,0,0,1,1⟩, ⟨0,0,0,0,0,0,0,0,0,1⟩],
    ![⟨1,0,0,0,0,0,0,0,0,0⟩, ⟨1,0,1,0,0,1,1,0,0,1⟩, ⟨0,1,0,1,1,1,1,0,1,0⟩, ⟨0,0,0,0,0,1,1,1,0,0⟩, ⟨0,0,0,0,0,0,1,1,1,1⟩, ⟨0,0,0,0,0,0,0,1,0,1⟩, ⟨0,0,0,0,0,0,0,0,1,1⟩, ⟨0,0,0,0,0,0,0,0,0,1⟩],
    ![⟨1,0,0,0,0,0,1,1,1,1⟩, ⟨1,0,1,0,1,1,1,1,1,0⟩, ⟨0,0,1,1,1,1,1,1,0,1⟩, ⟨0,0,1,1,1,0,0,0,0,1⟩, ⟨0,0,0,0,0,0,0,0,1,1⟩, ⟨0,0,0,0,0,0,0,1,0,1⟩, ⟨0,0,0,0,0,0,0,0,0,1⟩, ⟨0,0,0,0,0,0,0,0,0,1⟩],
    ![⟨0,0,0,1,0,0,0,0,0,0⟩, ⟨0,1,0,1,1,1,1,0,1,1⟩, ⟨0,0,0,0,1,1,0,0,1,1⟩, ⟨0,0,0,0,0,0,1,0,1,0⟩, ⟨0,0,0,0,0,0,0,1,0,0⟩, ⟨0,0,0,0,0,0,0,0,1,1⟩, ⟨0,0,0,0,0,0,0,0,0,1⟩, ⟨0,0,0,0,0,0,0,0,0,1⟩]]

private def generatorBit (i : Fin 7) (j : Fin 8) : ZMod 2 :=
  if (i = 5 ∨ i = 6) ∧ j = 1 then 1 else 0

set_option maxHeartbeats 8000000 in
private theorem generator_eq : ∀ i j, rankFourGenerators i j =
    evenElement (generatorBit i j) (generatorCore i j) := by decide +kernel

private def parameterBit (i : Fin 7) (v : Fin 8 → ZMod 2) : ZMod 2 :=
  if i = 5 then v 1 + v 2 else if i = 6 then v 0 else 0

private theorem parameter_eq (i : Fin 7) (v : Fin 8 → ZMod 2) :
    parameter i v = evenElement (parameterBit i v) (parameter i v).left := by
  fin_cases i <;> rfl

set_option maxHeartbeats 16000000 in
private theorem generator_step (i : Fin 7) (x : SylowModel)
    (hx : rankFourCarrier i x) (j : Fin 8) :
    rankFourCarrier i (x * rankFourGenerators i j) ∧
      rankFourCoordinates i (x * rankFourGenerators i j) =
        rankFourCoordinates i x * rankFourCoordinates i (rankFourGenerators i j) := by
  obtain ⟨v, rfl⟩ := exists_parameter i x hx
  clear hx
  have hv : v = ![v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7] := by
    funext k
    fin_cases k <;> rfl
  rw [hv]
  clear hv
  generalize (v 0) = b0
  generalize (v 1) = b1
  generalize (v 2) = b2
  generalize (v 3) = b3
  generalize (v 4) = b4
  generalize (v 5) = b5
  generalize (v 6) = b6
  generalize (v 7) = b7
  clear v
  rw [generator_eq, parameter_eq, evenElement_mul]
  fin_cases i <;> fin_cases j
  all_goals dsimp only [rankFourCarrier, rankFourCoordinates, evenElement, Core.mul,
    evenCoreAction, generatorBit, generatorCore, parameterBit, parameter,
    Matrix.cons_val, Fin.reduceFinMk, Fin.isValue]
  all_goals revert b0 b1 b2 b3 b4 b5 b6 b7
  all_goals decide +kernel

private def squareWords : Fin 7 → Fin 4 → List (List (Fin 8)) :=
  ![![[[2, 1]], [[2], [2, 1]], [[0, 1]], [[0, 4]]],
    ![[[1, 2]], [[1], [2, 5]], [[1, 0]], [[0, 4]]],
    ![[[1], [0, 1]], [[1], [1, 2]], [[1, 0]], [[0, 4]]],
    ![[[1, 0, 2]], [[1], [2, 5]], [[1, 0]], [[0, 2]]],
    ![[[1, 4]], [[1], [0, 1, 2]], [[1], [2]], [[0, 1]]],
    ![[[1]], [[0], [2]], [[0]], []],
    ![[[0, 1]], [[0]], [[2]], []]]

private def kernelGenerator : Fin 7 → Fin 4 → SylowModel :=
  ![![root 5, root 6 * root 7, root 8, root 9],
    ![root 5, root 6, root 8, root 9],
    ![root 5 * root 6, root 7, root 8, root 9],
    ![root 5, root 6 * root 7, root 8, root 9],
    ![root 5, root 6 * root 8, root 7, root 9],
    ![root 2 * root 3 * root 4 * root 8, root 7, root 9, 1],
    ![root 4 * root 5, root 8, root 9, 1]]

private def word {I : Type*} (g : I → SylowModel) (w : List I) : SylowModel :=
  (w.map g).prod

set_option maxHeartbeats 8000000 in
private theorem squareWords_valid : ∀ i j,
    word (fun w => (evalWord (rankFourGenerators i) w) ^ 2) (squareWords i j) =
      kernelGenerator i j := by decide +kernel

private def kernelWord (i : Fin 7) (x : SylowModel) : SylowModel :=
  let c := x.left
  let e : Fin 7 → Fin 4 → ZMod 2 :=
    ![![c.b5,c.b6,c.b8,c.b9], ![c.b5,c.b6,c.b8,c.b9],
      ![c.b5,c.b7,c.b8,c.b9], ![c.b5,c.b6,c.b8,c.b9],
      ![c.b5,c.b6,c.b7,c.b9], ![c.b2,c.b7,c.b9,0], ![c.b4,c.b8,c.b9,0]]
  kernelGenerator i 0 ^ (e i 0).val * kernelGenerator i 1 ^ (e i 1).val *
    kernelGenerator i 2 ^ (e i 2).val * kernelGenerator i 3 ^ (e i 3).val

set_option maxHeartbeats 8000000 in
private theorem kernelWord_valid (i : Fin 7) (x : SylowModel)
    (hx : rankFourCarrier i x) (hzero : rankFourCoordinates i x = 1) :
    kernelWord i x = x := by
  rcases x with ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩,t⟩
  fin_cases i
  all_goals dsimp [rankFourCarrier] at hx
  all_goals rcases hx with ⟨ht, hx⟩
  all_goals try (change t = _ at ht; subst t)
  all_goals rcases hx with ⟨h1, h2⟩
  all_goals try rcases h2 with ⟨h2, h3⟩
  all_goals have hz0 := congrArg (fun v : Binary 4 => v.toAdd 0) hzero
  all_goals have hz1 := congrArg (fun v : Binary 4 => v.toAdd 1) hzero
  all_goals have hz2 := congrArg (fun v : Binary 4 => v.toAdd 2) hzero
  all_goals have hz3 := congrArg (fun v : Binary 4 => v.toAdd 3) hzero
  all_goals clear hzero
  all_goals dsimp [rankFourCoordinates] at hz0 hz1 hz2 hz3
  all_goals simp_all only [zero_add, add_zero, add_eq_zero_iff_eq_neg]
  all_goals subst_vars
  all_goals try revert b0
  all_goals try revert b4
  all_goals try revert b5
  all_goals try revert b6
  all_goals try revert b7
  all_goals try revert b8
  all_goals try revert b9
  all_goals decide +kernel

private theorem generators_mem (i : Fin 7) (j : Fin 8) :
    rankFourGenerators i j ∈ smallEvenCandidate (rankFourIndex i) := by
  rw [rankFourCandidate_eq]
  exact Subgroup.subset_closure (Set.mem_range_self j)

private theorem candidate_induction (i : Fin 7) {p : SylowModel → Prop}
    (h1 : p 1)
    (hstep : ∀ x ∈ smallEvenCandidate (rankFourIndex i), ∀ j, p x →
      p (x * rankFourGenerators i j))
    (x : SylowModel) (hx : x ∈ smallEvenCandidate (rankFourIndex i)) : p x := by
  have hx' : x ∈ Submonoid.closure (Set.range (rankFourGenerators i)) := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    simpa only [Subgroup.mem_toSubmonoid, ← rankFourCandidate_eq] using hx
  clear hx
  induction hx' using Submonoid.closure_induction_right with
  | one => exact h1
  | mul_right x hx y hy ih =>
    obtain ⟨j, rfl⟩ := hy
    apply hstep x _ j ih
    rw [rankFourCandidate_eq]
    exact Subgroup.le_closure_toSubmonoid _ hx

private theorem candidate_carrier (i : Fin 7) (x : SylowModel)
    (hx : x ∈ smallEvenCandidate (rankFourIndex i)) : rankFourCarrier i x := by
  apply candidate_induction i _ _ x hx
  · exact (by decide +kernel : ∀ i, rankFourCarrier i 1) i
  · intro y _ j hy
    exact (generator_step i y hy j).1

private theorem coordinates_one : ∀ i, rankFourCoordinates i 1 = 1 := by decide +kernel

private theorem carrier_mul_candidate (i : Fin 7) (y : SylowModel)
    (hy : y ∈ smallEvenCandidate (rankFourIndex i)) :
    ∀ x, rankFourCarrier i x → rankFourCarrier i (x * y) ∧
      rankFourCoordinates i (x * y) = rankFourCoordinates i x * rankFourCoordinates i y := by
  apply candidate_induction i _ _ y hy
  · intro x hx
    simp only [mul_one, coordinates_one]
    exact ⟨hx, trivial⟩
  · intro y hy j ih x hx
    obtain ⟨hxy, he⟩ := ih x hx
    obtain ⟨hm, hq⟩ := generator_step i (x * y) hxy j
    refine ⟨by simpa only [mul_assoc] using hm, ?_⟩
    rw [← mul_assoc, hq, he, (generator_step i y (candidate_carrier i y hy) j).2,
      mul_assoc]

/-- The fixed binary coordinates preserve multiplication on the exact candidate. -/
public theorem rankFourMap_mul (i : Fin 7)
    (x y : smallEvenCandidate (rankFourIndex i)) :
    rankFourMap i (x * y) = rankFourMap i x * rankFourMap i y :=
  (carrier_mul_candidate i y.val y.property x.val
    (candidate_carrier i x.val x.property)).2

private theorem word_mem {I : Type*} (D : Subgroup SylowModel)
    (g : I → SylowModel) (hg : ∀ j, g j ∈ D) (w : List I) : word g w ∈ D := by
  induction w with
  | nil => exact D.one_mem
  | cons j w ih => exact D.mul_mem (hg j) ih

private theorem kernelGenerator_mem (i : Fin 7) (D : Subgroup SylowModel)
    (hsq : ∀ x ∈ smallEvenCandidate (rankFourIndex i), x ^ 2 ∈ D)
    (j : Fin 4) : kernelGenerator i j ∈ D := by
  rw [← squareWords_valid i j]
  apply word_mem
  intro w
  exact hsq _ (evalWord_mem _ _ (generators_mem i) w)

private theorem coordinates_mem_of_squares (i : Fin 7) (D : Subgroup SylowModel)
    (hsq : ∀ x ∈ smallEvenCandidate (rankFourIndex i), x ^ 2 ∈ D)
    (x : SylowModel) (hx : rankFourCarrier i x)
    (hzero : rankFourCoordinates i x = 1) : x ∈ D := by
  rw [← kernelWord_valid i x hx hzero]
  unfold kernelWord
  repeat apply Subgroup.mul_mem
  all_goals exact D.pow_mem (kernelGenerator_mem i D hsq _) _

private theorem binary_square : ∀ v : Binary 4, v * v = 1 := by decide +kernel

/-- The internal equations describe exactly the original root-generated candidates. -/
public theorem rankFour_mem_iff_carrier (i : Fin 7) (x : SylowModel) :
    x ∈ smallEvenCandidate (rankFourIndex i) ↔ rankFourCarrier i x := by
  refine ⟨candidate_carrier i x, fun hx => ?_⟩
  obtain ⟨y, hy⟩ := rankFourMap_surjective i (rankFourCoordinates i x)
  have hxy := carrier_mul_candidate i y.val y.property x hx
  have hzero : rankFourCoordinates i (x * y.val) = 1 := by
    rw [hxy.2, ← hy]
    exact binary_square _
  have hm : x * y.val ∈ smallEvenCandidate (rankFourIndex i) :=
    coordinates_mem_of_squares i _ (fun z hz => Subgroup.pow_mem _ hz 2) _ hxy.1 hzero
  simpa only [mul_inv_cancel_right] using
    (smallEvenCandidate (rankFourIndex i)).mul_mem hm
      ((smallEvenCandidate (rankFourIndex i)).inv_mem y.property)

/-- The zero fibers of the fixed coordinates are precisely the Frattini subgroups. -/
public theorem rankFourMap_eq_one_iff_mem_frattini (i : Fin 7)
    (x : smallEvenCandidate (rankFourIndex i)) :
    rankFourMap i x = 1 ↔ x ∈ frattini (smallEvenCandidate (rankFourIndex i)) := by
  let U := smallEvenCandidate (rankFourIndex i)
  let π : U →* Binary 4 := MonoidHom.mk' (rankFourMap i) (rankFourMap_mul i)
  have hU : IsPGroup 2 U := (IsPGroup.of_card (n := 12) card).to_subgroup U
  have hphi := hU.frattini_eq_closure_squares
  constructor
  · intro hx
    let D := (frattini U).map U.subtype
    have hsq (y : SylowModel) (hy : y ∈ U) : y ^ 2 ∈ D := by
      refine ⟨(⟨y, hy⟩ : U) ^ 2, ?_, rfl⟩
      rw [hphi]
      exact Subgroup.subset_closure ⟨⟨y, hy⟩, rfl⟩
    have hval : x.val ∈ D := coordinates_mem_of_squares i D hsq x.val
      (candidate_carrier i x.val x.property) hx
    obtain ⟨y, hy, he⟩ := hval
    exact (show y = x from Subtype.ext he) ▸ hy
  · intro hx
    have hle : frattini U ≤ π.ker := by
      rw [hphi]
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨y, rfl⟩
      change π (y ^ 2) = 1
      rw [map_pow, pow_two]
      exact binary_square _
    exact hle hx

end ReeTwo.SylowModel.SmallEvenAutB
