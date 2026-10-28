module

public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.Support.Multiple.Operators
public import Mathlib.RepresentationTheory.Irreducible

/-!
# Adjacent active roots force dimension at least twelve

Let `v` be a nonzero binary SL₅ local highest vector with adjacent active roots
`i,j`. On their three coordinates write `x,y` for the simple upper transvections,
`z` for the central upper transvection, and `w` for the longest exchange translate
of `v`. Write `A,B,C` for their operators `ρ(g) + 1`. Rank-one relations give
`A C B w = v`. These operators square to zero, `C` commutes with `A,B`, and
`A,B` commute on the image of `C`. Successive square-zero lifting therefore
proves independence of `w,Bw,Aw,ABw` and their four images under `C`.

A fourth coordinate supplies an upper transvection `t` commuting with `x,y,z`
and fixing `w`. Its difference kills all eight vectors. An exchange `s` conjugates
`z` to `t`, so the four `s`-translates of `w,Bw,Aw,ABw` have independent images
under that difference. Adjoining them gives twelve independent vectors.

The finite matrix identities are checked by kernel reduction. The argument
allows any additional active roots and does not require irreducibility.

Source application: Aschbacher--Smith, *The Classification of Quasithin Groups*,
I.1.6(7), printed p.408/PDF p.419.
-/

@[expose] public section

open scoped BigOperators

namespace Representation.SL5TenDimensional.Classification

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem lift_independent {ι : Type*} [Fintype ι]
    (D : V →ₗ[ZMod 2] V) (f : ι → V)
    (hD : ∀ k, D (D (f k)) = 0)
    (hf : LinearIndependent (ZMod 2) (fun k => D (f k))) :
    LinearIndependent (ZMod 2) (Sum.elim f (fun k => D (f k))) := by
  rw [Fintype.linearIndependent_iff] at hf ⊢
  intro c hc
  have he := congrArg D hc
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, map_add,
    map_sum, map_smul, hD, smul_zero, Finset.sum_const_zero, add_zero, map_zero] at he
  have hl := hf (fun k => c (.inl k)) he
  have hr : ∀ k, c (.inr k) = 0 := by
    apply hf
    simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      hl, zero_smul, Finset.sum_const_zero, zero_add] using hc
  intro k
  cases k with
  | inl k => exact hl k
  | inr k => exact hr k

private theorem independent_eight (A B C : V →ₗ[ZMod 2] V)
    (hAA : ∀ x, A (A x) = 0) (hBB : ∀ x, B (B x) = 0)
    (hCC : ∀ x, C (C x) = 0)
    (hAC : ∀ x, A (C x) = C (A x))
    (hBC : ∀ x, B (C x) = C (B x))
    (hAB : ∀ x, B (A (C x)) = A (B (C x)))
    (w : V) (hv : A (B (C w)) ≠ 0) :
    let f := Sum.elim (Sum.elim (fun _ : Unit => w) (fun _ : Unit => B w))
        (Sum.elim (fun _ : Unit => A w) (fun _ : Unit => A (B w)))
    LinearIndependent (ZMod 2) (Sum.elim f (fun k => C (f k))) := by
  -- First construct the four-vector image under C.
  have hpair : LinearIndependent (ZMod 2)
      (Sum.elim (fun _ : Unit => A (C w)) (fun _ : Unit => B (A (C w)))) := by
    apply lift_independent B (fun _ : Unit => A (C w)) (fun _ => hBB _)
    rw [Fintype.linearIndependent_iff]
    intro c hc k
    have he : c () • B (A (C w)) = 0 := by simpa using hc
    exact (smul_eq_zero.mp he).resolve_right (by rwa [hAB])
  have hfour : LinearIndependent (ZMod 2)
      (Sum.elim (Sum.elim (fun _ : Unit => C w) (fun _ : Unit => B (C w)))
        (Sum.elim (fun _ : Unit => A (C w)) (fun _ : Unit => A (B (C w))))) := by
    have he := lift_independent A
      (Sum.elim (fun _ : Unit => C w) (fun _ : Unit => B (C w)))
      (fun _ => hAA _) (by
        convert hpair using 1
        funext k
        cases k <;> simp [hAB])
    convert he using 1
    funext k
    cases k <;> simp only [Sum.elim_inl, Sum.elim_inr]
    rename_i k
    cases k <;> rfl
  dsimp only
  apply lift_independent C _ (fun _ => hCC _)
  convert hfour using 1
  funext k
  rcases k with (k | k) | (k | k) <;> simp [← hAC, ← hBC]

private theorem join_independent {ι κ : Type*} [Fintype ι] [Fintype κ]
    (D : V →ₗ[ZMod 2] V) (f : ι → V) (g : κ → V)
    (hf : LinearIndependent (ZMod 2) f) (hDf : ∀ k, D (f k) = 0)
    (hg : LinearIndependent (ZMod 2) (fun k => D (g k))) :
    LinearIndependent (ZMod 2) (Sum.elim f g) := by
  rw [Fintype.linearIndependent_iff] at hf hg ⊢
  intro c hc
  have he := congrArg D hc
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, map_add,
    map_sum, map_smul, hDf, smul_zero, Finset.sum_const_zero, zero_add, map_zero] at he
  have hr := hg (fun k => c (.inr k)) he
  have hl : ∀ k, c (.inl k) = 0 := by
    apply hf
    simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      hr, zero_smul, Finset.sum_const_zero, add_zero] using hc
  intro k
  cases k with
  | inl k => exact hl k
  | inr k => exact hr k

namespace Adjacent

private def longUpper (i j : Fin 4) : Group :=
  simpleUpper i * simpleUpper j * simpleUpper i * simpleUpper j

private def longestExchange (i j : Fin 4) : Group := simpleSwap i * simpleSwap j * simpleSwap i

private def rootSum (ρ : Representation (ZMod 2) Group V) (g : Group) : V →ₗ[ZMod 2] V :=
  ρ g + LinearMap.id

private theorem binary_add_self (x : V) : x + x = 0 := by
  have hh : (1 : ZMod 2) + 1 = 0 := by decide
  simpa only [add_smul, one_smul, zero_smul] using congrArg (fun c : ZMod 2 => c • x) hh

private theorem rootSum_apply (ρ : Representation (ZMod 2) Group V) (g : Group) (x : V) :
    rootSum ρ g x = ρ g x + x := rfl

private theorem act_mul (ρ : Representation (ZMod 2) Group V) (g k : Group) (x : V) :
    ρ g (ρ k x) = ρ (g * k) x := by rw [map_mul]; rfl

private theorem rootSum_square (ρ : Representation (ZMod 2) Group V)
    {g : Group} (hg : g * g = 1) (x : V) : rootSum ρ g (rootSum ρ g x) = 0 := by
  simp only [rootSum_apply, map_add, act_mul, hg, map_one, Module.End.one_apply]
  calc
    _ = (x + x) + (ρ g x + ρ g x) := by abel
    _ = 0 := by rw [binary_add_self, binary_add_self, add_zero]

private theorem rootSum_move (ρ : Representation (ZMod 2) Group V)
    {g k t : Group} (he : g * t = t * k) (x : V) :
    rootSum ρ g (ρ t x) = ρ t (rootSum ρ k x) := by
  simp only [rootSum_apply, map_add, act_mul, he]

private theorem rootSum_commute (ρ : Representation (ZMod 2) Group V)
    {g k : Group} (he : g * k = k * g) (x : V) :
    rootSum ρ g (rootSum ρ k x) = rootSum ρ k (rootSum ρ g x) := by
  simp only [rootSum_apply, map_add, act_mul, he]
  abel

private theorem upper_square (i : Fin 4) : simpleUpper i * simpleUpper i = 1 := by
  revert i
  decide

private theorem long_square (i j : Fin 4) (hij : i.val + 1 = j.val) :
    longUpper i j * longUpper i j = 1 := by
  revert i j
  decide

private theorem long_left (i j : Fin 4) (hij : i.val + 1 = j.val) :
    simpleUpper i * longUpper i j = longUpper i j * simpleUpper i := by
  revert i j
  decide

private theorem long_right (i j : Fin 4) (hij : i.val + 1 = j.val) :
    simpleUpper j * longUpper i j = longUpper i j * simpleUpper j := by
  revert i j
  decide

private theorem adjacent_commutator (i j : Fin 4) (hij : i.val + 1 = j.val) :
    simpleUpper j * simpleUpper i * longUpper i j = simpleUpper i * simpleUpper j ∧
    simpleUpper i * simpleUpper j * longUpper i j = simpleUpper j * simpleUpper i := by
  revert i j
  decide

private theorem conjugate_roots (i j : Fin 4) (hij : i.val + 1 = j.val) :
    simpleUpper j * simpleSwap i = simpleSwap i * longUpper i j ∧
    longUpper i j * simpleSwap i = simpleSwap i * simpleUpper j ∧
    longUpper i j * simpleSwap j = simpleSwap j * simpleUpper i := by
  revert i j
  decide

private theorem sums_commute_on_long (ρ : Representation (ZMod 2) Group V)
    (i j : Fin 4) (hij : i.val + 1 = j.val) (x : V) :
    rootSum ρ (simpleUpper j) (rootSum ρ (simpleUpper i) (rootSum ρ (longUpper i j) x)) =
      rootSum ρ (simpleUpper i) (rootSum ρ (simpleUpper j) (rootSum ρ (longUpper i j) x)) := by
  simp only [rootSum_apply, map_add, act_mul, ← mul_assoc,
    (adjacent_commutator i j hij).1, (adjacent_commutator i j hij).2]
  abel

private theorem rootSum_active {ρ : Representation (ZMod 2) Group V}
    {J : Finset (Fin 4)} {v : V} (h : LocalHighestVector ρ J v)
    {i : Fin 4} (hi : i ∈ J) : rootSum ρ (simpleUpper i) (ρ (simpleSwap i) v) = v := by
  have hn (x : V) : -x = x := by
    apply add_right_cancel (b := x)
    rw [neg_add_cancel, binary_add_self]
  have hs := h.upperDifference_swap hi
  change ρ (simpleUpper i) (ρ (simpleSwap i) v) - ρ (simpleSwap i) v = v at hs
  change ρ (simpleUpper i) (ρ (simpleSwap i) v) + ρ (simpleSwap i) v = v
  simpa only [sub_eq_add_neg, hn] using hs

private theorem norm_longestExchange {ρ : Representation (ZMod 2) Group V}
    {J : Finset (Fin 4)} {v : V} (h : LocalHighestVector ρ J v)
    {i j : Fin 4} (hi : i ∈ J) (hj : j ∈ J) (hij : i.val + 1 = j.val) :
    rootSum ρ (simpleUpper i) (rootSum ρ (longUpper i j)
      (rootSum ρ (simpleUpper j) (ρ (longestExchange i j) v))) = v := by
  obtain ⟨hya, hza, hzb⟩ := conjugate_roots i j hij
  simp only [longestExchange, map_mul, Module.End.mul_apply]
  rw [rootSum_move ρ hya, rootSum_move ρ hza, rootSum_move ρ hzb,
    rootSum_active h hi, rootSum_active h hj, rootSum_active h hi]

/-- Four lifts of the central-root image in the adjacent rank-two module. -/
private def fourVectors (ρ : Representation (ZMod 2) Group V) (i j : Fin 4) (v : V) :=
  let w := ρ (longestExchange i j) v
  let A := rootSum ρ (simpleUpper i)
  let B := rootSum ρ (simpleUpper j)
  Sum.elim (Sum.elim (fun _ : Unit => w) (fun _ : Unit => B w))
    (Sum.elim (fun _ : Unit => A w) (fun _ : Unit => A (B w)))

/-- Eight vectors in the adjacent rank-two module. -/
private def eightVectors (ρ : Representation (ZMod 2) Group V) (i j : Fin 4) (v : V) :=
  let f := fourVectors ρ i j v
  Sum.elim f (fun k => rootSum ρ (longUpper i j) (f k))

private theorem independent_rankTwo {ρ : Representation (ZMod 2) Group V}
    {J : Finset (Fin 4)} {v : V} (h : LocalHighestVector ρ J v) (hv : v ≠ 0)
    {i j : Fin 4} (hi : i ∈ J) (hj : j ∈ J) (hij : i.val + 1 = j.val) :
    LinearIndependent (ZMod 2) (eightVectors ρ i j v) := by
  apply independent_eight
    (rootSum ρ (simpleUpper i)) (rootSum ρ (simpleUpper j)) (rootSum ρ (longUpper i j))
    (rootSum_square ρ (upper_square i)) (rootSum_square ρ (upper_square j))
    (rootSum_square ρ (long_square i j hij))
    (rootSum_commute ρ (long_left i j hij)) (rootSum_commute ρ (long_right i j hij))
    (sums_commute_on_long ρ i j hij)
  rw [rootSum_commute ρ (long_right i j hij)]
  rwa [norm_longestExchange h hi hj hij]

private theorem independent_centralImage {ρ : Representation (ZMod 2) Group V}
    {J : Finset (Fin 4)} {v : V} (h : LocalHighestVector ρ J v) (hv : v ≠ 0)
    {i j : Fin 4} (hi : i ∈ J) (hj : j ∈ J) (hij : i.val + 1 = j.val) :
    LinearIndependent (ZMod 2) (fun k => rootSum ρ (longUpper i j) (fourVectors ρ i j v k)) :=
  (independent_rankTwo h hv hi hj hij).comp Sum.inr Sum.inr_injective

-- Exchange the rightmost coordinate of the triple with its right neighbor,
-- or the leftmost coordinate with its left neighbor for the final triple.
private def outsideRoot (i : Fin 4) : Fin 4 := if i = 0 then 2 else if i = 1 then 3 else 1
private def outsideUpper (i j : Fin 4) : Group :=
  simpleSwap (outsideRoot i) * longUpper i j * simpleSwap (outsideRoot i)

private theorem outside_relations (i j : Fin 4) (hij : i.val + 1 = j.val) :
    outsideUpper i j * simpleUpper i = simpleUpper i * outsideUpper i j ∧
    outsideUpper i j * simpleUpper j = simpleUpper j * outsideUpper i j ∧
    outsideUpper i j * longUpper i j = longUpper i j * outsideUpper i j ∧
    outsideUpper i j * longestExchange i j = longestExchange i j * simpleUpper (outsideRoot i) ∧
    outsideUpper i j * simpleSwap (outsideRoot i) = simpleSwap (outsideRoot i) * longUpper i j := by
  revert i j
  decide

private theorem outside_kills_eight {ρ : Representation (ZMod 2) Group V}
    {J : Finset (Fin 4)} {v : V} (h : LocalHighestVector ρ J v)
    {i j : Fin 4} (hij : i.val + 1 = j.val) :
    ∀ k, rootSum ρ (outsideUpper i j) (eightVectors ρ i j v k) = 0 := by
  obtain ⟨htx, hty, htz, htw, _⟩ := outside_relations i j hij
  have hw : rootSum ρ (outsideUpper i j) (ρ (longestExchange i j) v) = 0 := by
    rw [rootSum_move ρ htw]
    have hu := h.upper_fixed (outsideRoot i).castSucc (outsideRoot i).succ (by simp)
    change ρ (simpleUpper (outsideRoot i)) v = v at hu
    rw [rootSum_apply, hu, binary_add_self, map_zero]
  intro k
  rcases k with ((k | k) | (k | k)) | ((k | k) | (k | k)) <;>
    simp only [eightVectors, fourVectors, Sum.elim_inl, Sum.elim_inr,
      rootSum_commute ρ htx, rootSum_commute ρ hty, rootSum_commute ρ htz, hw, map_zero]

private theorem twelve_independent {ρ : Representation (ZMod 2) Group V}
    {J : Finset (Fin 4)} {v : V} (h : LocalHighestVector ρ J v) (hv : v ≠ 0)
    {i j : Fin 4} (hi : i ∈ J) (hj : j ∈ J) (hij : i.val + 1 = j.val) :
    LinearIndependent (ZMod 2) (Sum.elim (eightVectors ρ i j v)
      (fun k => ρ (simpleSwap (outsideRoot i)) (fourVectors ρ i j v k))) := by
  apply join_independent (rootSum ρ (outsideUpper i j)) _ _
    (independent_rankTwo h hv hi hj hij) (outside_kills_eight h hij)
  have he := independent_centralImage h hv hi hj hij
  have hinj : Function.Injective (ρ (simpleSwap (outsideRoot i))) :=
    fun x y he => by
      have hh := congrArg (ρ ((simpleSwap (outsideRoot i))⁻¹)) he
      simpa only [act_mul, inv_mul_cancel, map_one, Module.End.one_apply] using hh
  have hm := he.map' (ρ (simpleSwap (outsideRoot i))) (LinearMap.ker_eq_bot.mpr hinj)
  simpa only [rootSum_move ρ (outside_relations i j hij).2.2.2.2, Function.comp_def] using hm

end Adjacent

/-- Two adjacent active roots force twelve independent vectors, even without irreducibility. -/
theorem LocalHighestVector.twelve_le_finrank_of_adjacent [Module.Finite (ZMod 2) V]
    {ρ : Representation (ZMod 2) Group V} {J : Finset (Fin 4)} {v : V}
    (h : LocalHighestVector ρ J v) (hv : v ≠ 0) {i j : Fin 4}
    (hi : i ∈ J) (hj : j ∈ J) (hij : i.val + 1 = j.val) :
    12 ≤ Module.finrank (ZMod 2) V := by
  simpa using (Adjacent.twelve_independent h hv hi hj hij).fintype_card_le_finrank

/-- A ten-dimensional binary SL₅ module cannot have adjacent active highest-vector roots. -/
theorem LocalHighestVector.false_of_finrank_ten_of_adjacent
    {ρ : Representation (ZMod 2) Group V} {J : Finset (Fin 4)} {v : V}
    (h : LocalHighestVector ρ J v) (hv : v ≠ 0) (hdim : Module.finrank (ZMod 2) V = 10)
    {i j : Fin 4} (hi : i ∈ J) (hj : j ∈ J) (hij : i.val + 1 = j.val) : False := by
  let := Module.finite_of_finrank_pos (R := ZMod 2) (M := V) (by omega)
  have hh := h.twelve_le_finrank_of_adjacent hv hi hj hij
  omega

end Representation.SL5TenDimensional.Classification
