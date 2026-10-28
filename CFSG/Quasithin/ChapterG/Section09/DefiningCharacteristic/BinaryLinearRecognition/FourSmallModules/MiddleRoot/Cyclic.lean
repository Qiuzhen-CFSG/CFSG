module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules.LocalData
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.ExteriorOrthogonal
public import Mathlib.RepresentationTheory.Irreducible

/-!
# The cyclic module of a middle-root highest vector

For binary SL₄, the six exchange translates of a highest vector supported on
root 1 have exactly the generator actions on the exterior-square coordinates
01, 02, 03, 12, 13, 23. They therefore define an intertwining map from the
literal compound-matrix representation. Two upper-root differences, after a
coordinate exchange, extract each coefficient, so the map is injective when
the highest vector is nonzero. Irreducibility of its target gives surjectivity.
No degree bound, faithfulness, or splitting-field hypothesis is used.

The exterior coordinates and action are the checked ATLAS construction imported
below; its attribution and license remain in the owning modules.
Source: Aschbacher--Smith, combined manuscript (1 March 2004), G.9.3(12),
printed pp.354,356--357. This proves the middle-root recognition step used there.
-/

open Representation Atlas.Order20160A8
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules.MiddleRoot

-- Short exchange words representing the six unordered coordinate pairs.
private def word (w : List (Fin 3)) : Group := (w.map simpleSwap).prod
private def reps : Fin 6 → Group := fun k => word (![[], [1], [2,1], [0,1], [2,0,1], [1,2,0,1]] k)
private def inactive : Fin 4 → Group := fun a => word (![[], [0], [2], [0,2]] a)
private def swapIndex : Fin 3 → Fin 6 → Fin 6 :=
  ![![0,3,4,1,2,5], ![1,0,2,3,5,4], ![0,2,1,4,3,5]]
private def extra (k : Fin 6) : Fin 6 := if k = 1 then 0 else 4
private def correction (k : Fin 6) : Fin 4 := if k = 1 then 0 else 3

-- Evaluate words as coordinate functions before checking the matrix identities.
private def permMatrix (p : Fin 4 → Fin 4) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  fun i j => if i = p j then 1 else 0
set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
private theorem swap_matrix : ∀ i : Fin 3, (simpleSwap i).val =
    permMatrix (![![1,0,2,3], ![0,2,1,3], ![0,1,3,2]] i) := by decide
private theorem permMatrix_mul (p q : Fin 4 → Fin 4) :
    permMatrix p * permMatrix q = permMatrix (p ∘ q) := by
  ext i j
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (q j)]
  · simp [permMatrix]
  · intro b _ hb
    simp [permMatrix, hb]
  · simp

private def wordIndices (w : List (Fin 3)) : Fin 4 → Fin 4 :=
  w.foldr (fun j p => (![![1,0,2,3], ![0,2,1,3], ![0,1,3,2]] j) ∘ p) id
private theorem word_matrix (w : List (Fin 3)) : (word w).val = permMatrix (wordIndices w) := by
  induction w with
  | nil =>
    ext i j
    simp only [word, wordIndices, List.map_nil, List.prod_nil,
      Matrix.SpecialLinearGroup.coe_one, List.foldr_nil, id_eq, permMatrix, Matrix.one_apply]
    split_ifs with hij <;> simp [hij]
  | cons j w ih =>
    change (simpleSwap j * word w).val = _
    rw [Matrix.SpecialLinearGroup.coe_mul, swap_matrix, ih, permMatrix_mul]
    rfl
set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
private theorem reps_matrix : ∀ k : Fin 6, (reps k).val =
    permMatrix (![![0,1,2,3], ![0,2,1,3], ![0,3,1,2],
      ![1,2,0,3], ![1,3,0,2], ![2,3,0,1]] k) := by
  simp only [reps, word_matrix]
  decide
set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
private theorem inactive_matrix : ∀ a : Fin 4, (inactive a).val =
    permMatrix (![![0,1,2,3], ![1,0,2,3], ![0,1,3,2], ![1,0,3,2]] a) := by
  simp only [inactive, word_matrix]
  decide

private theorem group_eq_iff (a b : Group) : a = b ↔ a.val = b.val := Subtype.ext_iff

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
private theorem swap_reps : ∀ (j : Fin 3) (k : Fin 6), ∃ a : Fin 4,
    simpleSwap j * reps k = reps (swapIndex j k) * inactive a := by
  simp only [group_eq_iff, Matrix.SpecialLinearGroup.coe_mul, swap_matrix, reps_matrix, inactive_matrix]
  decide
set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
private theorem upper_reps_fixed : ∀ (k : Fin 6), k ≠ 1 → k ≠ 5 →
    ∃ (a b : Fin 4) (hab : a < b), simpleUpper 1 * reps k =
      reps k * Matrix.SpecialLinearGroup.transvection (ne_of_lt hab) (1 : ZMod 2) := by
  simp only [group_eq_iff, Matrix.SpecialLinearGroup.coe_mul, reps_matrix, simpleUpper,
    Matrix.SpecialLinearGroup.transvection_coe]
  decide
set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
private theorem upper_reps_active : ∀ (k : Fin 6), k = 1 ∨ k = 5 →
    simpleUpper 1 * reps k = reps k * inactive (correction k) * simpleLower 1 *
      inactive (correction k) := by
  simp only [group_eq_iff, Matrix.SpecialLinearGroup.coe_mul, reps_matrix, inactive_matrix,
    simpleUpper, simpleLower, Matrix.SpecialLinearGroup.transvection_coe]
  decide
set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
private theorem active_reps : ∀ (k : Fin 6), k = 1 ∨ k = 5 →
    reps k * inactive (correction k) * simpleSwap 1 =
      reps (extra k) * inactive (correction k) := by
  simp only [group_eq_iff, Matrix.SpecialLinearGroup.coe_mul, reps_matrix, inactive_matrix,
    swap_matrix]
  decide

/-- The literal six-coordinate exterior-square action of binary SL₄. -/
@[expose] public noncomputable def exterior : Representation (ZMod 2) Group (Bivectors.Six (ZMod 2)) where
  toFun g := Bivectors.exteriorMap g.val
  map_one' := Bivectors.exteriorMap_one
  map_mul' g h := Bivectors.exteriorMap_mul g.val h.val

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
private theorem exterior_swap : ∀ (j : Fin 3) (k : Fin 6),
    exterior (simpleSwap j) (Pi.single k 1) = Pi.single (swapIndex j k) 1 := by
  change ∀ j k, Bivectors.exteriorMap (simpleSwap j).val _ = _
  simp only [swap_matrix]
  decide
set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
private theorem exterior_upper : ∀ k : Fin 6,
    exterior (simpleUpper 1) (Pi.single k 1) =
      if k = 1 ∨ k = 5 then Pi.single k 1 + Pi.single (extra k) 1 else Pi.single k 1 := by
  decide

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) Group V} {v : V}

private theorem inactive_fixed (h : LocalHighestVector ρ {1} v) (a : Fin 4) :
    ρ (inactive a) v = v := by
  have h0 := h.inactive_fixed 0 (by decide)
  have h2 := h.inactive_fixed 2 (by decide)
  fin_cases a <;> simp [inactive, word, map_mul, Module.End.mul_apply, h0, h2]

private theorem swap_vectors (h : LocalHighestVector ρ {1} v) (j : Fin 3) (k : Fin 6) :
    ρ (simpleSwap j) (ρ (reps k) v) = ρ (reps (swapIndex j k)) v := by
  obtain ⟨a, ha⟩ := swap_reps j k
  change (ρ (simpleSwap j) * ρ (reps k)) v = _
  rw [← map_mul, ha, map_mul]
  change ρ (reps (swapIndex j k)) (ρ (inactive a) v) = _
  rw [inactive_fixed h]

private theorem add_self_binary (x : V) : x + x = 0 := by
  have ht : (1 : ZMod 2) + 1 = 0 := by decide
  simpa only [add_smul, one_smul, zero_smul] using congrArg (fun c : ZMod 2 => c • x) ht

private theorem upper_vectors (h : LocalHighestVector ρ {1} v) (k : Fin 6) :
    ρ (simpleUpper 1) (ρ (reps k) v) =
      if k = 1 ∨ k = 5 then ρ (reps k) v + ρ (reps (extra k)) v else ρ (reps k) v := by
  by_cases hk : k = 1 ∨ k = 5
  · rw [if_pos hk]
    have hl : ρ (simpleLower 1) v = v + ρ (simpleSwap 1) v := by
      have hr := h.active_relation 1 (Finset.mem_singleton_self _)
      have hr' := congrArg (fun x => x + ρ (simpleLower 1) v) hr
      simpa only [add_assoc, add_self_binary, add_zero, zero_add] using hr'.symm
    change (ρ (simpleUpper 1) * ρ (reps k)) v = _
    rw [← map_mul, upper_reps_active k hk, map_mul]
    change ρ (reps k * inactive (correction k) * simpleLower 1)
      (ρ (inactive (correction k)) v) = _
    rw [inactive_fixed h, map_mul]
    change ρ (reps k * inactive (correction k)) (ρ (simpleLower 1) v) = _
    rw [hl, map_add]
    congr 1
    · rw [map_mul]
      change ρ (reps k) (ρ (inactive (correction k)) v) = _
      rw [inactive_fixed h]
    · change (ρ (reps k * inactive (correction k)) * ρ (simpleSwap 1)) v = _
      rw [← map_mul, active_reps k hk, map_mul]
      change ρ (reps (extra k)) (ρ (inactive (correction k)) v) = _
      rw [inactive_fixed h]
  · rw [if_neg hk]
    obtain ⟨a,b,hab,heq⟩ := upper_reps_fixed k (fun h => hk (.inl h)) (fun h => hk (.inr h))
    change (ρ (simpleUpper 1) * ρ (reps k)) v = _
    rw [← map_mul, heq, map_mul]
    change ρ (reps k) (ρ (Matrix.SpecialLinearGroup.transvection (ne_of_lt hab) 1) v) = _
    rw [h.upper_fixed a b hab]

private def conjugatorWord : Fin 4 → Fin 4 → List (Fin 3) :=
  ![![[], [1,0], [0], [0,2]], ![[0,1,0], [], [], [2]],
    ![[0,1], [1], [], [1,2]], ![[0,2,1], [2,1], [1,2,1], []]]
set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
private theorem transvection_conjugate : ∀ (a b : Fin 4) (hab : a ≠ b),
    Matrix.SpecialLinearGroup.transvection hab (1 : ZMod 2) =
      word (conjugatorWord a b) * simpleUpper 1 * word (conjugatorWord a b).reverse := by
  intro a b hab
  apply Subtype.ext
  change (Matrix.SpecialLinearGroup.transvection hab (1 : ZMod 2)).val = _
  simp only [Matrix.SpecialLinearGroup.coe_mul, word_matrix, simpleUpper,
    Matrix.SpecialLinearGroup.transvection_coe]
  fin_cases a <;> fin_cases b <;> first | exact (hab rfl).elim | decide

/-- The map from the six exterior coordinates to the six highest-vector translates. -/
private noncomputable def cyclicMap (ρ : Representation (ZMod 2) Group V) (v : V) :
    Bivectors.Six (ZMod 2) →ₗ[ZMod 2] V :=
  (Pi.basisFun (ZMod 2) (Fin 6)).constr (ZMod 2) (fun k => ρ (reps k) v)

@[simp] private theorem cyclicMap_single (k : Fin 6) :
    cyclicMap ρ v (Pi.single k 1) = ρ (reps k) v := by
  simpa only [cyclicMap, Pi.basisFun_apply] using
    (Pi.basisFun (ZMod 2) (Fin 6)).constr_basis (ZMod 2) (fun k => ρ (reps k) v) k

@[simp] private theorem cyclicMap_highest : cyclicMap ρ v (Pi.single 0 1) = v := by
  rw [cyclicMap_single]
  have h0 : reps 0 = 1 := by decide
  rw [h0, map_one, Module.End.one_apply]

private theorem cyclicMap_intertwines (h : LocalHighestVector ρ {1} v) (g : Group) :
    (cyclicMap ρ v).comp (exterior g) = (ρ g).comp (cyclicMap ρ v) := by
  let P (g : Group) : Prop := (cyclicMap ρ v).comp (exterior g) = (ρ g).comp (cyclicMap ρ v)
  have hs (j : Fin 3) : P (simpleSwap j) := by
    apply (Pi.basisFun (ZMod 2) (Fin 6)).ext
    intro k
    simp only [Pi.basisFun_apply, LinearMap.comp_apply]
    change cyclicMap ρ v (exterior (simpleSwap j) (Pi.single k 1)) =
      ρ (simpleSwap j) (cyclicMap ρ v (Pi.single k 1))
    rw [exterior_swap, cyclicMap_single, cyclicMap_single, swap_vectors h]
  have hu : P (simpleUpper 1) := by
    apply (Pi.basisFun (ZMod 2) (Fin 6)).ext
    intro k
    simp only [Pi.basisFun_apply, LinearMap.comp_apply]
    change cyclicMap ρ v (exterior (simpleUpper 1) (Pi.single k 1)) =
      ρ (simpleUpper 1) (cyclicMap ρ v (Pi.single k 1))
    rw [exterior_upper, cyclicMap_single, upper_vectors h]
    split_ifs <;> simp
  have h1 : P 1 := by
    change (cyclicMap ρ v).comp (exterior 1) = (ρ 1).comp (cyclicMap ρ v)
    rw [map_one, map_one]
    change (cyclicMap ρ v).comp LinearMap.id = LinearMap.id.comp (cyclicMap ρ v)
    rw [LinearMap.comp_id, LinearMap.id_comp]
  have hm (a b : Group) (ha : P a) (hb : P b) : P (a * b) := by
    change (cyclicMap ρ v).comp (exterior (a * b)) = (ρ (a * b)).comp (cyclicMap ρ v)
    rw [map_mul, map_mul]
    change (cyclicMap ρ v).comp ((exterior a).comp (exterior b)) =
      ((ρ a).comp (ρ b)).comp (cyclicMap ρ v)
    rw [← LinearMap.comp_assoc, ha, LinearMap.comp_assoc, hb, ← LinearMap.comp_assoc]
  have hw (w : List (Fin 3)) : P (word w) := by
    induction w with
    | nil => exact h1
    | cons j w ih => exact hm _ _ (hs j) ih
  apply Matrix.SpecialLinearGroup.diagonal_transvection_induction' P g
  · intro i j hij c hc
    have hc1 : c = 1 := by
      have : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
      exact this c hc
    subst c
    have hd : Matrix.SpecialLinearGroup.diag2n hij (1 : ZMod 2) hc = 1 := by
      apply Subtype.ext
      simp [Matrix.SpecialLinearGroup.diag2n_coe]
    rw [hd]
    exact h1
  · intro i j hij c
    have hc : c = 0 ∨ c = 1 := by
      have : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
      exact this c
    rcases hc with rfl | rfl
    · simpa only [Matrix.SpecialLinearGroup.transvection_coeff_zero] using h1
    · rw [transvection_conjugate i j hij]
      exact hm _ _ (hm _ _ (hw _) hu) (hw _)
  · exact hm

private noncomputable def cyclicIntertwiner (h : LocalHighestVector ρ {1} v) :
    IntertwiningMap exterior ρ where
  __ := cyclicMap ρ v
  isIntertwining' := cyclicMap_intertwines h

private def reverseRep : Fin 6 → Group := fun k =>
  word ((![[], [1], [2,1], [0,1], [2,0,1], [1,2,0,1]] k).reverse)
-- The differences for roots 02 and 13 send coordinate 23 to 01 and kill the rest.
private def raiseLeft : Group := Matrix.SpecialLinearGroup.transvection (i := 0) (j := 2) (by decide) 1
private def raiseRight : Group := Matrix.SpecialLinearGroup.transvection (i := 1) (j := 3) (by decide) 1

private noncomputable def difference (g : Group) :
    Module.End (ZMod 2) (Bivectors.Six (ZMod 2)) := exterior g - 1

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
private theorem raise_coordinate (x : Bivectors.Six (ZMod 2)) :
    (difference raiseLeft) ((difference raiseRight) x) =
      x 5 • Pi.single 0 1 := by
  have heq : (difference raiseLeft).comp (difference raiseRight) =
      (LinearMap.proj (R := ZMod 2) 5).smulRight (Pi.single 0 1) := by
    apply (Pi.basisFun (ZMod 2) (Fin 6)).ext
    intro j
    simp only [Pi.basisFun_apply, LinearMap.comp_apply]
    revert j
    decide
  exact LinearMap.congr_fun heq x

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
private theorem reindex_coordinate (k : Fin 6) (x : Bivectors.Six (ZMod 2)) :
    exterior (reps 5 * reverseRep k) x 5 = x k := by
  have heq : (LinearMap.proj 5).comp (exterior (reps 5 * reverseRep k)) = LinearMap.proj k := by
    apply (Pi.basisFun (ZMod 2) (Fin 6)).ext
    intro j
    simp only [Pi.basisFun_apply, LinearMap.comp_apply]
    change exterior (reps 5 * reverseRep k) (Pi.single j 1) 5 = (Pi.single j (1 : ZMod 2) : Fin 6 → ZMod 2) k
    change Bivectors.exteriorMap (reps 5 * reverseRep k).val (Pi.single j 1) 5 = _
    rw [Matrix.SpecialLinearGroup.coe_mul, reps_matrix]
    simp only [reverseRep, word_matrix]
    revert k j
    decide
  exact LinearMap.congr_fun heq x

private theorem coordinate_extraction (k : Fin 6) (x : Bivectors.Six (ZMod 2)) :
    (difference raiseLeft)
      ((difference raiseRight) (exterior (reps 5 * reverseRep k) x)) =
        x k • Pi.single 0 1 := by
  rw [raise_coordinate, reindex_coordinate]

/-- The six translates are independent: two raising differences extract each coefficient. -/
private theorem cyclicMap_injective (h : LocalHighestVector ρ {1} v) (hv : v ≠ 0) :
    Function.Injective (cyclicMap ρ v) := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  have intertwine (g : Group) (x : Bivectors.Six (ZMod 2)) :
      cyclicMap ρ v (exterior g x) = ρ g (cyclicMap ρ v x) :=
    LinearMap.congr_fun (cyclicMap_intertwines h g) x
  ext k
  have he := congrArg (cyclicMap ρ v) (coordinate_extraction k x)
  simp only [difference, LinearMap.sub_apply, Module.End.one_apply, map_sub, intertwine, hx, map_zero,
    sub_self, map_smul, cyclicMap_highest] at he
  exact (smul_eq_zero.mp he.symm).resolve_right hv

/-- Irreducibility makes the nonzero cyclic map surjective. -/
private theorem cyclicMap_surjective [IsIrreducible ρ] (h : LocalHighestVector ρ {1} v)
    (hv : v ≠ 0) : Function.Surjective (cyclicMap ρ v) := by
  apply (IsIrreducible.surjective_or_eq_zero (cyclicIntertwiner h)).resolve_right
  intro hzero
  have hh := congrArg (fun f : IntertwiningMap exterior ρ => f (Pi.single 0 1)) hzero
  change cyclicMap ρ v (Pi.single 0 1) = 0 at hh
  rw [cyclicMap_highest] at hh
  exact hv hh

/-- Actual equivalence with the six-coordinate exterior-square representation. -/
private noncomputable def cyclicEquiv [IsIrreducible ρ] (h : LocalHighestVector ρ {1} v)
    (hv : v ≠ 0) : Representation.Equiv exterior ρ :=
  (cyclicIntertwiner h).ofBijective ⟨cyclicMap_injective h hv, cyclicMap_surjective h hv⟩

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules.MiddleRoot

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules

/-- A nonzero middle-root highest vector constructs an actual equivalence from
SL₄'s exterior square onto the given irreducible binary representation. -/
public noncomputable def LocalHighestVector.middleRootExteriorEquiv
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) Group V} [IsIrreducible ρ] {v : V}
    (h : LocalHighestVector ρ {1} v) (hv : v ≠ 0) :
    Representation.Equiv MiddleRoot.exterior ρ :=
  MiddleRoot.cyclicEquiv h hv

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules
