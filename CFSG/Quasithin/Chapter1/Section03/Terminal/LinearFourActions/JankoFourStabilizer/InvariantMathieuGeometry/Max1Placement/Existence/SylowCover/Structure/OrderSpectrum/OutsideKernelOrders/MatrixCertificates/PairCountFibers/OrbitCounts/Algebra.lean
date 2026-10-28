module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers.Plane
/-!
# Binary coordinates and plane bases for the J₄ pair count

Checked collection verifies the squares and commutation of the original basis
words. Binary product induction then identifies coordinate XOR with actual
multiplication. Sorting the three nonzero vectors of a plane preserves pair
rank by the binary involution shear identity.
Source context: Aschbacher–Smith A.3.12, pp.47–48; Kleidman–Wilson (1988),
pp.484–510. The coordinates and matrix realization are unchanged.
-/

@[expose] public section

open Janko4 Janko4.LocalStructure.SylowNormalEights
open Janko4.LocalStructure.SylowNormalEights.Presentation.Profiles
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.MatrixCertificates.PairCountFibers
attribute [local irreducible] modelGroup matrixA matrixB pairRank point
open Theory.GroupTheory.BinaryCollection
private theorem product_commute {G : Type*} [Group G] (l : List G) (x : G)
    (hc : ∀ y ∈ l, Commute x y) (n : ℕ) : Commute x (product l n) := by
  induction l generalizing n with
  | nil => exact Commute.one_right x
  | cons a l ih =>
    exact ((hc a List.mem_cons_self).pow_right _).mul_right
      (ih (fun y hy => hc y (List.mem_cons_of_mem a hy)) _)
private theorem product_xor {G : Type*} [Group G] (l : List G)
    (hs : ∀ x ∈ l, x * x = 1) (hc : ∀ x ∈ l, ∀ y ∈ l, Commute x y)
    (n m : ℕ) : product l (n ^^^ m) = product l n * product l m := by
  induction l generalizing n m with
  | nil => simp [product]
  | cons a l ih =>
    have hs' := fun x hx => hs x (List.mem_cons_of_mem a hx)
    have hc' := fun x hx y hy => hc x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy)
    have ha := hs a List.mem_cons_self
    have ht := product_commute l a (fun y hy => hc a List.mem_cons_self y (List.mem_cons_of_mem a hy)) (n / 2)
    have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
    have hm : m % 2 = 0 ∨ m % 2 = 1 := by omega
    simp only [product, Nat.xor_div_two, ih hs' hc', Nat.xor_mod_two_pow (n := 1)]
    rcases hn with hn | hn <;> rcases hm with hm | hm
    all_goals simp only [hn, hm, Nat.reduceXor, pow_zero, pow_one, one_mul]
    · rw [← mul_assoc, ht.eq, mul_assoc]
    · exact (mul_assoc _ _ _).symm
    · rw [← mul_assoc, ht.eq, mul_assoc (product l (n / 2)) a a, ha, mul_one]

private theorem words_product (ws : List (List (Fin 21))) (n : ℕ) :
    wordValue (selectWords ws n) = product (ws.map wordValue) n := by
  induction ws generalizing n with
  | nil => rfl
  | cons w ws ih =>
    simp only [selectWords, List.map_cons, product]
    split_ifs with h
    · simp only [List.nil_append, h, pow_zero, one_mul, ih]
    · have hn : n % 2 = 1 := by omega
      simp only [wordValue_append, hn, pow_one, ih]

private theorem words_square (i : Fin 9) :
    ∀ x ∈ (candidateWords i).map wordValue, x * x = 1 := by
  intro x hx
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
  obtain ⟨a, rfl⟩ := List.mem_iff_get.mp hw
  have h : ∀ (i : Fin 9) (a : Fin (candidateWords i).length),
      collect 128 ((candidateWords i)[a.val] ++ (candidateWords i)[a.val]) = [] := by
    intro i
    fin_cases i <;> decide +kernel
  simpa only [List.get_eq_getElem, wordValue_append, wordValue_nil] using wordValue_eq_of_collect 128 _ _ (h i a)

private theorem words_commute (i : Fin 9) :
    ∀ x ∈ (candidateWords i).map wordValue,
    ∀ y ∈ (candidateWords i).map wordValue, Commute x y := by
  intro x hx y hy
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hy
  obtain ⟨a, rfl⟩ := List.mem_iff_get.mp hw
  obtain ⟨b, rfl⟩ := List.mem_iff_get.mp hv
  have h : ∀ (i : Fin 9) (a b : Fin (candidateWords i).length),
      collect 128 ((candidateWords i)[a.val] ++ (candidateWords i)[b.val]) =
        collect 128 ((candidateWords i)[b.val] ++ (candidateWords i)[a.val]) := by
    intro i
    fin_cases i <;> decide +kernel
  change _ * _ = _ * _
  rw [← wordValue_append, ← wordValue_append]
  exact (collect_sound 128 _).symm.trans ((congrArg wordValue (h i a b)).trans
    (collect_sound 128 _))

/-- Addition in the original binary coordinate order. -/
def orbitXor (i : Fin 9) (a b : Fin (candidateOrder i)) : Fin (candidateOrder i) :=
  ⟨a.val ^^^ b.val, by
    exact (Nat.xor_lt_two_pow (a.isLt.trans_eq (candidateOrder_eq i))
      (b.isLt.trans_eq (candidateOrder_eq i))).trans_eq (candidateOrder_eq i).symm⟩

/-- The coordinate XOR is the actual multiplication in the literal subgroup. -/
theorem point_orbitXor (i : Fin 9) (a b : Fin (candidateOrder i)) :
    point i (orbitXor i a b) = point i a * point i b := by
  simp only [point, ← map_mul]
  apply congrArg realization
  simp only [abstractPoint, orbitXor, words_product]
  exact product_xor _ (words_square i) (words_commute i) _ _

theorem point_commute (i : Fin 9) (a b : Fin (candidateOrder i)) :
    point i a * point i b = point i b * point i a := by
  rw [← point_orbitXor, ← point_orbitXor]
  congr 1
  apply Fin.ext
  exact Nat.xor_comm _ _

/-- The least two nonzero vectors of a binary plane, also defined on dependent pairs. -/
def orbitPlane (i : Fin 9) (a b : Fin (candidateOrder i)) :
    Fin (candidateOrder i) × Fin (candidateOrder i) :=
  let c := orbitXor i a b
  if a ≤ b then
    if b ≤ c then (a,b) else if a ≤ c then (a,c) else (c,a)
  else
    if a ≤ c then (b,a) else if b ≤ c then (b,c) else (c,b)

/-- Sorting a binary plane changes only its basis, and preserves pair rank. -/
theorem pairRank_orbitPlane (i : Fin 9) (hi : 5 ≤ i.val)
    (a b : Fin (candidateOrder i)) :
    pairRank (point i (orbitPlane i a b).1) (point i (orbitPlane i a b).2) =
      pairRank (point i a) (point i b) := by
  have hs := pairRank_swap (point i a) (point i b) (point_commute i a b)
  have ha : pairRank (point i a) (point i (orbitXor i a b)) =
      pairRank (point i a) (point i b) := by
    rw [point_orbitXor, pairRank_point_shear i hi]
  have hb : pairRank (point i b) (point i (orbitXor i a b)) =
      pairRank (point i a) (point i b) := by
    rw [point_orbitXor, point_commute i a b, pairRank_point_shear i hi, ← hs]
  unfold orbitPlane
  dsimp only
  split_ifs
  · rfl
  · exact ha
  · exact (pairRank_swap _ _ (point_commute i _ _)).trans ha
  · exact hs.symm
  · exact hb
  · exact (pairRank_swap _ _ (point_commute i _ _)).trans hb
/-- Binary sum of a list of original subgroup coordinates. -/
def orbitFold (i : Fin 9) : List (Fin (candidateOrder i)) → ℕ → Fin (candidateOrder i)
  | [], _ => ⟨0, (by decide +kernel : ∀ i : Fin 9, 0 < candidateOrder i) i⟩
  | a :: l, n =>
    if n % 2 = 0 then orbitFold i l (n / 2) else orbitXor i a (orbitFold i l (n / 2))

private theorem map_product {G H : Type*} [Group G] [Group H] (f : G →* H)
    (l : List G) (n : ℕ) : f (product l n) = product (l.map f) n := by
  induction l generalizing n with
  | nil => exact f.map_one
  | cons a l ih => simp only [product, List.map_cons, map_mul, map_pow, ih]

theorem point_orbitFold (i : Fin 9) (l : List (Fin (candidateOrder i))) (n : ℕ) :
    point i (orbitFold i l n) = product (l.map (point i)) n := by
  induction l generalizing n with
  | nil => exact point_zero i
  | cons a l ih =>
    simp only [orbitFold, List.map_cons, product]
    split_ifs with h
    · simp only [h, pow_zero, one_mul, ih]
    · have hn : n % 2 = 1 := by omega
      rw [point_orbitXor, ih, hn, pow_one]

/-- It suffices to check a homomorphism on the original candidate basis words. -/
theorem point_map_of_basis (i : Fin 9) (f : Model →* Model)
    (images : List (Fin (candidateOrder i)))
    (h : (candidateWords i).map (fun w => f (realization (wordValue w))) =
      images.map (point i)) (n : Fin (candidateOrder i)) :
    f (point i n) = point i (orbitFold i images n.val) := by
  calc
    f (point i n) = product ((candidateWords i).map (fun w => f (realization (wordValue w)))) n.val := by
      simp only [point, abstractPoint, words_product, map_product, List.map_map, Function.comp_def]
    _ = point i (orbitFold i images n.val) := by rw [h, ← point_orbitFold]
end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.MatrixCertificates.PairCountFibers
