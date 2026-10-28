module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Coverage.NormalizerInclusions.RowZero
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.RepresentativeGeometry.ResidualRoots.Pair00.Alphabet
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.CentralContainment.Signature
public import Theory.GroupTheory.BinaryCollection

/-!
# Finite covers of the two middle outer Held rows

The published rows of ranks two and three are covered by binary products of
their actual commuting involution generators. Four-point certificates establish
the group identities. Existing checked pure-pair permutation tables evaluate the
words, so fixed-point counts need no reduction of the original ATLAS programs.

Source: unchanged ATLAS HeG1-p2058B0, GLS3 Table 5.3p, and the literal rows in
Coverage.Representatives, for Aschbacher--Smith 15.3.41--42, printed p.1138.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.NormalizerInclusions.Middle
open CoverageData
open Held.TwoLocalCandidates.MaximalNormalizerCatalogue.CentralContainment (commonFixedCount)
open Theory.GroupTheory.BinaryCollection

def rowIndex (k : Fin 2) : Fin 4 := ⟨k.val + 1, by omega⟩
def dim (k : Fin 2) : ℕ := k.val + 2
def genWord (k : Fin 2) (i : Fin (dim k)) : List ℤ :=
  ((rowWords (rowIndex k))[i.val]?).getD []
def gen (k : Fin 2) (i : Fin (dim k)) : Held.He := word (genWord k i)
def tableGen : Fin 4 → Equiv.Perm (Fin 2058)
  | 0 => Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair00.pair2
  | 1 => Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair00.pair3
  | 2 => Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair00.pair4
  | 3 => Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair00.pair5

theorem tableGen_eq (i : Fin 4) : tableGen i = Held.representation (generator i : Held.He) := by
  fin_cases i
  · exact Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair00.pair2_eq
  · exact Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair00.pair3_eq
  · exact Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair00.pair4_eq
  · exact Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair00.pair5_eq

def tableWord (w : List ℤ) : Equiv.Perm (Fin 2058) :=
 (w.map (fun k => if k < 0 then (tableGen (Fin.ofNat 4 (k.natAbs - 1)))⁻¹
   else tableGen (Fin.ofNat 4 (k.natAbs - 1)))).prod

theorem tableWord_eq (w : List ℤ) : tableWord w = Held.representation (word w : Held.He) := by
  change tableWord w = (Held.representation.comp pureTwo.subtype) (word w)
  simp only [tableWord, word, map_list_prod, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro n _
  simp only [letter]
  split_ifs <;> simp only [map_inv, MonoidHom.coe_comp, Function.comp_apply,
    tableGen_eq] <;> rfl

def perm (k : Fin 2) (i : Fin (dim k)) : Equiv.Perm (Fin 2058) := tableWord (genWord k i)
theorem perm_eq (k : Fin 2) (i : Fin (dim k)) : perm k i = Held.representation (gen k i) :=
  tableWord_eq _

def normalForm (k : Fin 2) (n : Fin (2 ^ dim k)) : Held.He := product (List.ofFn (gen k)) n.val
def permForm (k : Fin 2) (n : Fin (2 ^ dim k)) : Equiv.Perm (Fin 2058) := product (List.ofFn (perm k)) n.val

def centralIndex (k : Fin 2) : Fin (2 ^ dim k) := ⟨2 ^ (dim k - 1), by fin_cases k <;> decide⟩

def tableCount (x y : Equiv.Perm (Fin 2058)) : ℕ :=
  ((List.finRange 2058).filter (fun v => x v = v ∧ y v = v)).length


theorem words_row (k : Fin 2) : rowWords (rowIndex k) = List.ofFn (genWord k) := by
  have h : ∀ k : Fin 2, rowWords (rowIndex k) = List.ofFn (genWord k) := by decide +kernel
  exact h k

theorem heldRow_eq_closure (k : Fin 2) :
    heldRow (rowIndex k) = closure (Set.range (gen k)) := by
  rw [heldRow, row, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨w, hw, rfl⟩, rfl⟩
    rw [words_row] at hw
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨word (genWord k i), ⟨genWord k i, by
      rw [words_row]; exact List.mem_ofFn.mpr ⟨i, rfl⟩, rfl⟩, rfl⟩

theorem gen_mem (k : Fin 2) (i : Fin (dim k)) : gen k i ∈ heldRow (rowIndex k) := by
  rw [heldRow_eq_closure]
  exact subset_closure (Set.mem_range_self i)

private theorem map_product {G H : Type*} [Group G] [Group H]
    (f : G →* H) (l : List G) (n : ℕ) :
    f (product l n) = product (l.map f) n := by
  induction l generalizing n with
  | nil => exact f.map_one
  | cons a l ih => simp only [product, List.map_cons, map_mul, map_pow, ih]

theorem permForm_eq (k : Fin 2) (n : Fin (2 ^ dim k)) :
    permForm k n = Held.representation (normalForm k n) := by
  rw [normalForm, map_product, List.map_ofFn]
  change _ = product (List.ofFn (fun i => Held.representation (gen k i))) n.val
  simp only [← perm_eq]
  rfl

private theorem product_mem {G : Type*} [Group G] (K : Subgroup G) (l : List G)
    (hl : ∀ x ∈ l, x ∈ K) (n : ℕ) : product l n ∈ K := by
  induction l generalizing n with
  | nil => exact K.one_mem
  | cons a l ih =>
    exact K.mul_mem (K.pow_mem (hl a List.mem_cons_self) _)
      (ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)) _)

theorem normalForm_mem (k : Fin 2) (n : Fin (2 ^ dim k)) :
    normalForm k n ∈ heldRow (rowIndex k) := by
  apply product_mem
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact gen_mem k i

theorem normalForm_central (k : Fin 2) : normalForm k (centralIndex k) = rowZeroElement := by
  fin_cases k
  · change product (List.ofFn (fun i : Fin 2 => gen 0 i)) 2 = rowZeroElement
    simp only [List.ofFn_succ, List.ofFn_zero, product, Nat.reduceMod, Nat.reduceDiv,
      pow_zero, pow_one, one_mul, mul_one]
    rfl
  · change product (List.ofFn (fun i : Fin 3 => gen 1 i)) 4 = rowZeroElement
    simp only [List.ofFn_succ, List.ofFn_zero, product, Nat.reduceMod, Nat.reduceDiv,
      pow_zero, pow_one, one_mul, mul_one]
    rfl

set_option maxRecDepth 8192 in
private theorem squares_check : ∀ k : Fin 2, ∀ i : Fin (dim k), ∀ x : Fin 4,
    (perm k i * perm k i) ⟨x.val, by omega⟩ = ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem commute_check : ∀ k : Fin 2, ∀ i j : Fin (dim k), ∀ x : Fin 4,
    (perm k i * perm k j) ⟨x.val, by omega⟩ =
      (perm k j * perm k i) ⟨x.val, by omega⟩ := by
  decide +kernel

theorem gen_square (k : Fin 2) (i : Fin (dim k)) : gen k i * gen k i = 1 := by
  apply Held.eq_of_four_point_images
  simp only [map_mul, map_one, ← perm_eq]
  exact squares_check k i

theorem gen_commute (k : Fin 2) (i j : Fin (dim k)) : gen k i * gen k j = gen k j * gen k i := by
  apply Held.eq_of_four_point_images
  simp only [map_mul, ← perm_eq]
  exact commute_check k i j

private theorem triangular_of_commuting {G : Type*} [Group G] (l : List G)
    (hs : ∀ a ∈ l, a * a = 1) (hc : ∀ a ∈ l, ∀ b ∈ l, a * b = b * a) :
    triangular l := by
  induction l with
  | nil => trivial
  | cons a l ih =>
    refine ⟨?_, ?_, ih (fun b hb => hs b (List.mem_cons_of_mem _ hb))
      (fun b hb c hc' => hc b (List.mem_cons_of_mem _ hb) c (List.mem_cons_of_mem _ hc'))⟩
    · rw [hs a (List.mem_cons_self)]
      exact one_mem _
    · intro b hb
      have he : a⁻¹ * b * a = b := by
        rw [mul_assoc, ← hc a List.mem_cons_self b (List.mem_cons_of_mem _ hb),
          inv_mul_cancel_left]
      rw [he]
      exact subset_closure hb

theorem normalForm_cover (k : Fin 2) {x : Held.He} (hx : x ∈ heldRow (rowIndex k)) :
    ∃ n : Fin (2 ^ dim k), normalForm k n = x := by
  rw [heldRow_eq_closure] at hx
  have ht : triangular (List.ofFn (gen k)) := by
    apply triangular_of_commuting
    · intro a ha
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      exact gen_square k i
    · intro a ha b hb
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb
      exact gen_commute k i j
  obtain ⟨n, hn, he⟩ := cover (List.ofFn (gen k)) ht x (by
    simpa only [List.mem_ofFn', Set.ofPred_mem_eq] using hx)
  exact ⟨⟨n, by simpa using hn⟩, he⟩

theorem tableCount_eq (x y : Equiv.Perm (Fin 2058)) :
    tableCount x y =
      (Finset.univ.filter (fun v : Fin 2058 => x v = v ∧ y v = v)).card := by
  rw [tableCount, ← List.toFinset_card_of_nodup ((List.nodup_finRange _).filter _),
    List.toFinset_filter, List.toFinset_finRange]
  simp only [decide_eq_true_eq]

theorem normal_count_eq (k : Fin 2) (i j : Fin (2 ^ dim k)) :
    commonFixedCount (normalForm k i) (normalForm k j) =
      tableCount (permForm k i) (permForm k j) := by
  rw [tableCount_eq, permForm_eq, permForm_eq]
  rfl

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.NormalizerInclusions.Middle
