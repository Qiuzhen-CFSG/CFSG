module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Data
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# The four selected Figure 2 images

These are the literal (b), (d), (b′), (d′) permutation subgroups, in that
order. The primed rows omit the common first generator. Membership in the
native star quotient is certified by words in its original generators.
Source: Kleidman--Wilson (1988), Figure 2, p.490, and 2.3.4--2.3.5, pp.492--493.
The quotient images alone do not assert anything about squares of their lifts.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.ElementaryEightGeometry
open Cardinality.QuotientCount.Image

private theorem word_eq_permutation : ∀ i, evalWord alphabet (word i) = permutation i := by
  decide +kernel

private theorem alphabet_mem : ∀ i, alphabet i ∈ StarGroup := by
  intro i
  fin_cases i
  · exact subset_closure (by simp [alphabet])
  · exact subset_closure (by simp [alphabet])
  · exact StarGroup.inv_mem (subset_closure (by simp))
  · exact StarGroup.inv_mem (subset_closure (by simp))

/-- The actual image element in the native quotient, with its word certificate. -/
def starElement (i : Fin 6) : StarGroup :=
  ⟨permutation i, by
    rw [← word_eq_permutation]
    exact StarOrderCertificate.word_mem alphabet StarGroup alphabet_mem (word i)⟩

@[simp] theorem starElement_val (i : Fin 6) : (starElement i).val = permutation i := rfl

/-- The certified word, exposed for lifting through the native quotient map. -/
theorem starElement_word (i : Fin 6) :
    evalWord alphabet (word i) = (starElement i).val := word_eq_permutation i

/-- Index 0 is (b), 1 is (d), 2 is (b′), and 3 is (d′). -/
def rowGeneratorIndex (r : Fin 4) (j : Fin 3) : Fin 6 :=
  if j = 0 then 0 else if r.val % 2 = 0 then j.castLE (by decide)
    else ⟨j.val + 2, by omega⟩

/-- The primed configurations replace the omitted first generator by the identity. -/
def rowGenerator (r : Fin 4) (j : Fin 3) : StarGroup :=
  if 2 ≤ r.val ∧ j = 0 then 1 else starElement (rowGeneratorIndex r j)

/-- A literal quotient subgroup, independent of any centralizer claim. -/
def rowImage (r : Fin 4) : Subgroup StarGroup := closure (Set.range (rowGenerator r))

theorem rowGenerator_mem (r : Fin 4) (j : Fin 3) : rowGenerator r j ∈ rowImage r :=
  subset_closure (Set.mem_range_self j)

private theorem generator_square : ∀ r j, rowGenerator r j * rowGenerator r j = 1 := by
  intro r j
  apply Subtype.ext
  revert r j
  decide +kernel

private theorem generator_commute : ∀ r i j, Commute (rowGenerator r i) (rowGenerator r j) := by
  intro r i j
  apply Subtype.ext
  revert r i j
  decide +kernel

/-- All four source images are elementary, including both omitted-generator rows. -/
instance rowImage_elementary (r : Fin 4) : IsElementaryAbelian 2 (rowImage r) := by
  let : IsMulCommutative (closure (Set.range (rowGenerator r))) := isMulCommutative_closure (by
    rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
    exact generator_commute r i j)
  apply IsElementaryAbelian.closure_of_isMulCommutative
  rintro _ ⟨j,rfl⟩
  simpa only [pow_two] using generator_square r j

end Janko4.LocalStructure.ElementaryEightGeometry
