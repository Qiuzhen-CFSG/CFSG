module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.Subgroup

/-!
# A candidate local presentation with a marked comparison map

The seven short words are discovery data from the subgroup image in the
364-point permutation quotient. The first is the square of the first generator.
The other six still need proofs in the original six-relator group; no quotient
calculation supplies those proofs.

Once the seven identities hold on the fixed subgroup generators, the universal
property gives a surjection onto that actual subgroup. Thus an independent finite
order bound for this local presentation transfers to the subgroup. Both premises
are retained explicitly.

Source: the reproducible GAP computation in `source/Discover.g`, starting from
the six ATLAS words and `G23G1-max3W1`. The output is not trusted proof data.
-/

@[expose] public section

namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound

open Subgroup.CosetWordCertificate

/-- Seven literal local words; signs follow the same convention as the source words. -/
def localRelatorLetters : Fin 7 → Word Bool :=
  ![[(false, true), (false, true)],
    [(true, true), (true, true), (true, true), (true, true), (true, true), (true, true), (true, true), (true, true), (true, true)],
    [(false, true), (true, false), (true, false), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (true, false), (true, false), (false, true), (true, false), (false, true), (true, true)],
    [(true, false), (false, true), (true, true), (true, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (true, false), (true, false), (false, true), (true, true), (false, true), (true, false)],
    [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true)],
    [(false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (true, true), (false, true), (true, false), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false)],
    [(true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (true, true), (false, true), (true, true), (true, true), (true, true), (true, true), (false, true), (true, true), (true, true), (false, true), (true, false), (true, false), (true, false), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true)]]

def localRelator (i : Fin 7) : FreeGroup Bool := FreeGroup.mk (localRelatorLetters i)

abbrev LocalPresented := PresentedGroup (Set.range localRelator)

def localGenerator (s : Bool) : LocalPresented := PresentedGroup.of s

/-- The comparison is defined only after proving the actual lifted relations. -/
def localHom (hrel : ∀ i, eval boundGenerator (localRelatorLetters i) = 1) :
    LocalPresented →* Presentation.Presented :=
  PresentedGroup.toGroup (f := boundGenerator) (by
    rintro _ ⟨i, rfl⟩
    exact hrel i)

@[simp] theorem localHom_generator
    (hrel : ∀ i, eval boundGenerator (localRelatorLetters i) = 1) (s : Bool) :
    localHom hrel (localGenerator s) = boundGenerator s :=
  PresentedGroup.toGroup.of _

/-- The image is exactly the subgroup on the fixed source words. -/
theorem localHom_range
    (hrel : ∀ i, eval boundGenerator (localRelatorLetters i) = 1) :
    (localHom hrel).range = boundSubgroup := by
  rw [MonoidHom.range_eq_map,
    ← PresentedGroup.closure_range_of (Set.range localRelator),
    MonoidHom.map_closure, ← Set.range_comp]
  congr 1
  apply congrArg Set.range
  funext s
  exact localHom_generator hrel s

/-- Transfer the local finite bound through the marked map onto the actual subgroup. -/
theorem finite_card_boundSubgroup_le_of_local
    (hrel : ∀ i, eval boundGenerator (localRelatorLetters i) = 1)
    (hlocal : Finite LocalPresented ∧ Nat.card LocalPresented ≤ 11664) :
    Finite boundSubgroup ∧ Nat.card boundSubgroup ≤ 11664 := by
  let := hlocal.1
  have hs := (localHom hrel).rangeRestrict_surjective
  have hf : Finite (localHom hrel).range := Finite.of_surjective _ hs
  have hc : Nat.card (localHom hrel).range ≤ Nat.card LocalPresented :=
    Nat.card_le_card_of_surjective _ hs
  rw [localHom_range] at hf hc
  exact ⟨hf, hc.trans hlocal.2⟩

/-- The involution relation in the local package already lifts to the source group. -/
theorem localRelator_zero_holds : eval boundGenerator (localRelatorLetters 0) = 1 := by
  simpa [localRelatorLetters, eval_cons, pow_two] using boundGenerator_false_sq

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound
