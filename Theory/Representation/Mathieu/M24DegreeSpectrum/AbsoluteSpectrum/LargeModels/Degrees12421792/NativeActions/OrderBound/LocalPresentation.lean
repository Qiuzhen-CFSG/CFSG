module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.Subgroup
public import Mathlib.Data.ZMod.QuotientGroup

/-!
# A marked local presentation for the M24 order-bound route

The nine words are a candidate presentation discovered on the subgroup image
specified by ATLAS M24G1-max8W1. They are reversed for native composition.
The first two lift directly from the source relations. The other seven must
still be proved in the original abstract group; finite permutation calculations
supply no such implication. A map onto the literal subgroup is defined only
after all nine equations are supplied.

Source and untrusted discovery: `source/README.md` and `source/Discover.g`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound
open Subgroup.CosetWordCertificate

/-- Candidate local relations; a separate theorem must lift them to the source group. -/
def localRelatorLetters : Fin 9 → Word (Fin 2) :=
  ![[(0, true), (0, true)],
    [(1, true), (1, true), (1, true), (1, true)],
    [(1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true)],
    [(0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false)],
    [(0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (1, false), (0, true), (1, false), (1, false), (0, true), (1, false), (0, true), (1, false), (1, false), (0, true), (1, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true)],
    [(0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (1, false), (0, true), (1, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true)],
    [(1, false), (1, false), (0, true), (1, false), (1, false), (0, true), (1, true), (0, true), (1, false), (1, false), (0, true), (1, false), (1, false), (0, true), (1, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (1, false), (0, true), (1, false), (0, true), (1, true), (1, true), (0, true)],
    [(0, true), (1, false), (0, true), (1, false), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (1, false), (0, true), (1, true), (0, true), (1, false), (1, false), (0, true), (1, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (1, true), (0, true), (1, true)],
    [(0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true)]]

def localRelator (i : Fin 9) : FreeGroup (Fin 2) := FreeGroup.mk (localRelatorLetters i)

abbrev LocalPresented := PresentedGroup (Set.range localRelator)

def localGenerator (i : Fin 2) : LocalPresented := PresentedGroup.of i

/-- These are defining equations of the smaller presentation only. -/
theorem local_generator_relations (i : Fin 9) :
    eval localGenerator (localRelatorLetters i) = 1 := by
  have hm : FreeGroup.lift localGenerator = PresentedGroup.mk (Set.range localRelator) := by
    apply FreeGroup.ext_hom
    intro i
    rfl
  change FreeGroup.lift localGenerator (localRelator i) = 1
  rw [hm]
  exact PresentedGroup.one_of_mem ⟨i, rfl⟩

/-- The marked map exists when the candidate words vanish in the source group. -/
def localHom (hrel : ∀ i, eval boundGenerator (localRelatorLetters i) = 1) :
    LocalPresented →* UniversalGroup :=
  PresentedGroup.toGroup (f := boundGenerator) (by
    rintro _ ⟨i, rfl⟩
    exact hrel i)

@[simp] theorem localHom_generator
    (hrel : ∀ i, eval boundGenerator (localRelatorLetters i) = 1) (s : Fin 2) :
    localHom hrel (localGenerator s) = boundGenerator s :=
  PresentedGroup.toGroup.of _

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

/-- Transfer both finiteness and the order bound to the literal source subgroup. -/
theorem boundSubgroup_finite_card_le_of_local
    (hrel : ∀ i, eval boundGenerator (localRelatorLetters i) = 1)
    (hlocal : Finite LocalPresented ∧ Nat.card LocalPresented ≤ 6072) :
    Finite boundSubgroup ∧ Nat.card boundSubgroup ≤ 6072 := by
  let := hlocal.1
  have hs := (localHom hrel).rangeRestrict_surjective
  have hf : Finite (localHom hrel).range := Finite.of_surjective _ hs
  have hc : Nat.card (localHom hrel).range ≤ Nat.card LocalPresented :=
    Nat.card_le_card_of_surjective _ hs
  rw [localHom_range] at hf hc
  exact ⟨hf, hc.trans hlocal.2⟩

/-- The first candidate relation is a consequence of the original square relation. -/
theorem localRelator_zero_holds : eval boundGenerator (localRelatorLetters 0) = 1 := by
  simpa [localRelatorLetters, eval_cons, pow_two] using boundGenerator_zero_sq

/-- The second candidate relation follows from the source commutator equation. -/
theorem localRelator_one_holds : eval boundGenerator (localRelatorLetters 1) = 1 := by
  simpa [localRelatorLetters, eval_cons, pow_succ, mul_assoc] using boundGenerator_one_pow_four

/-- The subgroup for the small, independent local coset enumeration. -/
def localCyclic : Subgroup LocalPresented := Subgroup.zpowers (localGenerator 1)

theorem localCyclic_bound : Finite localCyclic ∧ Nat.card localCyclic ≤ 4 := by
  have hp : localGenerator 1 ^ 4 = 1 := by
    simpa [localRelatorLetters, eval_cons, pow_succ, mul_assoc] using local_generator_relations 1
  have hx := isOfFinOrder_iff_pow_eq_one.mpr ⟨4, by decide, hp⟩
  refine ⟨hx.finite_zpowers.to_subtype, ?_⟩
  change Nat.card (Subgroup.zpowers (localGenerator 1)) ≤ 4
  rw [Nat.card_zpowers]
  exact orderOf_le_of_pow_eq_one (by decide) hp

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound
