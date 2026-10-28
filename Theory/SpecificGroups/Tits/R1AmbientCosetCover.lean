module

public import Theory.SpecificGroups.Tits.PresentationCosetBounds
public import Theory.GroupTheory.CosetEnumeration
public import Theory.SpecificGroups.Tits.R1Certificate.Verified

/-!
# The ambient 1755-coset cover by Parrott's R₁ subgroup

This preserves the original ambient cover assembly. The distinct 1024-coset
cover of the local presentation by `⟨r1,s1⟩` is in `R1CosetCover`.

A complete signed table with inverse columns gives generator permutations.
Each positive table edge must additionally be proved as an equation of right
cosets in the presented group. The assembly below separates these obligations:
the inverse-table check alone does not imply coverage.

The checked certificate is the Todd–Coxeter enumeration for the nine-generator
subgroup R₁ in Parrott (1972), §5, p. 683. The immutable representatives and
inference rules are interpreted by `CosetEnumeration`.
-/

namespace Tits

open Theory.GroupTheory Theory.GroupTheory.CosetEnumeration

/-- Assemble a cover from genuine certified edges and a complete inverse table. -/
public def parrottR1CosetCoverOfCertifiedTable
    (input : Input ParrottGenerator)
    (model : Models parrottGenerator parrottR1Subgroup input)
    (index : Fin 1755 → Nat) (initial : Fin 1755) (hzero : index initial = 0)
    (table : Fin 1755 → Letter ParrottGenerator → Fin 1755)
    (inverseTable : ∀ i a, table (table i a) (flip a) = i)
    (edges : ∀ i a,
      (CosetEnumeration.Fact.mk (index i) [(a, true)] (index (table i (a, true)))).Valid
        parrottGenerator parrottR1Subgroup input) : ParrottR1CosetCover where
  rep i := representative parrottGenerator input (index i)
  initial := initial
  initial_eq := by simp [representative, hzero, model.zero]
  step a := tablePermutation table inverseTable (a, true)
  transition i a := by
    simpa only [CosetEnumeration.Fact.Valid, Related, eval_singleton, letterValue, ↓reduceIte,
      tablePermutation, Equiv.coe_fn_mk] using edges i a

/-- The checked 1755-representative cover for Parrott's nine-generator subgroup.
Every transition follows from the certified coset-enumeration derivation in the
actual presentation, including its coincidences and transferred edges. -/
public noncomputable def parrottAmbientR1CosetCover : ParrottR1CosetCover :=
  parrottR1CosetCoverOfCertifiedTable R1Certificate.input R1Certificate.model
    R1Certificate.index R1Certificate.initial R1Certificate.initial_index
    R1Certificate.table R1Certificate.inverse_table R1Certificate.edges

/-- Parrott's presentation admits the certified cover without any finiteness
assumption on the subgroup. -/
public theorem nonempty_parrottR1CosetCover : Nonempty ParrottR1CosetCover :=
  ⟨parrottAmbientR1CosetCover⟩

end Tits
