module

public import Theory.Character.ModularBlock.SymmetricFourCartanData
public import Theory.Character.ModularBlock.BrauerCharacterQuadratic
public import Theory.Representation.SymmetricFourModular
public import Mathlib.RingTheory.SimpleModule.Rank

/-!
# The two characteristic-two simple modules of S₄

We construct the trivial module and the two-dimensional module obtained from
the linear parts of the affine permutations of the four-point plane over F₂.
Opposite shears prove the latter irreducible over the prescribed splitting
field. Its three-cycle characteristic polynomial is `X² + X + 1`; lifting the
two cube roots gives Brauer value `-1`. The identity value is its integer
dimension, and conjugacy handles every odd-order element.

The result inhabits `SimpleModuleData` without any assumption about ordinary
characters or block selectors. Completeness and independence are supplied by
`SymmetricFourCartanData`.
Source: Fong, *Some Sylow subgroups of order 32*, J. Algebra 6 (1967), p. 71.
-/

public section
noncomputable section

namespace ModularBlock.SymmetricFourCartan
open PrincipalBlockConstruction BrauerCoefficientExtension

private def trivialRep (d : PrincipalCongruenceBlockData Group) :
    Representation (splittingField d) Group (Fin 1 → splittingField d) :=
  Representation.trivial _ _ _

private theorem trivialRep_irreducible (d : PrincipalCongruenceBlockData Group) :
    Representation.IsIrreducible (trivialRep d) := by
  let : IsSimpleModule (splittingField d) (Fin 1 → splittingField d) :=
    isSimpleModule_iff_finrank_eq_one.mpr (by simp)
  let : IsSimpleOrder (Submodule (splittingField d) (Fin 1 → splittingField d)) :=
    (isSimpleModule_iff _ _).mp inferInstance
  refine { eq_bot_or_eq_top := ?_ }
  intro S
  rcases eq_bot_or_eq_top S.toSubmodule with h | h
  · exact Or.inl (Subrepresentation.toSubmodule_injective h)
  · exact Or.inr (Subrepresentation.toSubmodule_injective h)

private theorem trivialRep_value (d : PrincipalCongruenceBlockData Group) (g : Group) :
    BrauerCharacter.value d (trivialRep d) g = 1 := by
  have h : trivialRep d g = trivialRep d 1 := rfl
  have he : BrauerCharacter.value d (trivialRep d) g =
      BrauerCharacter.value d (trivialRep d) 1 := by
    simp only [BrauerCharacter.value, BrauerCharacter.integralValue, h]
  rw [he, BrauerCharacter.value_one]
  simp

open SymmetricFourConjugacy Polynomial
variable (d : PrincipalCongruenceBlockData Group)

private theorem degreeTwo_value
    (ρ : Representation (splittingField d) Group (Fin 2 → splittingField d))
    (hp : (ρ threeCycle).charpoly = X ^ 2 + X + 1)
    (g : Group) (hg : Odd (orderOf g)) :
    BrauerCharacter.value d ρ g = if g = 1 then 2 else -1 := by
  by_cases he : g = 1
  · subst g
    simp
  · rw [if_neg he]
    have hthree : BrauerCharacter.value d ρ threeCycle = -1 :=
      BrauerCharacter.value_eq_neg_one_of_charpoly d
        (by norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]) ρ threeCycle hp
    rcases eq_one_or_isConj_threeCycle g hg with h | hc
    · exact (he h).elim
    · obtain ⟨k, rfl⟩ := isConj_iff.mp hc
      rw [BrauerCharacter.value_conj, hthree]

/-- The actual trivial and degree-two simple modules, with their lifted Brauer values. -/
def simpleModuleData : SimpleModuleData d where
  rep := Fin.cases (trivialRep d)
    (Fin.cases (SymmetricFourModular.rep (splittingField d)) (fun i => i.elim0))
  irreducible j := by
    fin_cases j
    · exact trivialRep_irreducible d
    · exact SymmetricFourModular.irreducible (splittingField d)
  value_zero g _ := by
    change BrauerCharacter.value d (trivialRep d) g = 1
    exact trivialRep_value d g
  value_one g hg := by
    change BrauerCharacter.value d (SymmetricFourModular.rep (splittingField d)) g = _
    exact degreeTwo_value d (SymmetricFourModular.rep (splittingField d))
      (SymmetricFourModular.charpoly_threeCycle (splittingField d)) g hg

/-- Both characteristic-two S₄ simple modules exist over the datum's splitting field. -/
theorem nonempty_simpleModuleData : Nonempty (SimpleModuleData d) :=
  ⟨simpleModuleData d⟩

end ModularBlock.SymmetricFourCartan
