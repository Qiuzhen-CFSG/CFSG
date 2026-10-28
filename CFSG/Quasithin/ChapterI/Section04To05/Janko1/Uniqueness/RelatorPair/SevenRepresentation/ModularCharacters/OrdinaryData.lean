module

public import Theory.Character.ConjClassFunction
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# The ordinary character table needed before the eleven-block calculation

This module specifies the ordinary table on actual conjugacy classes of the
source group. Existence of this data is a separate theorem, still to be proved
from the local J₁ hypotheses. It is not inferred from the concrete matrix model.

The numerical table is the ATLAS table, with the ordering recorded in GAP
CTblLib 1.3.11, `data/ctoconja.tbl`, entry `J1` (Thomas Breuer,
GPL-3.0-or-later). Fifth- and nineteenth-root periods are written explicitly;
the two indicated Galois conjugations are expanded. See `Source.md` here for
the provenance and the distinction between this specification and its proof.
The source argument is Janko, J. Algebra 3 (1966), 147–186, summarized in
Gorenstein, *Finite Groups*, §16.6, p.482.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters

/-- Degrees, in the ordinary ATLAS row order. -/
@[expose] public def ordinaryDegree : Fin 15 → ℕ :=
  ![1, 56, 56, 76, 76, 77, 77, 77, 120, 120, 120, 133, 133, 133, 209]

/-- Element orders, in the ordinary ATLAS column order. -/
@[expose] public def classOrder : Fin 15 → ℕ :=
  ![1, 2, 3, 5, 5, 6, 7, 10, 10, 11, 15, 15, 19, 19, 19]

/-- Centralizer orders for those columns. -/
@[expose] public def centralizerOrder : Fin 15 → ℕ :=
  ![175560, 120, 30, 30, 30, 6, 7, 10, 10, 11, 15, 15, 19, 19, 19]

/-- The literal ordinary table, parametrized by compatible primitive roots. -/
@[expose] public noncomputable def ordinaryValue (ζ₅ ζ₁₉ : ℂ) : Fin 15 → Fin 15 → ℂ :=
  let a := ζ₅ + ζ₅ ^ 4
  let b := ζ₅ ^ 2 + ζ₅ ^ 3
  let c := ζ₁₉ + ζ₁₉ ^ 7 + ζ₁₉ ^ 8 + ζ₁₉ ^ 11 + ζ₁₉ ^ 12 + ζ₁₉ ^ 18
  let d := ζ₁₉ ^ 2 + ζ₁₉ ^ 3 + ζ₁₉ ^ 5 + ζ₁₉ ^ 14 + ζ₁₉ ^ 16 + ζ₁₉ ^ 17
  let e := ζ₁₉ ^ 4 + ζ₁₉ ^ 6 + ζ₁₉ ^ 9 + ζ₁₉ ^ 10 + ζ₁₉ ^ 13 + ζ₁₉ ^ 15
  ![![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![56, 0, 2, -2*a, -2*b, 0, 0, 0, 0, 1, a, b, -1, -1, -1],
    ![56, 0, 2, -2*b, -2*a, 0, 0, 0, 0, 1, b, a, -1, -1, -1],
    ![76, 4, 1, 1, 1, 1, -1, -1, -1, -1, 1, 1, 0, 0, 0],
    ![76, -4, 1, 1, 1, -1, -1, 1, 1, -1, 1, 1, 0, 0, 0],
    ![77, 5, -1, 2, 2, -1, 0, 0, 0, 0, -1, -1, 1, 1, 1],
    ![77, -3, 2, a, b, 0, 0, a, b, 0, a, b, 1, 1, 1],
    ![77, -3, 2, b, a, 0, 0, b, a, 0, b, a, 1, 1, 1],
    ![120, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, c, d, e],
    ![120, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, e, c, d],
    ![120, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, d, e, c],
    ![133, 5, 1, -2, -2, -1, 0, 0, 0, 1, 1, 1, 0, 0, 0],
    ![133, -3, -2, -a, -b, 0, 0, a, b, 1, -a, -b, 0, 0, 0],
    ![133, -3, -2, -b, -a, 0, 0, b, a, 1, -b, -a, 0, 0, 0],
    ![209, 1, -1, -1, -1, 1, -1, 1, 1, 0, -1, -1, 0, 0, 0]]

/-- A complete table of genuine ordinary irreducibles of the arbitrary group.
No modular representation or group recognition is part of this contract. -/
public structure OrdinaryData (G : Type*) [Group G] [Finite G] where
  representatives : Fin 15 → G
  classes : Fin 15 ≃ ConjClasses G
  classes_eq : ∀ i, classes i = ConjClasses.mk (representatives i)
  identity : representatives 0 = 1
  orders : ∀ i, orderOf (representatives i) = classOrder i
  centralizers : ∀ i,
    Nat.card (Subgroup.centralizer ({representatives i} : Set G)) = centralizerOrder i
  chi : Fin 15 → ConjClassFunction G
  complete : IsCompleteIrreducibleCharacterFamily chi
  rootFive : ℂ
  rootFive_primitive : IsPrimitiveRoot rootFive 5
  rootNineteen : ℂ
  rootNineteen_primitive : IsPrimitiveRoot rootNineteen 19
  values : ∀ i j, chi i (classes j) = ordinaryValue rootFive rootNineteen i j

/-- The table specification gives the ordinary degrees at the actual identity. -/
public theorem OrdinaryData.degree_value {G : Type*} [Group G] [Finite G]
    (d : OrdinaryData G) (i : Fin 15) :
    d.chi i (ConjClasses.mk 1) = (ordinaryDegree i : ℂ) := by
  have h := d.values i 0
  rw [d.classes_eq, d.identity] at h
  rw [h]
  fin_cases i <;> simp [ordinaryValue, ordinaryDegree]

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters
