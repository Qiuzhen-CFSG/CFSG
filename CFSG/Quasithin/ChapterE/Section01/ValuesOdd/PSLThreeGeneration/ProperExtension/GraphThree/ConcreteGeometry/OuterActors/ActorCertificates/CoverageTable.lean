module
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.OuterActors.Certificates

/-!
# Finite coverage of the whole outer actors

The 32-element multiplication table covers every outer four-group. Adjoining
one commuting involution gives one of two maximal elementary
eight-groups. Thus coverage requires only pairs and a single extension,
without searching the powerset of the Sylow group.

Source: Aschbacher–Smith E.1.14(7), printed p.214; Asc82a Lemma 4.11.
The rows were discovered by the supplied GAP diagnostic; all coverage facts
below are checked from the published faithful multiplication coordinates.
-/

public section
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.OuterActors.ActorCertificates
set_option maxRecDepth 10000

@[expose] def actor : Fin 15 → Finset Index :=
  ![{(0,false), (12,false), (7,true), (9,true)},
    {(0,false), (14,false), (5,true), (13,true)},
    {(0,false), (10,false), (1,true), (13,true)},
    {(0,false), (8,false), (3,true), (9,true)},
    {(0,false), (4,false), (0,true), (4,true)},
    {(0,false), (4,false), (2,true), (6,true)},
    {(0,false), (8,false), (7,true), (13,true)},
    {(0,false), (10,false), (5,true), (9,true)},
    {(0,false), (14,false), (1,true), (9,true)},
    {(0,false), (12,false), (3,true), (13,true)},
    {(0,false), (4,false), (9,true), (13,true)},
    {(0,false), (4,false), (3,true), (7,true)},
    {(0,false), (4,false), (1,true), (5,true)},
    {(0,false), (4,false), (8,false), (12,false), (3,true), (7,true), (9,true), (13,true)},
    {(0,false), (4,false), (10,false), (14,false), (1,true), (5,true), (9,true), (13,true)}]

@[expose] def four (i j : Index) : Finset Index :=
  {(0,false), i, j, multiply i j}

@[expose] def eight (n : Fin 15) (k : Index) : Finset Index :=
  actor n ∪ (actor n).image (multiply k)

@[expose] def involutive (i : Index) : Prop := multiply i i = (0,false)
@[expose] def commutes (i j : Index) : Prop := multiply i j = multiply j i

instance (i : Index) : Decidable (involutive i) := inferInstanceAs (Decidable (_ = _))
instance (i j : Index) : Decidable (commutes i j) := inferInstanceAs (Decidable (_ = _))

theorem four_table : ∀ i j : Index,
    i.2 = true → involutive i → involutive j → commutes i j →
    j ≠ (0,false) → j ≠ i → ∃ n : Fin 15, n.val < 13 ∧ actor n = four i j := by
  decide +kernel

@[expose] def maximal (m : Fin 15) : Prop := ∀ l : Index, involutive l →
  (∀ i ∈ actor m, commutes l i) → l ∈ actor m
instance (m : Fin 15) : Decidable (maximal m) :=
  inferInstanceAs (Decidable (∀ l : Index, involutive l →
    (∀ i ∈ actor m, commutes l i) → l ∈ actor m))

theorem eight_table : ∀ (n : Fin 15) (k : Index),
    n.val < 13 → involutive k → k ∉ actor n →
    (∀ i ∈ actor n, commutes k i) →
    ∃ m : Fin 15, 13 ≤ m.val ∧ actor m = eight n k ∧
      maximal m := by
  decide +kernel

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.OuterActors.ActorCertificates
