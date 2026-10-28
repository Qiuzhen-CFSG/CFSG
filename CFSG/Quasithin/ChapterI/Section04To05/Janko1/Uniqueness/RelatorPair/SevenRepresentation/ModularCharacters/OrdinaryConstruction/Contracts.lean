module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.OrdinaryData

/-!
# Separate class enumeration and generalized-character construction

The ordinary table is constructed in two independent stages. The first lists
actual conjugacy classes with their element and centralizer orders. Given such
a list, the second must realize the numerical rows as differences of genuine
complex representation characters. Norm one and positive degree then turn
these differences into irreducibles in `OrdinaryConstruction`.

Equal element orders alone do not fix the compatible labels of the two classes
of each of orders 5, 10, 15, or the three classes of order 19. The generalized-
character stage can therefore permute columns while preserving both order
lists and the identity. This avoids imposing an unjustified power-map choice
on the class-enumeration theorem.

These are intermediate contracts, not assertions of their existence. Source:
Janko, J. Algebra 3 (1966), 147–186; Gorenstein, *Finite Groups*, §16.6,
printed p.482. Numerical conventions and licensing are in `../Source.md`.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters

/-- The group-theoretic column calculation, without any character assumptions. -/
public structure OrdinaryClassData (G : Type*) [Group G] [Finite G] where
  representatives : Fin 15 → G
  classes : Fin 15 ≃ ConjClasses G
  classes_eq : ∀ i, classes i = ConjClasses.mk (representatives i)
  identity : representatives 0 = 1
  orders : ∀ i, orderOf (representatives i) = classOrder i
  centralizers : ∀ i,
    Nat.card (Subgroup.centralizer ({representatives i} : Set G)) = centralizerOrder i

/-- Compatible labels and genuine generalized characters on the given classes.
`generalized` requires differences of actual representation characters of G;
cyclotomic integrality and numerical orthogonality do not supply it. -/
public structure OrdinaryGeneralizedRows {G : Type*} [Group G] [Finite G]
    (c : OrdinaryClassData G) where
  labels : Fin 15 ≃ Fin 15
  labels_zero : labels 0 = 0
  labels_orders : ∀ j, classOrder (labels j) = classOrder j
  labels_centralizers : ∀ j, centralizerOrder (labels j) = centralizerOrder j
  rootFive : ℂ
  rootFive_primitive : IsPrimitiveRoot rootFive 5
  rootNineteen : ℂ
  rootNineteen_primitive : IsPrimitiveRoot rootNineteen 19
  generalized : ∀ i, IsGeneralizedCharacter (fun g : G =>
    ordinaryValue rootFive rootNineteen i (labels.symm (c.classes.symm (ConjClasses.mk g))))

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters
