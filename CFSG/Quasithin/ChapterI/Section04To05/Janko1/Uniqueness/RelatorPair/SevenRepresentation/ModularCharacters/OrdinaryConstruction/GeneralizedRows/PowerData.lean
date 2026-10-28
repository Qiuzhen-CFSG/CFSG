module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.OrdinaryConstruction.Contracts

/-!
# Compatible power labels for the ordinary J₁ rows

The cycles below specify the class of each nonnegative power, starting at
exponent zero. Fifth-root labels use the exponent orbits `{1,4}` and `{2,3}`;
nineteenth-root labels use the three orbits listed in `../../Source.md`.
The mixed-order cycles retain these fifth-root conventions: the square of
10A and the cube of 15A lie in 5B. In particular the order lists alone do
not determine this data.

`OrdinaryPowerLabels` is a group-theoretic intermediate contract. Its field
`powers` concerns actual conjugacy classes of powers of actual representatives;
it contains no character or representation assumption. Constructing this
contract from the source group hypotheses is a separate obligation.
Source: Janko, J. Algebra 3 (1966), 147–186, ordinary-character calculation;
Gorenstein, *Finite Groups*, §16.6, printed p.482.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters

/-- One complete period of the required power map for each class. -/
@[expose] public def ordinaryPowerCycle : Fin 15 → List (Fin 15) :=
  ![[0],
    [0, 1],
    [0, 2, 2],
    [0, 3, 4, 4, 3],
    [0, 4, 3, 3, 4],
    [0, 5, 2, 1, 2, 5],
    [0, 6, 6, 6, 6, 6, 6],
    [0, 7, 4, 8, 3, 1, 3, 8, 4, 7],
    [0, 8, 3, 7, 4, 1, 4, 7, 3, 8],
    [0, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9],
    [0, 10, 11, 4, 10, 2, 3, 11, 11, 3, 2, 10, 4, 11, 10],
    [0, 11, 10, 3, 11, 2, 4, 10, 10, 4, 2, 11, 3, 10, 11],
    [0, 12, 13, 13, 14, 13, 14, 12, 12, 14, 14, 12, 12, 14, 13, 14, 13, 13, 12],
    [0, 13, 14, 14, 12, 14, 12, 13, 13, 12, 12, 13, 13, 12, 14, 12, 14, 14, 13],
    [0, 14, 12, 12, 13, 12, 13, 14, 14, 13, 13, 14, 14, 13, 12, 13, 12, 12, 14]]

/-- The specified class label of the `n`-th power of a class-`j` element. -/
@[expose] public def ordinaryPowerClass (j : Fin 15) (n : ℕ) : Fin 15 :=
  (ordinaryPowerCycle j).getD (n % classOrder j) 0

public theorem ordinaryPowerCycle_length (j : Fin 15) :
    (ordinaryPowerCycle j).length = classOrder j := by
  revert j
  decide +kernel

public theorem ordinaryPowerClass_zero (j : Fin 15) : ordinaryPowerClass j 0 = 0 := by
  revert j
  decide +kernel

public theorem ordinaryPowerClass_one (j : Fin 15) : ordinaryPowerClass j 1 = j := by
  revert j
  decide +kernel

/-- Compatible class labels with the required actual power maps. -/
public structure OrdinaryPowerLabels {G : Type*} [Group G] [Finite G]
    (c : OrdinaryClassData G) where
  labels : Fin 15 ≃ Fin 15
  labels_zero : labels 0 = 0
  labels_orders : ∀ j, classOrder (labels j) = classOrder j
  labels_centralizers : ∀ j, centralizerOrder (labels j) = centralizerOrder j
  powers : ∀ (j : Fin 15) (n : ℕ),
    ConjClasses.mk (c.representatives (labels j) ^ n) =
      c.classes (labels (ordinaryPowerClass j n))

namespace OrdinaryPowerLabels
variable {G : Type*} [Group G] [Finite G] {c : OrdinaryClassData G}

/-- The compatible label of the actual conjugacy class of an element. -/
@[expose] public noncomputable def classIndex (p : OrdinaryPowerLabels c) (g : G) : Fin 15 :=
  p.labels.symm (c.classes.symm (ConjClasses.mk g))

/-- The literal numerical row on the actual source group. -/
@[expose] public noncomputable def row (p : OrdinaryPowerLabels c)
    (ζ₅ ζ₁₉ : ℂ) (i : Fin 15) : ClassFunction G :=
  fun g => ordinaryValue ζ₅ ζ₁₉ i (p.classIndex g)

public theorem row_isClassFunction (p : OrdinaryPowerLabels c)
    (ζ₅ ζ₁₉ : ℂ) (i : Fin 15) : IsClassFunction (p.row ζ₅ ζ₁₉ i) :=
  ofConjClassFunction_isClassFunction
    (fun d => ordinaryValue ζ₅ ζ₁₉ i (p.labels.symm (c.classes.symm d)))

public theorem classIndex_order (p : OrdinaryPowerLabels c) (g : G) :
    classOrder (p.classIndex g) = orderOf g := by
  rw [← p.labels_orders, ← c.orders]
  have hc : IsConj (c.representatives (p.labels (p.classIndex g))) g := by
    apply ConjClasses.mk_eq_mk_iff_isConj.mp
    rw [← c.classes_eq]
    simp [classIndex]
  obtain ⟨a, ha⟩ := hc
  exact SemiconjBy.orderOf_eq (a : G) ha

public theorem classIndex_one (p : OrdinaryPowerLabels c) : p.classIndex 1 = 0 := by
  have he : c.classes (p.labels 0) = ConjClasses.mk 1 := by
    rw [p.labels_zero, c.classes_eq, c.identity]
  simp [classIndex, ← he]

public theorem classIndex_involution (p : OrdinaryPowerLabels c) (g : G)
    (hg : orderOf g = 2) : p.classIndex g = 1 := by
  have ho := (p.classIndex_order g).trans hg
  generalize p.classIndex g = j at ho ⊢
  fin_cases j <;> simp_all [classOrder]

public theorem row_power (p : OrdinaryPowerLabels c) (ζ₅ ζ₁₉ : ℂ)
    (i j : Fin 15) (n : ℕ) :
    p.row ζ₅ ζ₁₉ i (c.representatives (p.labels j) ^ n) =
      ordinaryValue ζ₅ ζ₁₉ i (ordinaryPowerClass j n) := by
  simp [row, classIndex, p.powers]

end OrdinaryPowerLabels
end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters
