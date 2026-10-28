module

public import Theory.AlgebraicGroup.Borel.RootStructure.theorem_1_12_4
public import Theory.AlgebraicGroup.Borel.RootStructure.FundamentalCorootCharacterCriterion

/-!
This module isolates `theorem_1_12_5` from `Theory.AlgebraicGroup.Borel.RootStructure`.
It retains the declarations following that unresolved result up to the next
unresolved result.  For part (b), GLS3 Theorems 1.9.5(d) and 1.12.1 use the
algebraic root cocharacters attached to a genuine simple-root base.  The
`IsAlgebraicFundamentalCorootData` hypothesis records exactly that input: its
point formula identifies `C.h` with those cocharacters, while its pairing and
simple-root specifications identify the based root datum.  This excludes the
arbitrary surjective reparametrizations allowed by raw `ChevalleyData` and
supports constructing the product morphism with the stated point formula.
-/

set_option warningAsError false

universe u v w

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem theorem_1_12_5
    {K : Variety k} [AlgebraicGroup K] (hK : IsSemisimpleAlgebraicGroup K)
    (T : ClosedSubgroup K) (D : RootGroupData K T) (C : ChevalleyData K D)
    [Fintype D.simple]
    (hT : IsMaximalTorus T) (hD : D.IsRealization)
    (hTGenerated :
      T.toSubgroup = Subgroup.closure {g | ∃ α t, g = C.h α t})
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced] (e : D.Root ≃ ι)
    (base : P.Base) (hCoroot : IsAlgebraicFundamentalCorootData C P e base) :
    (IsAdjointVersion K → Subgroup.center (Variety.Point K) = ⊥) ∧
    Finite (Subgroup.center (Variety.Point K)) ∧
    (∃ order : List D.Root, EnumeratesRootSet D.simple order ∧
      ∃ φ : FundamentalCorootMorphism C order,
        (IsUniversalVersion K ↔
          ∃ iso : AlgebraicGroup.Iso (dVariety k order.length)
              T.carrierVariety,
            iso.hom = φ.map)) ∧
    Nonempty
      (Subgroup.center (Variety.Point K) ≃*
        ((TorusWeight T ⧸ TorusRootLattice T) →* kˣ)) ∧
    (IsSimpleAlgebraicGroup K →
      ∀ classification, HasRootSystemType K classification →
        IsValidGeneratorTableClassification classification →
        (IsUniversalVersion K →
          HasCenterShape (K := K) (universalCenterShape classification)) ∧
        IsCenterHomomorphicImageOfShape (K := K)
          (universalCenterShape classification)) := by sorry

end Theory.AlgebraicGroup
