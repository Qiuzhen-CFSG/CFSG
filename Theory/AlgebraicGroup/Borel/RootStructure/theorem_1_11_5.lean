module

public import Theory.AlgebraicGroup.Borel.RootStructure.theorem_1_11_4

/-!
This module isolates `theorem_1_11_5` from `Theory.AlgebraicGroup.Borel.RootStructure`.
It retains the declarations following that unresolved result up to the next
unresolved result, preserving the source order and public API of the GLS3
algebraic-group development. The normalizer/Weyl map is required to carry the
actual conjugation action on realized root subgroups; surjectivity and kernel
data alone do not determine this labeling.
-/

set_option warningAsError false

universe u v w

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem theorem_1_11_5
    {K : Variety k} [AlgebraicGroup K] (hK : IsReductiveAlgebraicGroup K)
    (T B U : ClosedSubgroup K) (D : RootGroupData K T)
    (positiveRoots : Set D.Root) (hB : IsBorelSubgroup B)
    (hT : IsMaximalTorus T) (hD : D.IsRealization)
    (hpositive : IsPositiveSystem D positiveRoots)
    (hUplus : U.toSubgroup = RootSubgroupGenerated D positiveRoots)
    {ι X Y : Type u} [Finite ι] [AddCommGroup X] [AddCommGroup Y]
    (P : RootPairing ι ℤ X Y) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (base : P.Base) (e : D.Root ≃ ι)
    (weightEquiv : Multiplicative X ≃* TorusWeight T)
    (hActual : IsActualBasedRootDatum D P base e weightEquiv positiveRoots)
    (weylMap : T.normalizer.toSubgroup →* P.weylGroup)
    (hweylSurj : Function.Surjective weylMap)
    (hweylKer : weylMap.ker = T.toSubgroup.comap T.normalizer.toSubgroup.subtype)
    (hweylAction : ∀ (m : T.normalizer.toSubgroup) (α : D.Root),
      (D.rootSubgroup α).conjugate ((m : Variety.Point K)⁻¹) =
        D.rootSubgroup
          (e.symm (P.weylGroupToPerm (weylMap m)⁻¹ (e α))))
    (w₀ : P.weylGroup) (hw₀ : MapsBaseToNegative base w₀) :
    (∀ (w : P.weylGroup) (m : T.normalizer.toSubgroup),
      normalizerWeylClass T P weylMap m = w₀ * w →
        (U.inter (U.conjugate ((m : Variety.Point K)⁻¹))).toSubgroup =
          RootSubgroupGenerated D (BruhatRootSet D positiveRoots P e w)) ∧
    (∀ g : Variety.Point K,
      ∃! f : BruhatNormalForm D positiveRoots U P e weylMap,
        g = f.u * (f.n : Variety.Point K) * f.v) := by sorry

end Theory.AlgebraicGroup
