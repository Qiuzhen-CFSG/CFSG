module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At.Recognition
public import CFSG.Quasithin.Chapter14.Section08.SourceCases

/-!
# The order-32 application at the original nonabelian-recognition consumer

These theorems take exactly the counterexample, higher-rank hypothesis,
multiple-overgroup guard and flag used by `NonabelianRecognition`, in its
order-32 branch. They use Chapter 12 inputs only at the same G,T. The
large-core application has no recognition callback; the separate final
adapter retains genuine I.4.5 as an explicit input. Neither claims the
remaining HS/large-order branches or unconditional I.4.5.

Source: Aschbacher–Smith 14.4.3 and 14.4.14, pp.1007–1012.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section08.SourceCases
open ClassificationModels
open Chapter12.Section02 Chapter12.Section08
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Section04.CaseOneDimensionFour.At
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original nonabelian branch application when 27 divides the ambient order. -/
theorem orderThirtyTwo_of_cube_dvd
    (T : Sylow 2 G) (L V : Subgroup G)
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (hbig : 3 ^ 3 ∣ Nat.card G) :
    IsG2At G 3 ∨ Nonempty (G ≃* KnownSimple.SporadicName.hs.Carrier) := by
  exact Or.inl ⟨ZMod 3, inferInstance, inferInstance, Nat.card_zmod 3,
    source_recognition_of_cube_dvd d h structural alternatives F hne hZ hcard hbig⟩

/-- Application of genuine I.4.5 to the actual order-32 consumer.
The recognition premise retains its independent producer. -/
theorem orderThirtyTwo_of_i45
    (recognize : ∀ (X : Type u) [Group X] [Finite X],
      Nonempty (Section04.DimensionFour.G2ThreeConfiguration X) →
        Nonempty (X ≃* Atlas.G2.Model (ZMod 3)))
    (T : Sylow 2 G) (L V : Subgroup G)
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    IsG2At G 3 ∨ Nonempty (G ≃* KnownSimple.SporadicName.hs.Carrier) := by
  exact Or.inl ⟨ZMod 3, inferInstance, inferInstance, Nat.card_zmod 3,
    source_recognition_of_i45 d h structural alternatives F hne hZ hcard recognize⟩

end CFSG.Quasithin.Chapter14.Section08.SourceCases
