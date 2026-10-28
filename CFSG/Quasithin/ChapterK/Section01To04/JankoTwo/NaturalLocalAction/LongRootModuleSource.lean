module

public import Theory.Representation.G2NaturalLongRootFixer
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule
public import CFSG.Quasithin.ChapterK.Section01To04.JankoTwo.NaturalLocalAction.LongRootApplications

/-!
# Source long-root module facts for the J₂ rank-two exclusion

The fixed-codimension calculation and the full pointwise-fixer theorem give
both clauses of `B46LongRootModuleFacts` for the literal natural quotient.
Specializing to the marked four-element field discharges that input in the
existing rank-two exclusion, preserving the original carrier embedding and
its action. The separate root-fusion and centralizer clauses remain with
the B.4.6 root-facts producer.

Source: Aschbacher–Smith B.4.6(4) and K.4.5, printed pp.88 and 460.
-/

@[expose] public noncomputable section

open Atlas.G2 Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterK.JankoTwo.NaturalLocalAction
variable (K : Type*) [Field K] [CharP K 2] [Algebra (ZMod 2) K] [Finite K]

/-- The actual natural G₂ module satisfies both long-root clauses of B.4.6(4). -/
theorem b46LongRootModuleFacts : B46LongRootModuleFacts K := by
  let : Fintype K := Fintype.ofFinite K
  have hc : Nat.card K = 2 ^ Module.finrank (ZMod 2) K := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  constructor
  · intro g r hr
    change fixedCodim (NaturalOffenders.binaryNatural (F:=K)) _ = _
    rw [NaturalOffenders.natural_fixedCodim_eq]
    exact NaturalOffenders.fixedCodim_longRoot hc ⟨r,hr,g,rfl⟩
  · intro g r hr
    exact NaturalLongRootFixer.subspaceKernel_fixedSpace_longRoot g r hr

/-- The literal four-element field used in the J₂ marking has the required
pointwise-fixer theorem, with no representation-theoretic premise remaining. -/
theorem b46LongRootModuleFacts_four :
    B46LongRootModuleFacts Sporadic.LeechRelated.J2.G2FourModule.F :=
  b46LongRootModuleFacts _

end CFSG.Quasithin.ChapterK.JankoTwo.NaturalLocalAction

namespace CFSG.Quasithin.ChapterK.JankoTwo.MarkedModule
open NaturalLocalAction Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.GeneratorPair
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
  (D : MarkedModule (K := G2FourModule.F) ρ)

/-- The original rank-two J₂ exclusion with the universal natural-module
facts discharged. The earlier root-fusion and centralizer facts retain their
separate source producer. -/
theorem carrier_rank_two_exclusion_of_rootFacts
    (h : InvolutionImages.B46RootFacts G2FourModule.F)
    (A : Subgroup Carrier) (hA : rank A = 2) (hzA : FirstFusion.t ∈ A) :
    2 * rank A < fixedCodim D.carrierAction A :=
  D.carrier_rank_two_exclusion_of_B46 h b46LongRootModuleFacts_four A hA hzA
end CFSG.Quasithin.ChapterK.JankoTwo.MarkedModule
