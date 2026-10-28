module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.Source.ElementaryClosure
public import Theory.GroupTheory.CharacteristicCentralizerFusion
import all CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Branches
/-!
# Literal local models for the two small J₄ closure rows

A normal closure of order two contains the unique central Sylow involution.
Its actual normalizer is the involution centralizer, hence isomorphic to the
certified max2 word subgroup. For the order-four row, the checked plane
conjugator places its full normalizer inside the literal conjugate of max4.
These statements concern an arbitrary Sylow overgroup with the given closure;
no p=3 hypothesis or ambient maximality is assumed.

The internal import of `Branches` deliberately shares its central Sylow
conjugacy proof and centralizer comparison. The public statements retain only
actual subgroups and isomorphisms. Source: Aschbacher–Smith 1.3.4, p.511;
the lower matrix comparisons are the cited A.3.12 calculations.
-/

public section
open Subgroup
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover
open Janko4 Janko4.LocalStructure.SymmetricLinear
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Source
attribute [local irreducible] Janko4.modelGroup matrixA matrixB max4Subgroup

/-- The order-two closure has the actual max2 centralizer as its normalizer. -/
theorem normalizer_equiv_max2_of_closure_card_two
    (S : Sylow 2 Model) (H : Subgroup Model) (hSH : S.toSubgroup ≤ H)
    (hc : Nat.card (elementaryClosure S H hSH) = 2) :
    Nonempty (normalizer (elementaryClosure S H hSH : Set Model) ≃* sourceSubgroup) := by
  let E := centralClosure S H hSH
  have hE : Nat.card E = 2 :=
    (card_map_of_injective H.subtype_injective).symm.trans hc
  obtain ⟨z, hzne, _⟩ := (Nat.card_eq_two_iff' (1 : E)).mp hE
  let zm : H := z
  have hzm : zm ≠ 1 := fun hz => hzne (Subtype.ext hz)
  have hz : (zm : Model) ≠ 1 := fun hz => hzm (Subtype.ext hz)
  have hp : IsPGroup 2 E := IsPGroup.of_card (n := 1) (by simpa using hE)
  have hzS : (zm : Model) ∈ S := (hp.le_sylow_of_normal (S.subtype hSH)) z.property
  have hzc : zm ∈ center H := central_of_normal_card_two E hE z.property
  obtain ⟨g, hg⟩ := central_sylow_involution_conjugate S zm hzS
    (fun s hs => congrArg H.subtype (mem_center_iff.mp hzc ⟨s, hSH hs⟩)) hz
  have ho : orderOf (zm : Model) = 2 := by
    rw [← hg]
    exact (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
      Janko4.a).trans Janko4.orderOf_a
  have hEz : elementaryClosure S H hSH = zpowers (zm : Model) := by
    symm
    apply eq_of_le_of_card_ge (zpowers_le.mpr (mem_map_of_mem H.subtype z.property))
    rw [Nat.card_zpowers]
    change Nat.card (elementaryClosure S H hSH) ≤ orderOf (zm : Model)
    rw [hc, ho]
  have hC : (centralizer ({Janko4.a} : Set Model)).map (MulAut.conj g).toMonoidHom =
      centralizer ({(zm : Model)} : Set Model) := by
    apply le_antisymm
    · simpa only [Set.image_singleton, MulEquiv.coe_toMonoidHom, hg] using
        map_centralizer_le_centralizer_image ({Janko4.a} : Set Model)
          (MulAut.conj g).toMonoidHom
    · intro x hx
      refine ⟨(MulAut.conj g).symm x, mem_centralizer_singleton_iff.mpr ?_,
        (MulAut.conj g).apply_symm_apply x⟩
      apply (MulAut.conj g).injective
      simpa only [map_mul, MulEquiv.apply_symm_apply, hg] using
        mem_centralizer_singleton_iff.mp hx
  rw [hEz, normalizer_zpowers_eq_centralizer_of_order_two _ ho]
  exact ⟨(MulEquiv.subgroupCongr hC).symm.trans
    (((MulAut.conj g).subgroupMap (centralizer ({Janko4.a} : Set Model))).symm.trans
      sourceEquivCentralizer.symm)⟩

/-- The order-four row has its full normalizer in the certified max4 conjugate. -/
theorem candidate_two_normalizer_le_max4_conjugate :
    normalizer (KernelOrders.candidate 2 : Set Model) ≤
      max4Subgroup.map (MulAut.conj MatrixNormalizerBounds.ThirdConjugacy.conjugator).toMonoidHom := by
  rw [← KernelOrders.PureNormalizers.max4Plane_map_conjugator,
    ← map_equiv_normalizer_eq]
  exact map_mono (KernelOrders.PureNormalizers.max4Plane_normalizer_lt_of_marking
    MatrixNormalizerBounds.Max4EightCentralizer.marking).le

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Source
