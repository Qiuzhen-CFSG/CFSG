module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.JankoTwoEndpointGenerators
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.JankoTwoTensorApplication

/-!
# Source endpoint words for the literal mixed tensor pair

The compatible reduced J₂ comparison supplies the DGS (15.3)(v),(vi)
generators in the original H/AT pair. Their commutator and central-core
placements use the unchanged original two-cores. The mixed word z^(dt)
is transported through the full reduced Borel, and adjoining all of BT
recovers both original endpoints.

Source: DGS, Groups and Graphs (1985), printed p.229. The genuine reduced
amalgam isomorphism remains explicit. This does not determine the outer
involution's action or prove the separate order-twelve product.
-/

public section
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Subgroup Theory.GroupTheory Chapter3.Section02 MixedZeroCore
open ChapterF.Source ChapterF.Source.DGS85.OriginalExtension ChapterF.GreenBook
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}

/-- Both source generating sets in H and AT, with all mixed-word overlap
placements and the original BT supplements. -/
theorem mixed_cubic_factor_endpoint_generators_of_reduced_j2
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B U : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hBA : B ≤ A) (hBK : B ≤ (pResidual 2 H).map H.subtype) (hB3 : Nat.card B = 3)
    (hU : CubicFactor T A B U) (hzero : pCore 2 (H ⊔ A : Subgroup G) = ⊥)
    (e : RankTwoAmalgam.Iso
      (reducedAmalgam ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G))
      HallJanko.j2Model.toMarking.amalgam) :
    ∃ k d z t q : G,
      k∈commonBorel ![(pResidual 2 H).map H.subtype,U]
        (twoCore (B ⊔ (T : Subgroup G) : Subgroup G)) ∧ orderOf k=3 ∧
      d∈parabolic ![(pResidual 2 H).map H.subtype,U]
        (twoCore (B ⊔ (T : Subgroup G) : Subgroup G)) 1 ∧ orderOf d=3 ∧
      z∈commonBorel ![(pResidual 2 H).map H.subtype,U]
        (twoCore (B ⊔ (T : Subgroup G) : Subgroup G)) ∧ orderOf z=2 ∧
      z∈twoCore (A ⊔ (T : Subgroup G) : Subgroup G) ∧
      (∀ a∈twoCore (A ⊔ (T : Subgroup G) : Subgroup G),z*a=a*z) ∧
      q∈commonBorel ![(pResidual 2 H).map H.subtype,U]
        (twoCore (B ⊔ (T : Subgroup G) : Subgroup G)) ∧ orderOf q=4 ∧
      q∈⁅twoCore H,zpowers k⁆ ∧
      t∈parabolic ![(pResidual 2 H).map H.subtype,U]
        (twoCore (B ⊔ (T : Subgroup G) : Subgroup G)) 0 ∧ t^2=1 ∧
      t∉B ⊔ (T : Subgroup G) ∧ t*k*t⁻¹=k⁻¹ ∧ d*k=k*d ∧
      d⁻¹*z*d∈commonBorel ![(pResidual 2 H).map H.subtype,U]
        (twoCore (B ⊔ (T : Subgroup G) : Subgroup G)) ∧
      (d*t)⁻¹*z*(d*t)∈commonBorel ![(pResidual 2 H).map H.subtype,U]
        (twoCore (B ⊔ (T : Subgroup G) : Subgroup G)) ∧
      d⁻¹*q*d∈commonBorel ![(pResidual 2 H).map H.subtype,U]
        (twoCore (B ⊔ (T : Subgroup G) : Subgroup G)) ∧
      closure (Set.range ![k,t,q,d⁻¹*q*d])=parabolic ![(pResidual 2 H).map H.subtype,U]
        (twoCore (B ⊔ (T : Subgroup G) : Subgroup G)) 0 ∧
      closure (Set.range ![k,d,z,(d*t)⁻¹*z*(d*t),q])=parabolic ![(pResidual 2 H).map H.subtype,U]
        (twoCore (B ⊔ (T : Subgroup G) : Subgroup G)) 1 ∧
      closure (Set.range ![k,t,q,d⁻¹*q*d]) ⊔ (B ⊔ (T : Subgroup G))=H ∧
      closure (Set.range ![k,d,z,(d*t)⁻¹*z*(d*t),q]) ⊔ (B ⊔ (T : Subgroup G))=A ⊔ (T : Subgroup G) := by
  obtain ⟨hf,_,_,_,hb,hp,hAT⟩ :=
    mixed_cubic_factor_rank_two hH eK A B U hAB hBA hBK hB3 hU hzero
  have hh := JankoTwo.GeneratorRelations.original_endpoint_generators hf 0 1 e
  rw [SuzukiContainment.reducedSylow,hb,hp,hAT] at hh
  exact hh

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
