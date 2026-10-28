module

public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.CartanRankOne
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoOne
public import Theory.SpecificGroups.Janko1.Model.Certification
public import Theory.GroupAction.InnerInvolutionGeometry

/-!
# The J₁ rank-one Cartan container

The certified matrix automorphism theorem proves that the actual outer
group of J₁ is trivial. Together with the checked simple perfect model,
this supplies the center and outer-group inputs to the rank-one Cartan
argument. Both consumers retain the original H-star residual and the
literal tensor line; the second feeds the new overgroup component product.

This uses the proved generator-image and involution-orbit certificates,
not the conditional innerness input to the involutory two-component API.
Source: Aschbacher–Smith 9.3.1, printed p.732; GLS3, Table 5.3f.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

private theorem janko_center_outer_of_equiv
    {X : Type*} [Group X] (eX : X ≃* Janko1.Model) :
    center X = ⊥ ∧ IsPGroup 2 (MulAut.Outer X) := by
  have hz : center Janko1.Model = ⊥ := center_eq_bot_of_simple_perfect
  constructor
  · apply eq_bot_iff.mpr
    intro z hz'
    have hez : eX z ∈ center Janko1.Model := (centerCongr eX ⟨z,hz'⟩).property
    rw [hz,mem_bot] at hez
    exact eX.injective (hez.trans eX.map_one.symm)
  · let : Subsingleton (MulAut.Outer Janko1.Model) := Janko1.OuterCertificate.outer_subsingleton
    have ho : IsPGroup 2 (MulAut.Outer Janko1.Model) := fun x =>
      ⟨0,by simpa only [pow_zero,pow_one] using (Subsingleton.elim x 1)⟩
    exact ho.of_equiv (MulAut.outerCongr eX).symm

/-- The actual J₁ quotient discharges the automorphism inputs to source 9.3.1. -/
theorem cartan_jankoOne_normalizes_and_centralizes_tensorLine
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B J : Subgroup G) [IsElementaryAbelian 3 A]
    (hJU : J ≤ normalizer (m.tensorLine : Set G))
    (hJ : (J.subgroupOf (normalizer (m.tensorLine : Set G))).IsCComponent)
    (hKJ : (pResidual 2 H).map H.subtype ≤ J)
    (hBA : B ≤ A) (hBK : B ≤ (pResidual 2 H).map H.subtype) (hB : Nat.card B = 3)
    (hAU : A ≤ normalizer (m.tensorLine : Set G)) (hr : primeRank 3 J ≤ 1)
    (eJ : (J ⧸ pCore 2 J) ≃* Janko1.Model)
    (d : G) (hdA : d ∈ A) (hd3 : d ^ 3 = 1)
    (hdC : d ∉ centralizer (m.tensorLine : Set G)) :
    A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G) ∧
      (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G) := by
  obtain ⟨hz,hout⟩ := janko_center_outer_of_equiv eJ
  exact m.cartan_rank_one_normalizes_and_centralizes_tensorLine hH eK A B J
    hJU hJ hKJ hBA hBK hB hAU hr hz hout d hdA hd3 hdC

/-- The J₁ row applied to the original new overgroup and its two-residual. -/
theorem cartan_jankoOne_tensor_pair_component_product
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B J : Subgroup G) [IsElementaryAbelian 3 A]
    (hJU : J ≤ normalizer (m.tensorLine : Set G))
    (hJ : (J.subgroupOf (normalizer (m.tensorLine : Set G))).IsCComponent)
    (hKJ : (pResidual 2 H).map H.subtype ≤ J)
    (hBA : B ≤ A) (hBK : B ≤ (pResidual 2 H).map H.subtype) (hB : Nat.card B = 3)
    (hAU : A ≤ normalizer (m.tensorLine : Set G)) (hr : primeRank 3 J ≤ 1)
    (eJ : (J ⧸ pCore 2 J) ≃* Janko1.Model)
    (d : G) (hdA : d ∈ A) (hd3 : d ^ 3 = 1)
    (hdC : d ∉ centralizer (m.tensorLine : Set G))
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G))
      ((pResidual 2 H).map H.subtype ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))))
    (E : Subgroup G) (hcore : pCore 2 E ≠ ⊥)
    (hgen : E = (L ⊔ (pResidual 2 H).map H.subtype) ⊔
      ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (hmove : ¬ (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorPlane : Set G)) :
    (pResidual 2 E).IsCComponent ∧
      L.subgroupOf E ≤ pResidual 2 E ∧
      ((pResidual 2 H).map H.subtype).subgroupOf E ≤ pResidual 2 E ∧
      ∀ g : E, ∃ k ∈ pResidual 2 E,
        ∃ r ∈ (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf E), k * r = g := by
  obtain ⟨hz,hout⟩ := janko_center_outer_of_equiv eJ
  exact m.cartan_rank_one_tensor_pair_component_product hn hH eK A B J
    hJU hJ hKJ hBA hBK hB hAU hr hz hout d hdA hd3 hdC hSyl E hcore hgen hmove

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
