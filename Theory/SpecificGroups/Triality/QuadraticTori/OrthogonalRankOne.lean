module

public import Theory.SpecificGroups.Triality.QuadraticTori.OrthogonalRankOne.Factors
public import Theory.SpecificGroups.Triality.LeviIdentification
public import Theory.SpecificGroups.Triality.QuadraticTori.RankOneReduction

/-!
# An orthogonal SL₂(q³) × SL₂(q) in binary triality

The fixed three-arm diagonal and the base-field highest-root SL₂ give the
two actual factor maps. Transvection generation places each image in the
elementary subgroup; characteristic-two centerlessness preserves faithfulness
through the genuine central quotient. The factors commute, and any element
in their intersection pulls back to the center of the first SL₂. Thus
multiplication gives an injective product map, including q = 2, with no
simplicity or perfectness hypothesis.

The final application supplies this map to the published finite-field
construction, giving a faithful product of quadratic-extension norm-one
tori of order (q³+1)(q+1), with an ambient element inverting the first
factor and fixing the second. No embedding premise remains in that result.

Source: GLS3 §2.6, Proposition 2.6.2(a,b), and the extended D₄ root subsystem
consisting of the three arms and the highest root,
`refs/KGroup/GLS3/chapter2.tex`. The directness argument uses trivial SL₂
centers in characteristic two; 2.6.2(d) does not apply to this subsystem.
-/

@[expose] public section

open Matrix
open scoped MatrixGroups
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open Triality.Standard.Parabolics
open Triality.Standard.Parabolics.RankOneMatrices
open Triality.Standard.PositiveCoordinates
open Triality.Standard.PositiveCoordinates.SumExchangeData
namespace Triality.Standard.QuadraticTori.OrthogonalRankOne
noncomputable section
local instance : InvolutiveNeg (TypeDRootIndex 4) := (typeDRootPairing 2).indexNeg

/-- The three-arm diagonal, with codomain restricted to the graph-field fixed group. -/
def armsFixedMap (P : Parameters) (hp : P.prime = 2) :
    SL(2, ExtensionField P) →* fixedSubgroup P := by
  let := rankOneExtensionCharTwo P hp
  exact ((pinnedRankOneMaps P hp).armsFixedEmbedding (armRootCommutation P hp)).codRestrict
    (fixedSubgroup P) (fun g =>
      ((pinnedRankOneMaps P hp).range_armsFixedEmbedding (armRootCommutation P hp)).le
        ⟨g, rfl⟩ |>.2)

/-- The highest-root base-field factor in the graph-field fixed group. -/
def highestFixedMap (P : Parameters) (hp : P.prime = 2) :
    SL(2, GaloisField P.prime P.exponent) →* fixedSubgroup P :=
  (highestBaseEmbedding P hp).codRestrict (fixedSubgroup P)
    (highestBaseEmbedding_fixed P hp)

theorem armsFixedMap_injective (P : Parameters) (hp : P.prime = 2) :
    Function.Injective (armsFixedMap P hp) := by
  let := rankOneExtensionCharTwo P hp
  intro g h he
  exact (pinnedRankOneMaps P hp).armsFixedEmbedding_injective (armRootCommutation P hp)
    (congrArg Subtype.val he)

theorem highestFixedMap_injective (P : Parameters) (hp : P.prime = 2) :
    Function.Injective (highestFixedMap P hp) := by
  intro g h he
  exact highestBaseEmbedding_injective P hp (congrArg Subtype.val he)

/-- The cubic-field factor after elementary restriction and the genuine central quotient. -/
def armsCarrierEmbedding (P : Parameters) (hp : P.prime = 2) :
    SL(2, ExtensionField P) →* Carrier P := by
  let := rankOneExtensionCharTwo P hp
  exact (toCarrier P).comp (sl2ElementaryLift P hp (armsFixedMap P hp))

/-- The base-field highest-root factor after the same restriction and quotient. -/
def highestCarrierEmbedding (P : Parameters) (hp : P.prime = 2) :
    SL(2, GaloisField P.prime P.exponent) →* Carrier P := by
  let : CharP (GaloisField P.prime P.exponent) 2 := hp ▸ inferInstance
  exact (toCarrier P).comp (sl2ElementaryLift P hp (highestFixedMap P hp))

theorem armsCarrierEmbedding_injective (P : Parameters) (hp : P.prime = 2) :
    Function.Injective (armsCarrierEmbedding P hp) := by
  let := rankOneExtensionCharTwo P hp
  exact sl2_toCarrier_injective P hp _ (armsFixedMap_injective P hp)

theorem highestCarrierEmbedding_injective (P : Parameters) (hp : P.prime = 2) :
    Function.Injective (highestCarrierEmbedding P hp) := by
  let : CharP (GaloisField P.prime P.exponent) 2 := hp ▸ inferInstance
  exact sl2_toCarrier_injective P hp _ (highestFixedMap_injective P hp)

/-- Commutation survives elementary restriction and the central quotient. -/
theorem carrier_factors_commute (P : Parameters) (hp : P.prime = 2)
    (g : SL(2, ExtensionField P)) (h : SL(2, GaloisField P.prime P.exponent)) :
    Commute (armsCarrierEmbedding P hp g) (highestCarrierEmbedding P hp h) := by
  let := rankOneExtensionCharTwo P hp
  let : CharP (GaloisField P.prime P.exponent) 2 := hp ▸ inferInstance
  have he : Commute (sl2ElementaryLift P hp (armsFixedMap P hp) g)
      (sl2ElementaryLift P hp (highestFixedMap P hp) h) := by
    apply Subtype.ext
    apply Subtype.ext
    exact (arms_highest_commute P hp g h).eq
  exact he.map (toCarrier P)

private theorem coprod_injective_of_center_eq_bot {A B G : Type*}
    [Group A] [Group B] [Group G] (f : A →* G) (g : B →* G)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hA : Subgroup.center A = ⊥) (hc : ∀ a b, Commute (f a) (g b)) :
    Function.Injective (f.noncommCoprod g hc) := by
  apply (MonoidHom.noncommCoprod_injective f g hc).mpr
  refine ⟨hf, hg, ?_⟩
  rw [disjoint_iff_inf_le]
  rintro x ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
  have ha : a ∈ Subgroup.center A := by
    rw [Subgroup.mem_center_iff]
    intro c
    apply hf
    simp only [map_mul]
    rw [← hb]
    exact (hc c b).eq
  have ha1 : a = 1 := by simpa only [hA, Subgroup.mem_bot] using ha
  simp only [ha1, map_one, Subgroup.mem_bot]

/-- The orthogonal rank-one direct product in the actual triality carrier. -/
def productEmbedding (P : Parameters) (hp : P.prime = 2) :
    SL(2, ExtensionField P) × SL(2, GaloisField P.prime P.exponent) →* Carrier P :=
  (armsCarrierEmbedding P hp).noncommCoprod (highestCarrierEmbedding P hp)
    (carrier_factors_commute P hp)

/-- Centerlessness eliminates the intersection of the two faithful commuting factors. -/
theorem productEmbedding_injective (P : Parameters) (hp : P.prime = 2) :
    Function.Injective (productEmbedding P hp) := by
  let := rankOneExtensionCharTwo P hp
  exact coprod_injective_of_center_eq_bot _ _ (armsCarrierEmbedding_injective P hp)
    (highestCarrierEmbedding_injective P hp) (Theory.PSL2.sl2_center_eq_bot _) _

end
end Triality.Standard.QuadraticTori.OrthogonalRankOne

namespace Triality.Standard.QuadraticTori

/-- The actual SL₂(q³) × SL₂(q) subsystem of binary triality, including q = 2. -/
noncomputable def rankOneProductEmbedding (n : ℕ) (hn : 0 < n) :
    RankOneProduct n →* BinaryCarrier n hn :=
  OrthogonalRankOne.productEmbedding (binaryParameters n hn) rfl

theorem rankOneProductEmbedding_injective (n : ℕ) (hn : 0 < n) :
    Function.Injective (rankOneProductEmbedding n hn) :=
  OrthogonalRankOne.productEmbedding_injective (binaryParameters n hn) rfl

/-- The nonsplit norm-one product and its independent inverter, with the actual
orthogonal subsystem supplied and no remaining embedding hypothesis. -/
theorem exists_nonsplit_product (n : ℕ) (hn : 0 < n) :
    ∃ (ι : NonsplitLeft n × NonsplitRight n →* BinaryCarrier n hn)
      (w : BinaryCarrier n hn), Function.Injective ι ∧
      Nat.card ι.range = ((2 ^ n) ^ 3 + 1) * (2 ^ n + 1) ∧
      (∀ c, w * ι (c,1) * w⁻¹ = ι (c⁻¹,1)) ∧
      (∀ d, w * ι (1,d) * w⁻¹ = ι (1,d)) :=
  exists_nonsplit_product_of_rankOneProduct n hn (rankOneProductEmbedding n hn)
    (rankOneProductEmbedding_injective n hn)

end Triality.Standard.QuadraticTori
