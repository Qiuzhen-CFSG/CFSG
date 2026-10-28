module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.NormalizerEscapeCubicIndex
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.OddSmallSplitAction
public import Theory.Representation.FrattiniAction
public import Theory.GroupAction.QuinticFixedIndex

/-!
# The original cubic bound on the faithful Frattini representation

The actual quotient map Q to Q/Φ(Q) is equivariant for the same original
cubic complement. Passing to its original image in K/O₂(K) therefore
transfers the natural-core branch's index256 bound to fixed codimension
at most eight on the literal faithful binary Frattini representation.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L H P : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : NaturalData D} {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}

/-- The genuine natural-core branch bounds the original cubic on the
unchanged faithful containing-quotient representation. -/
theorem Data.collapsed_natural_core_cubicFrattini
    (h : Data D H) (f : LiftData s hz)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2)
    (hm : ⁅(localJoin T L).pCoreIn 2,localOrbit T L⁆ = D.fullModule) :
    let Q := (enlargedResidual T L H).pCoreIn 2
    letI : Fact (IsPGroup 2 Q) := ⟨isPGroup_pCoreIn 2 _⟩
    letI : IsElementaryAbelian 2 (CoreFrattiniSection T L H) := isElementaryAbelian_quotient_frattini
    let ρ := Representation.FrattiniAction.ofAutomorphismHom (h.coreQuotientFrattiniAction hn)
    Function.Injective ρ ∧
      Representation.BinaryOffender.fixedCodim ρ (quotientImage (enlargedResidual T L H) P) ≤ 8 := by
  let K := enlargedResidual T L H
  let Q := K.pCoreIn 2
  let W := CoreFrattiniSection T L H
  let : Fact (IsPGroup 2 Q) := ⟨isPGroup_pCoreIn 2 _⟩
  let : IsElementaryAbelian 2 W := isElementaryAbelian_quotient_frattini
  let b := h.coreQuotientFrattiniAction hn
  let ρ := Representation.FrattiniAction.ofAutomorphismHom b
  have hfρ : Function.Injective ρ := by
    intro x y he
    apply h.coreQuotientFrattiniAction_injective hn
    ext w
    exact Additive.ofMul.injective (DFunLike.congr_fun he (Additive.ofMul w))
  refine ⟨hfρ,?_⟩
  have hPK : P ≤ K := hi.complement_le.trans h.residual_le_enlargedResidual
  have hPQ : P ≤ normalizer (Q : Set G) := hPK.trans
    (K.le_normalizer.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  let C := quotientImage K P
  let r : P →* C := ((QuotientGroup.mk' (pCore 2 K)).subgroupMap (P.subgroupOf K)).comp
    (subgroupOfEquivOfLe hPK).symm.toMonoidHom
  have hr : Function.Surjective r :=
    ((QuotientGroup.mk' (pCore 2 K)).subgroupMap_surjective (P.subgroupOf K)).comp
      (subgroupOfEquivOfLe hPK).symm.surjective
  let τ := ρ.comp C.subtype
  let : MulDistribMulAction P Q := conjMulDistribMulActionOfLeNormalizer P Q hPQ
  have hsource : (FixedPoints.subgroup P Q).index ≤ 256 := by
    rw [fixedPoints_conjugation_eq_centralizer P Q hPQ]
    change (centralizer (P : Set G)).relIndex Q ≤ 256
    rw [←inf_relIndex_left]
    exact (h.collapsed_natural_core_cubic_index f hi hP hc hm).2
  let : MulDistribMulAction P (Multiplicative (Additive W)) :=
    Representation.BinaryFixedPoints.action (τ.comp r)
  let π : Q →* Multiplicative (Additive W) := {
    toFun q := Multiplicative.ofAdd (Additive.ofMul (QuotientGroup.mk' (frattini Q) q))
    map_one' := by exact map_one (QuotientGroup.mk' (frattini Q))
    map_mul' x y := (QuotientGroup.mk' (frattini Q)).map_mul x y }
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective (frattini Q)
  have heq (p : P) (q : Q) : π (p • q) = p • π q := by
    change QuotientGroup.mk' (frattini Q) (p • q) =
      b (QuotientGroup.mk' (pCore 2 K) ⟨p,hPK p.property⟩) (QuotientGroup.mk' (frattini Q) q)
    rw [h.coreQuotientFrattiniAction_mk,coreFrattiniAction_mk]
    rfl
  have hfixed : Representation.BinaryFixedPoints.fixedIndex (τ.comp r) ≤ 256 :=
    (fixedPoints_index_le_of_surjective_equivariant π hπ heq).trans hsource
  have hindex : Representation.BinaryFixedPoints.fixedIndex (τ.comp r) =
      Representation.BinaryFixedPoints.fixedIndex τ :=
    Representation.BinaryFixedPoints.fixedIndex_eq_of_equivariant τ r hr (MulEquiv.refl _)
      (by intros; rfl)
  rw [hindex,Representation.FrattiniAction.fixedIndex_eq_two_pow_fixedCodim ρ C] at hfixed
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hfixed

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
