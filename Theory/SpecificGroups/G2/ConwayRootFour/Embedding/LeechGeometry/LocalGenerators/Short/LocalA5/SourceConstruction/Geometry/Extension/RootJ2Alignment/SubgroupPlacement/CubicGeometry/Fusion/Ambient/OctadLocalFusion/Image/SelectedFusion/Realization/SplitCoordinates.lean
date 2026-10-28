module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.Realization.Transport
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.GeometryInterface
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.KernelModel
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.Counting
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.Extraspecial.SignAction
public import Mathlib.LinearAlgebra.Dual.Basis

/-!
# Split square coordinates on the actual octad central quotient

The shortened sign code restricts surjectively to the dual of the native
four-dimensional transvection axis. Its complementary word vanishes on that
axis, so the sign functional and the pointwise actor give a homomorphism from
the literal monomial kernel onto the direct sum of the axis and its dual.
The kernel of this map is central and has order two. The supplied extraspecial
hypothesis therefore identifies it with the actual center.

The semidirect-product square is the complementary word multiplied by the
functional evaluated on the actor's axis vector. Choosing a basis and its dual
turns this evaluation into exactly `ClassicalOrthogonal.formD 4 (ZMod 2)`.
Thus these coordinates preserve the square test, not just the quotient order.

Source: Aschbacher, *Sporadic Groups* (1994), 8.3, 25.1 and 46.1,
pp.23, 132–133 and 251. The sign-action bridge uses the existing native/ATLAS
Golay comparison; see `LICENSES/ATLAS.txt` and `LICENSES/ATLAS-CITATION.cff`.
-/

noncomputable section
open Atlas.Conway Atlas.Codes Atlas.Lattices
open MathieuCode.CocodeOctad.Dynamics
open scoped BigOperators
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction
namespace Realization
open KernelModel
namespace SplitCoordinates

abbrev AxisSpace := Axis nativeOctad
abbrev PairSpace := Module.Dual Bit AxisSpace × AxisSpace

def actorEquiv : pointwise ≃* Multiplicative AxisSpace :=
  nativeEquiv.symm.trans (octadTransvectionEquiv nativeOctad)

lemma axis_card : Nat.card AxisSpace = 16 := by
  rw [← Nat.card_congr (actorEquiv.toEquiv.trans Multiplicative.toAdd)]
  exact pointwise_card

lemma axis_finrank : Module.finrank Bit AxisSpace = 4 := by
  have h := axis_card
  rw [Module.natCard_eq_pow_finrank (K := Bit), show Nat.card Bit = 2 by simp [Bit]] at h
  change 2 ^ Module.finrank Bit AxisSpace = 2 ^ 4 at h
  exact Nat.pow_right_injective (by decide : 1 < 2) h

def axisBasis : Module.Basis (Fin 4) Bit AxisSpace :=
  Module.finBasisOfFinrankEq Bit AxisSpace axis_finrank

def signFunctional : signCode →ₗ[Bit] Module.Dual Bit AxisSpace :=
  (Axis nativeOctad).dualRestrict.comp signDual

lemma signFunctional_apply (c : signCode) (x : AxisSpace) :
    signFunctional c x = signDual c x.val := rfl

lemma signFunctional_surjective : Function.Surjective signFunctional :=
  (Subspace.dualRestrict_surjective (W := Axis nativeOctad)).comp signDual_surjective

lemma signFunctional_complement : signFunctional complementWord = 0 := by
  apply LinearMap.ext
  intro x
  rw [signFunctional_apply, signDual_complementWord, quotientParity_axis]
  rfl

lemma pointwise_inv (g : pointwise) : g⁻¹ = g :=
  inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using pointwise_sq g)

lemma sign_action (g : pointwise) (c : signCode) :
    signCodeEquiv g c = c + signFunctional c (actorEquiv g).toAdd • complementWord := by
  rw [signCodeEquiv_transvection, ← map_inv, pointwise_inv]
  rfl

lemma signFunctional_action (g : pointwise) (c : signCode) :
    signFunctional (signCodeEquiv g c) = signFunctional c := by
  rw [sign_action, map_add, map_smul, signFunctional_complement, smul_zero, add_zero]

def modelPair : KernelModel.Model →* Multiplicative PairSpace where
  toFun m := Multiplicative.ofAdd (signFunctional m.left.toAdd, (actorEquiv m.right).toAdd)
  map_one' := by
    apply Multiplicative.toAdd.injective
    apply Prod.ext
    · exact map_zero signFunctional
    · exact congrArg Multiplicative.toAdd (map_one actorEquiv)
  map_mul' m n := by
    apply Multiplicative.toAdd.injective
    apply Prod.ext
    · change signFunctional (m.left.toAdd + signCodeEquiv m.right n.left.toAdd) = _
      rw [map_add, signFunctional_action]
      rfl
    · exact congrArg Multiplicative.toAdd (map_mul actorEquiv m.right n.right)

lemma modelPair_surjective : Function.Surjective modelPair := by
  intro v
  obtain ⟨c, hc⟩ := signFunctional_surjective v.toAdd.1
  obtain ⟨g, hg⟩ := actorEquiv.surjective (Multiplicative.ofAdd v.toAdd.2)
  refine ⟨⟨Multiplicative.ofAdd c, g⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  exact Prod.ext hc (congrArg Multiplicative.toAdd hg)

lemma modelPair_ker_le_center : modelPair.ker ≤ Subgroup.center KernelModel.Model := by
  intro m hm
  have hf : signFunctional m.left.toAdd = 0 :=
    congrArg (fun v : Multiplicative PairSpace => v.toAdd.1) hm
  have hg : m.right = 1 := actorEquiv.injective
    ((congrArg (fun v : Multiplicative PairSpace => Multiplicative.ofAdd v.toAdd.2) hm).trans
      (map_one actorEquiv).symm)
  have hfix (g : pointwise) : signCodeEquiv g m.left.toAdd = m.left.toAdd := by
    rw [sign_action, hf, LinearMap.zero_apply, zero_smul, add_zero]
  rw [Subgroup.mem_center_iff]
  intro n
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    change n.left.toAdd + signCodeEquiv n.right m.left.toAdd =
      m.left.toAdd + signCodeEquiv m.right n.left.toAdd
    rw [hfix, hg]
    change n.left.toAdd + m.left.toAdd = m.left.toAdd + n.left.toAdd
    exact add_comm _ _
  · simp [hg]

lemma modelPair_square (m : KernelModel.Model) :
    (modelPair m).toAdd.1 (modelPair m).toAdd.2 = 0 ↔ m ^ 2 = 1 := by
  have hl : (m ^ 2).left.toAdd =
      signFunctional m.left.toAdd (actorEquiv m.right).toAdd • complementWord := by
    rw [pow_two]
    change m.left.toAdd + signCodeEquiv m.right m.left.toAdd = _
    rw [sign_action, ← add_assoc, signCode_add_self, zero_add]
  have hr : (m ^ 2).right = 1 := by
    change (SemidirectProduct.rightHom : KernelModel.Model →* pointwise) (m ^ 2) = 1
    rw [map_pow, pointwise_sq]
  change signFunctional m.left.toAdd (actorEquiv m.right).toAdd = 0 ↔ _
  constructor
  · intro h
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      rw [hl, h, zero_smul]
      rfl
    · exact hr
  · intro h
    have hz := congrArg (fun n : KernelModel.Model => n.left.toAdd) h
    rw [hl] at hz
    exact (smul_eq_zero.mp hz).resolve_right complementWord_ne_zero

lemma pair_card : Nat.card PairSpace = 256 := by
  have hd : Nat.card (Module.Dual Bit AxisSpace) = 16 := by
    rw [Module.natCard_eq_pow_finrank (K := Bit), Subspace.dual_finrank_eq, axis_finrank]
    simp [Bit]
  rw [Nat.card_prod, hd, axis_card]

def kernelPair : action.ker →* Multiplicative PairSpace :=
  modelPair.comp kernelEquiv.symm.toMonoidHom

lemma kernelPair_surjective : Function.Surjective kernelPair :=
  modelPair_surjective.comp kernelEquiv.symm.surjective

lemma kernelPair_ker_le_center : kernelPair.ker ≤ Subgroup.center action.ker := by
  intro k hk
  have hm : kernelEquiv.symm k ∈ Subgroup.center KernelModel.Model := modelPair_ker_le_center hk
  rw [Subgroup.mem_center_iff] at hm ⊢
  intro g
  apply kernelEquiv.symm.injective
  simpa only [map_mul] using hm (kernelEquiv.symm g)

lemma kernelPair_ker_card : Nat.card kernelPair.ker = 2 := by
  have hq : Nat.card (action.ker ⧸ kernelPair.ker) = 256 :=
    (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective kernelPair
      kernelPair_surjective).toEquiv).trans
      ((Nat.card_congr Multiplicative.toAdd).trans pair_card)
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup kernelPair.ker
  rw [kernel_card_512, hq] at hc
  omega

lemma kernelPair_ker_eq_center (hExtra : IsExtraspecial 2 action.ker) :
    kernelPair.ker = Subgroup.center action.ker := by
  apply Subgroup.eq_of_le_of_card_ge kernelPair_ker_le_center
  rw [kernelPair_ker_card, hExtra.center_order_p]

/-- The actual central quotient is the direct sum of the axis and its dual. -/
def quotientPair (hExtra : IsExtraspecial 2 action.ker) :
    KernelCentralQuotient ≃* Multiplicative PairSpace :=
  (QuotientGroup.quotientMulEquivOfEq (kernelPair_ker_eq_center hExtra).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective kernelPair kernelPair_surjective)

lemma quotientPair_mk (hExtra : IsExtraspecial 2 action.ker) (k : action.ker) :
    quotientPair hExtra (QuotientGroup.mk' (Subgroup.center action.ker) k) = kernelPair k := rfl

/-- Dual coordinates put evaluation into the specified ordered split form. -/
def pairCoordinates : PairSpace ≃ₗ[Bit] SelectedGeometry.Space :=
  (axisBasis.dualBasis.equivFun.prodCongr axisBasis.equivFun).trans
    (LinearEquiv.sumArrowLequivProdArrow (Fin 4) (Fin 4) Bit Bit).symm

lemma pairCoordinates_form (v : PairSpace) :
    SelectedGeometry.form (pairCoordinates v) = v.1 v.2 := by
  rw [ClassicalOrthogonal.formD_apply]
  change (∑ i : Fin 4, axisBasis.dualBasis.equivFun v.1 i * axisBasis.equivFun v.2 i) = _
  simp only [Module.Basis.dualBasis_equivFun]
  conv_rhs => rw [← axisBasis.sum_equivFun v.2, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, smul_eq_mul, mul_comm]

end SplitCoordinates

/-- Square-compatible split coordinates on the literal octad central quotient. -/
public noncomputable def squareCoordinates (hExtra : IsExtraspecial 2 action.ker) : SquareCoordinates where
  coordinates := (SplitCoordinates.quotientPair hExtra).trans
    SplitCoordinates.pairCoordinates.toAddEquiv.toMultiplicative
  square_zero_iff k := by
    change SelectedGeometry.form (SplitCoordinates.pairCoordinates
      ((SplitCoordinates.quotientPair hExtra)
        (QuotientGroup.mk' (Subgroup.center action.ker) k)).toAdd) = 0 ↔ k ^ 2 = 1
    rw [SplitCoordinates.quotientPair_mk, SplitCoordinates.pairCoordinates_form]
    change (SplitCoordinates.modelPair (kernelEquiv.symm k)).toAdd.1
      (SplitCoordinates.modelPair (kernelEquiv.symm k)).toAdd.2 = 0 ↔ _
    rw [SplitCoordinates.modelPair_square]
    rw [← map_pow, ← kernelEquiv.symm.map_one, kernelEquiv.symm.injective.eq_iff]

/-- The actual octad kernel admits hyperbolic coordinates compatible with every square. -/
public theorem nonempty_squareCoordinates (hExtra : IsExtraspecial 2 action.ker) :
    Nonempty SquareCoordinates :=
  ⟨squareCoordinates hExtra⟩

end Realization
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction
end
