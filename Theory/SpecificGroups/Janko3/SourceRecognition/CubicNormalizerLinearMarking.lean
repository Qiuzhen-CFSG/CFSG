module
public import Theory.SpecificGroups.Janko3.SourceRecognition.CubicNormalizerThirdCoordinates
public import Theory.SpecificGroups.Janko3.SourceRecognition.CubicModelPairEquiv
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.Model.SingerPointEquiv
public import Theory.SpecificGroups.Alternating.CubicFiveThirty
public import Theory.SpecificGroups.GL2.FourCentralProduct

/-!
# The fixed full linear-to-cubic third-overlap marking

The Singer point identification and the fixed pair identification prescribe a
map on the actual order-thirty linear subgroup. Its central cubic maps into
the full cubic kernel, because the projective pair has order twenty.
Centralizing this nontrivial cubic forces its entire projective image into
the derived order-ten pair and hence the fixed A5. Thus the prescribed map
lands in the full third overlap. The proved order-thirty extension theorem
then supplies a unique marking of all GL2(4), retaining the cubic kernel.
No ambient source, subgroup alignment, or compatible-isomorphism assumption
is used in this construction.
-/

public noncomputable section
namespace Sporadic.Janko3.SourceRecognition.CubicNormalizerModel
open Subgroup
open Representation.CentralCubicNaturalFour
local notation "M16" => Theory.PSL2.BinaryFourFieldExtension.Model

/-- The actual Singer complement in the sixteen-field pair, using the fixed
point identification rather than an independently chosen pair marking. -/
@[expose] def singerPair : SingerField.normalizer →* Seventeen.ModelAmalgam.pair where
  toFun n := ⟨((Seventeen.ModelAmalgam.SingerPoint.complementEquiv n :
    Seventeen.ModelAmalgam.point) : M16),
    (Seventeen.ModelAmalgam.SingerPoint.complementEquiv n).property.2⟩
  map_one' := Subtype.ext (congrArg
    (fun c : Seventeen.ModelAmalgam.C => ((c : Seventeen.ModelAmalgam.point) : M16))
    Seventeen.ModelAmalgam.SingerPoint.complementEquiv.map_one)
  map_mul' n m := Subtype.ext (congrArg
    (fun c : Seventeen.ModelAmalgam.C => ((c : Seventeen.ModelAmalgam.point) : M16))
    (Seventeen.ModelAmalgam.SingerPoint.complementEquiv.map_mul n m))

/-- The pair inclusion is literally the fixed Singer point map on an actor. -/
theorem singerPair_coe (n : SingerField.normalizer) :
    (singerPair n : M16) =
      (Seventeen.ModelAmalgam.SingerPoint.pointEquiv (SemidirectProduct.inr n) : M16) := by
  rw [Seventeen.ModelAmalgam.SingerPoint.pointEquiv_inr]
  rfl

private theorem cube_right_eq_one (y : pair) (h3 : y^3=1) : y.val.right=1 := by
  let p : projectivePair := ⟨y.val.right,y.property⟩
  have hp3 : p^3=1 := by
    apply Subtype.ext
    have h3a : (y : Model)^3=1 := congrArg (fun z : pair => (z : Model)) h3
    have hh := congrArg projection h3a
    exact (show projection (y : Model)^3=1 by simpa only [map_pow,map_one] using hh)
  have hp20 : orderOf p ∣ 20 := by
    rw [←projectivePair_card]
    exact orderOf_dvd_natCard p
  have hp : p=1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp (by
    simpa using Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hp3) hp20))
  exact congrArg Subtype.val hp

private theorem third_mem_of_commute_cube (x y : pair) (h3 : y^3=1) (hne : y≠1)
    (hc : Commute x y) : (x : Model) ∈ thirdOverlap := by
  have hyr := cube_right_eq_one y h3
  have hy : (y : Model) = SemidirectProduct.inl y.val.left :=
    SemidirectProduct.ext rfl hyr
  have hyn : y.val.left ≠ 1 := by
    intro he
    apply hne
    apply Subtype.ext
    change (y : Model) = 1
    rw [hy,he,map_one]
  have hact : action x.val.right y.val.left = y.val.left := by
    have hh := congrArg (fun z : pair => (z : Model).left) hc.eq
    change x.val.left * action x.val.right y.val.left =
      y.val.left * action y.val.right x.val.left at hh
    rw [hyr,map_one,MulAut.one_apply,mul_comm y.val.left] at hh
    exact mul_left_cancel hh
  have hxD : x.val.right ∈ derived := by
    by_contra hnot
    have hi : action x.val.right = inversion := by rw [action_apply,if_neg hnot]
    rw [hi] at hact
    change y.val.left⁻¹ = y.val.left at hact
    have hz : ∀ z : Z, z⁻¹=z → z=1 := by decide +kernel
    exact hyn (hz _ hact)
  exact pairTen_le_thirdFive ⟨x.property,hxD⟩

private def pairMap : SingerField.normalizer →* pair :=
  modelPairEquiv.toMonoidHom.comp singerPair

private theorem pairMap_injective : Function.Injective pairMap := by
  intro x y he
  apply Seventeen.ModelAmalgam.SingerPoint.complementEquiv.injective
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : Seventeen.ModelAmalgam.pair => (z : M16)) (modelPairEquiv.injective he)

private theorem pairMap_mem (n : SingerField.normalizer) : (pairMap n : Model) ∈ thirdOverlap := by
  let u : Seventeen.Complement := (Multiplicative.ofAdd 1,1)
  let s : SingerField.normalizer := BaumeisterParabolics.complementEquiv u
  have hs3 : s^3=1 := by
    have hu : u^3=1 := by decide +kernel
    change (BaumeisterParabolics.complementEquiv u)^3=1
    rw [←map_pow,hu,map_one]
  have hsne : s≠1 := by
    intro he
    have hu : u≠1 := by decide +kernel
    exact hu (BaumeisterParabolics.complementEquiv.injective
      (he.trans (map_one _).symm))
  have hc : Commute n s := by
    obtain ⟨v,rfl⟩ := BaumeisterParabolics.complementEquiv.surjective n
    apply Commute.map
    exact (show Commute v u from Prod.ext (mul_comm _ _) (by simp [u]))
  apply third_mem_of_commute_cube (pairMap n) (pairMap s)
  · rw [←map_pow,hs3,map_one]
  · exact fun he => hsne (pairMap_injective (he.trans (map_one _).symm))
  · exact hc.map pairMap

private def thirdMap : SingerField.normalizer →* thirdOverlap :=
  (pair.subtype.comp pairMap).codRestrict thirdOverlap pairMap_mem

private theorem thirdMap_injective : Function.Injective thirdMap := by
  intro x y he
  apply pairMap_injective
  apply Subtype.ext
  have hh : (thirdMap x : Model) = (thirdMap y : Model) := congrArg Subtype.val he
  exact hh

private def linearMap : SingerField.normalizer →* LinearGroup :=
  SingerField.matrixEquiv.toMonoidHom.comp SingerField.normalizer.subtype

private theorem linearMap_injective : Function.Injective linearMap :=
  SingerField.matrixEquiv.injective.comp SingerField.normalizer.subtype_injective

/-- The canonical order-thirty marking extends to the entire linear group
and the full third overlap, with equality on every original Singer actor. -/
theorem exists_linear_third_equiv :
    ∃ e : LinearGroup ≃* thirdOverlap, ∀ n : SingerField.normalizer,
      (e (SingerField.matrixEquiv n.val) : Model) = (modelPairEquiv (singerPair n) : Model) := by
  let u := MonoidHom.ofInjective linearMap_injective
  let v := MonoidHom.ofInjective thirdMap_injective
  obtain ⟨e,he⟩ := alternatingGroup.FiveLocalGeometry.CubicThirty.marked_equiv_extends
    Representation.SL2FourNatural.SemilinearNormalizer.cubicFiveEquiv thirdCoordinates
    linearMap.range thirdMap.range
    ((Nat.card_congr u.toEquiv).symm.trans SingerField.normalizer_card)
    ((Nat.card_congr v.toEquiv).symm.trans SingerField.normalizer_card)
    (u.symm.trans v)
  refine ⟨e,?_⟩
  intro n
  have hh := he (u n)
  change e (linearMap n) = thirdMap (u.symm (u n)) at hh
  rw [u.symm_apply_apply] at hh
  exact congrArg Subtype.val hh

/-- A fixed whole-overlap marking determined by the two fixed pair maps. -/
@[expose] def linearThirdEquiv : LinearGroup ≃* thirdOverlap :=
  exists_linear_third_equiv.choose

/-- Exact prescribed restriction on the actual Singer linear complement. -/
theorem linearThirdEquiv_apply (n : SingerField.normalizer) :
    (linearThirdEquiv (SingerField.matrixEquiv n.val) : Model) =
      (modelPairEquiv (singerPair n) : Model) := exists_linear_third_equiv.choose_spec n

end Sporadic.Janko3.SourceRecognition.CubicNormalizerModel
