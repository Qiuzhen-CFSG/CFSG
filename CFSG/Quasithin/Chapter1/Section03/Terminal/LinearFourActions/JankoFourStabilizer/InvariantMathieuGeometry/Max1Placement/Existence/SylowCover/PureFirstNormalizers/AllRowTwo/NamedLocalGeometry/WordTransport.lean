module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.FiniteConfigurations.Data

/-!
# Native word transport for the finite pure-first configurations

Iterating the certified thirteen-bit action transports every literal kernel
word through an actual word in the original max2 generators. The central
correction is retained at each step. This is used by the named-local
placement certificates, without assuming any normalizer-cover theorem.

Source: Kleidman--Wilson (1988), Section 2.1, pp.488--489, and the native
ATLAS max2 words attributed in the imported action certificates.
-/

@[expose] public noncomputable section
open Subgroup
namespace Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.NamedLocalGeometry
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound NormalClosureControl
open FiniteConfigurations
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer.PairOrbitData
attribute [local irreducible] modelGroup matrixA matrixB

/-- An actual word in the original max2 generators. -/
def actorWord (w : List Bool) : sourceSubgroup := (w.map sourceGenerator).prod

/-- Full native masks after successive right conjugations. -/
def actMask : List Bool → ℕ → ℕ
  | [], m => m
  | b :: w, m => actMask w (maskAction b m)

private theorem maskProduct_mod (m : ℕ) :
    maskProduct kernelFactor (m % 8192) = maskProduct kernelFactor m := by
  unfold maskProduct
  congr 1
  congr 1
  funext i
  have h := Nat.testBit_mod_two_pow m 13 i.val
  rw [show 2^13 = (8192 : ℕ) from rfl] at h
  rw [h,decide_eq_true i.isLt,Bool.true_and]

/-- Exact word evaluation, including the central bit, at every action step. -/
theorem actorWord_conjugates (w : List Bool) (m : ℕ) :
    (actorWord w)⁻¹ * maskProduct kernelFactor m * actorWord w =
      maskProduct kernelFactor (actMask w m) := by
  induction w generalizing m with
  | nil => simp [actorWord,actMask]
  | cons b w ih =>
    have hs := source_action_law b ⟨m % 8192,Nat.mod_lt _ (by decide)⟩
    have hm : maskAction b (m % 8192) = maskAction b m := by
      unfold maskAction
      congr 1
      funext r i
      have h := Nat.testBit_mod_two_pow m 13 i.val
      rw [show 2^13 = (8192 : ℕ) from rfl] at h
      rw [h,decide_eq_true i.isLt,Bool.true_and]
    change (sourceGenerator b)⁻¹ * maskProduct kernelFactor (m % 8192) * sourceGenerator b = _ at hs
    rw [maskProduct_mod,hm] at hs
    simp only [actorWord,List.map_cons,List.prod_cons,mul_inv_rev,actMask]
    change (actorWord w)⁻¹ * (sourceGenerator b)⁻¹ * maskProduct kernelFactor m *
      (sourceGenerator b * actorWord w) = _
    rw [show (actorWord w)⁻¹ * (sourceGenerator b)⁻¹ * maskProduct kernelFactor m *
      (sourceGenerator b * actorWord w) =
      (actorWord w)⁻¹ * ((sourceGenerator b)⁻¹ * maskProduct kernelFactor m * sourceGenerator b) *
        actorWord w by group,hs]
    exact ih _

/-- Transport a literal source mask through the same ambient conjugator. -/
theorem nativeWord_conjugates (w : List Bool) (m n : Fin 8192)
    (h : actMask w m.val = n.val) :
    (MulAut.conj ((actorWord w : Model)⁻¹)) (nativeWord m) = nativeWord n := by
  have hh := congrArg (fun x : sourceSubgroup => (x : Model)) (actorWord_conjugates w m.val)
  simpa only [h,Subgroup.coe_mul,Subgroup.coe_inv,MulAut.conj_apply,inv_inv,nativeWord,
    kernelProduct,maskProduct] using hh

end Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.NamedLocalGeometry
