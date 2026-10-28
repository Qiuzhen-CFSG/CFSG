module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Model
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Arithmetic

/-!
# Fixed-space exclusion from a literal tensor-exchange model

Interchange on a tensor square of size n moves n(n-1)/2 dimensions. For the
non-small SL₃ words this is at least six binary dimensions, including n=3:
in that case the original Schur degree is at least two. Actors of rank at
most two are therefore excluded. For larger actors, the model supplies a
nonidentity diagonal involution. Its common fixed space with interchange
has dimension at most half the tensor square. Exact Schur descent and the
proved degree bound 9r finish the strict inequality.

The construction of the exchange model is a separate source obligation.
Source: GM, Classification of 2F-modules II, Proposition 4.8 steps 2,4,5,
manuscript pp.26–28; Aschbacher–Smith K.3.2, printed pp.454–456.
-/

public section
noncomputable section
open Representation Representation.BinaryOffender
open Representation.BinaryOffender.SchurNormalizer
open Representation.SL3.BinaryDefiningFactors
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition.AbsoluteExhaustion
open LinearMap.FixedSpaceTransport
open scoped MatrixGroups TensorProduct

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Tensors
variable {B : BinaryField} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    {σ : Representation (ZMod 2) SL(3,B.Carrier) V} [IsIrreducible σ]
    {A : Subgroup (linearNormalizer σ)} {hs : ∀ t ∈ A, IsSchurLinear σ t}

namespace SwapRealization
variable (R : SwapRealization B σ A hs)

/-- The square is an actual model of the original Schur scalar extension. -/
theorem finrank_eq : Module.finrank (ZMod 2) V = schurDegree σ * (R.size * R.size) := by
  rw [Representation.finrank_eq_schurDegree_mul 2 σ (SplittingField σ),
    R.equiv.finrank_eq, TensorInterchange.finrank_space]
  rfl

/-- Exact interchange displacement gives a bound for the whole actor's common fixed space. -/
theorem schur_mul_choose_le_fixedCodim : schurDegree σ * R.size.choose 2 ≤
    fixedCodim (normalizerRepresentation σ) A := by
  have he := finrank_range_sub_one_equiv R.equiv
    (absoluteActor σ (SplittingField σ) R.outer.val (hs _ R.outer.property))
    (TensorInterchange.flip (SplittingField σ) R.size) R.outer_action
  have hb := binary_range_finrank σ (SplittingField σ) R.outer.val (hs _ R.outer.property)
  rw [he, TensorInterchange.finrank_range_flip] at hb
  have hm := NaturalTensor.operatorFixedCodim_le_fixedCodim
    (normalizerRepresentation σ) A R.outer.property
  change Module.finrank (ZMod 2) (R.outer.val.val.val - 1).range ≤ _ at hm
  rw [hb] at hm
  exact hm

include R

/-- The pair in the model bounds the common fixed space of the entire actor. -/
theorem finrank_le_twice_fixedCodim (hr : 2 < rank A) :
    Module.finrank (ZMod 2) V ≤ 2 * fixedCodim (normalizerRepresentation σ) A := by
  obtain ⟨u, f, hf2, hfne, hfe⟩ := R.pair_action hr
  let C := (R.outer.val.val.val - 1).ker ⊓ (u.val.val.val - 1).ker
  have hC : fixedSpace (normalizerRepresentation σ) A ≤ C := by
    intro v hv
    exact ⟨sub_eq_zero.mpr (hv R.outer), sub_eq_zero.mpr (hv u)⟩
  have hdim := Submodule.finrank_mono hC
  have he := (commonFixedEquiv R.equiv
    (absoluteActor σ (SplittingField σ) R.outer.val (hs _ R.outer.property))
    (absoluteActor σ (SplittingField σ) u.val (hs _ u.property))
    (TensorInterchange.flip (SplittingField σ) R.size) (TensorProduct.map f f)
    R.outer_action hfe).finrank_eq
  have hb := binary_commonFixed_finrank σ (SplittingField σ)
    R.outer.val u.val (hs _ R.outer.property) (hs _ u.property)
  rw [he] at hb
  have hh := TensorInterchange.common_fixed_bound R.size
    (by have := R.three_le; omega : 2 ≤ R.size) f hf2 hfne
  have hm := Nat.mul_le_mul_left (schurDegree σ) hh
  have hd := R.finrank_eq
  have hc := fixedCodim_add_finrank (normalizerRepresentation σ) A
  change Module.finrank (ZMod 2) C = schurDegree σ * _ at hb
  nlinarith only [hd, hb, hm, hdim, hc]

/-- The smallest exchange still moves six binary dimensions on a remaining word. -/
theorem six_le_fixedCodim (M : RepeatedModel B σ)
    (hp : 0 < naturalCount M.block + adjointCount M.block) (hn : ¬ M.Small)
    (hj : ¬ SingleAdjoint B σ M) :
    6 ≤ fixedCodim (normalizerRepresentation σ) A := by
  have hb := R.schur_mul_choose_le_fixedCodim
  have hspos := schurDegree_pos σ
  by_cases h4 : 4 ≤ R.size
  · have hchoose : 6 ≤ R.size.choose 2 := by
      simpa only [show Nat.choose 4 2 = 6 by decide] using Nat.choose_le_choose 2 h4
    nlinarith
  · have h3 : R.size = 3 := by have := R.three_le; omega
    have hd : Module.finrank (ZMod 2) V = schurDegree σ * 9 := by
      simpa [h3] using R.finrank_eq
    have hs2 := two_le_schurDegree_of_square_three B σ M hp hn hj hd
    norm_num [h3] at hb
    omega

/-- A genuine tensor-exchange realization excludes the original cubic actor.
No cubicity is needed once the actual exchange and diagonal actions are known. -/
theorem estimate (M : RepeatedModel B σ)
    (hp : 0 < naturalCount M.block + adjointCount M.block) (hn : ¬ M.Small)
    (hj : ¬ SingleAdjoint B σ M) (hr : rank A ≤ 2 * B.degree) :
    2 * rank A < fixedCodim (normalizerRepresentation σ) A := by
  by_cases hsmall : rank A ≤ 2
  · have hh := R.six_le_fixedCodim M hp hn hj
    omega
  · have hh := R.finrank_le_twice_fixedCodim (by omega)
    have hd := nine_mul_degree_le_finrank B σ M hp hn hj
    have hpos := B.degree_pos
    omega

end SwapRealization

/-- On pure-adjoint tensors, the quarter-displacement bound for one actual
outer involution implies the strict common-fixed-space bound for the whole actor. -/
theorem adjointTensorEstimate_of_displacement (hd : AdjointTensorDisplacement B σ) :
    AdjointTensorEstimate B σ := by
  intro M ha hb hj A hA _ hr ho hs
  obtain ⟨x, hx, hxnot⟩ := SetLike.not_le_iff_exists.mp ho
  obtain ⟨t, ht, rfl⟩ := hx
  let : IsElementaryAbelian 2 A := hA.2
  have ht2 : t ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian t ht
  have hmove := hd M ha hb hj t ht2 hxnot (hs t ht)
  have hdim := thirty_two_mul_degree_le_finrank B σ M ha hb hj
  have hm := NaturalTensor.operatorFixedCodim_le_fixedCodim
    (normalizerRepresentation σ) A ht
  change Module.finrank (ZMod 2) (t.val.val - 1).range ≤ _ at hm
  have hpos := B.degree_pos
  omega

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Tensors
