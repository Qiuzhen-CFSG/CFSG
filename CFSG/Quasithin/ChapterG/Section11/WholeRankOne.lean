module
public import CFSG.Quasithin.ChapterG.Section11.LowRank
public import CFSG.Quasithin.ChapterG.Section09.SingleComponentExclusions
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions.UnitarySource
public import CFSG.Quasithin.ClassificationModels.Families
public import CFSG.Quasithin.ChapterG.Section10.CoefficientField
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.RankOneRecognition.Component
public import Theory.Representation.SL2NaturalOffenders.MarkedAlternatives
public import Theory.Representation.OrthogonalFourMinusRankOne.AmbientActions.Elementary
public import Theory.Representation.OrthogonalFourMinusRankOne.RootActors
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.TwistedTensor
public import Theory.Representation.BinaryIrreducibleCentralizer.InnerInvolution
public import Mathlib.Algebra.Module.TransferInstance

/-!
# Excluding whole rank-one components in the marked low-rank action

The G.9 classifier leaves natural, Hermitian and triple-tensor modules for
an irreducible binary SL₂ component. The low-displacement witness bounds
the natural field by four, contradicting degree at least six. In the
Hermitian case the actual component automorphism bound and the original
G.10 dimension equality force the marked space to have dimension at least
three; its coefficient field must then be binary. No small-actor bound is
assumed. For the degree-three triple tensor every ambient involution lies
in the component and moves four dimensions.

Together with the genuine G.9 unitary and Suzuki exclusions this removes
the full Bender family for a single whole component. The source application
is `StrictWholeRankOne`; the other whole-component families remain open.
Source: Aschbacher--Smith G.9.3 and G.11.7, printed pp.354,366--368.
-/

public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups TensorProduct
namespace CFSG.Quasithin.ChapterG.Section11.WholeRankOne
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X L : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
  {C : GroupClass} {k : Type*} [Field k] [Finite k] [CharP k 2]
local instance : Algebra (ZMod 2) k := SL2.BinarySmall.binaryAlgebra

private theorem involution_mem_odd_rank_one
    (h : Section09.ComponentHypothesis C ρ X L L
      (finrank (ZMod 2) (Additive X)))
    (e : L ≃* SL(2,k)) {n : ℕ} (hn : Odd n) (hcard : Nat.card k = 2^n)
    (a : G) (ha : a^2 = 1) : a ∈ L := by
  let := h.normal_H
  let := h.irreducible
  let φ : G →* MulAut SL(2,k) := (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal
  have hφ : φ a ^ 2 = 1 := by rw [← map_pow,ha,map_one]
  have hi : φ a ∈ MulAut.innerSubgroup SL(2,k) := by
    by_contra hout
    exact (Nat.not_even_iff_odd.mpr hn)
      (Theory.PSL2.sl2_outer_involution_formula hn.pos hcard (φ a) hφ hout).1
  change MulAut.congr e (MulAut.conjNormal (H := L) a) ∈ MulAut.innerSubgroup _ at hi
  rw [← MulAut.map_innerSubgroup_congr e,Subgroup.mem_map_equiv] at hi
  simp only [MulEquiv.symm_apply_apply] at hi
  have hz : center L = ⊥ := by
    apply bot_unique
    intro l hl
    apply e.injective
    exact (mem_bot.mp ((Theory.PSL2.sl2_center_eq_bot k) ▸
      ((Subgroup.centerCongr e) ⟨l,hl⟩).property)).trans e.map_one.symm
  exact BinaryIrreducibleCentralizer.inner_square_one_mem ρ L h.faithful hz ha
    (by obtain ⟨l,hl⟩ := hi; exact ⟨l,hl.symm⟩)

set_option backward.isDefEq.respectTransparency false in
private theorem not_triple
    (h : Section10.Hypothesis ρ B v W X X₀)
    (h9 : Section09.ComponentHypothesis C ρ X L L
      (finrank (ZMod 2) (Additive X)))
    (hw : LowRankWitness ρ v X) (e : L ≃* SL(2,k)) (hcard : Nat.card k = 2^3)
    (ht : SL2.BinarySmall.IsTriple ((ρ.comp L.subtype).comp e.symm.toMonoidHom)) : False := by
  obtain ⟨a,ha,ho,_,hr,_⟩ := hw.exists_involution h.point_ne_zero
  have hmem := involution_mem_odd_rank_one h9 e (by decide : Odd 3) hcard a
    (by simpa only [ho] using pow_orderOf_eq_one a)
  let b : L := ⟨a,hmem⟩
  let σ := (ρ.comp L.subtype).comp e.symm.toMonoidHom
  have hb : orderOf (e b) = 2 := by rw [e.orderOf_eq,← Subgroup.orderOf_coe]; exact ho
  obtain ⟨f⟩ := ht
  have hrank := RankTwo.finrank_movedSpace_equiv (k := k)
    (V := k ⊗[ZMod 2] V) (W := SL2.BinarySmall.TripleSpace k)
    (extendScalars k σ) (SL2.BinarySmall.triple (K := k)) f (e b)
  have he := (RankTwo.finrank_movedSpace_extendScalars (E := k) σ (e b)).symm.trans
    (hrank.trans (RankTwo.TwistedTensor.rank_eq_four (e b) hb))
  change finrank (ZMod 2) (RankTwo.movedSpace ρ ((e.symm (e b)) : G)) = 4 at he
  rw [e.symm_apply_apply] at he
  change finrank (ZMod 2) (RankTwo.movedSpace ρ a) = 4 at he
  omega

set_option backward.isDefEq.respectTransparency false in
private theorem not_natural
    (h : Section10.Hypothesis ρ B v W X X₀)
    (h9 : Section09.ComponentHypothesis C ρ X L L
      (finrank (ZMod 2) (Additive X)))
    (hw : LowRankWitness ρ v X) (hd : 6 ≤ finrank (ZMod 2) V)
    (e : L ≃* SL(2,k)) (n : ℕ) (hcard : Nat.card k = 2^n)
    (hdim : finrank (ZMod 2) V = 2*n)
    (hnat : SL2.BinarySmall.IsNatural ((ρ.comp L.subtype).comp e.symm.toMonoidHom)) : False := by
  let := h9.normal_H
  obtain ⟨f⟩ := hnat
  have hcoord (l : L) (w : V) : f (ρ l w) = (e l).val.mulVec (f w) := by
    have hh := Representation.IntertwiningMap.isIntertwining _ _ f.toIntertwiningMap (e l) w
    change f (ρ (e.symm (e l)) w) = (e l).val.mulVec (f w) at hh
    rw [e.symm_apply_apply] at hh
    exact hh
  obtain ⟨a,ha,ho,_,hr,_⟩ := hw.exists_involution h.point_ne_zero
  have ha1 : a ≠ 1 := by intro he; simp [he] at ho
  have hb := MarkedSemilinearPlane.card_le_four_of_natural_normal_component
    ρ h.faithful L e f.toLinearEquiv hcoord X v h.point_ne_zero
    (Or.inr ⟨⟨a,ha⟩,fun he => ha1 (congrArg Subtype.val he),hr⟩) n hcard
  rw [hcard] at hb
  have hn : n ≤ 2 := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hb
  omega

open Representation.OrthogonalFourMinus.FiniteModel
local instance (n : ℕ) : Algebra (ZMod 2) (fixedField n) := ZMod.algebra _ 2
local instance (n : ℕ) [NeZero n] : Module (ZMod 2) (Space n) :=
  Module.compHom (Space n) (algebraMap (ZMod 2) (fixedField n))

private theorem not_hermitian
    (h : Section10.Hypothesis ρ B v W X X₀)
    (h9 : Section09.ComponentHypothesis C ρ X L L
      (finrank (ZMod 2) (Additive X)))
    (hd : 6 ≤ finrank (ZMod 2) V)
    (r : ℕ) [NeZero r] (hrank : finrank (ZMod 2) (Additive X) ≤ 2*r)
    (hnat : Section09.Quasiequivalent (ρ.comp L.subtype) (SL2.BinarySmall.hermitian r)) : False := by
  classical
  let := h9.normal_H
  obtain ⟨e,c,hc⟩ := hnat
  let τ : Representation (ZMod 2) G (Space r) := c.conjRingEquiv.toMonoidHom.comp ρ
  have ht (a : G) (w : Space r) : τ a w = c (ρ a (c.symm w)) := rfl
  have hcoord (l : L) (w : Space r) : τ l w = SL2.BinarySmall.hermitian r (e l) w := by
    rw [ht]
    simpa only [MonoidHom.comp_apply,Subgroup.coe_subtype,c.apply_symm_apply] using hc l (c.symm w)
  have hlin := Representation.OrthogonalFourMinus.RankOne.AmbientActions.elementary_normal_component_linear
    r τ L e hcoord X
  have hdim : finrank (ZMod 2) V = 4*r :=
    c.finrank_eq.trans (Representation.OrthogonalFourMinus.RankOne.space_binary_finrank r)
  have hq := (Group.rank_le_of_surjective (QuotientGroup.mk' X₀)
    (QuotientGroup.mk'_surjective X₀)).trans (IsElementaryAbelian.rank_le_finrank (p := 2) X)
  have hW : 3 ≤ finrank (ZMod 2) W := by have := h.dimension; omega
  let : SMul (ZMod 2) (fixedField r) := (ZMod.algebra (fixedField r) 2).toSMul
  let : Module (fixedField r) V := c.toAddEquiv.module (fixedField r)
  let : IsScalarTower (ZMod 2) (fixedField r) V :=
    IsScalarTower.of_algebraMap_smul (fun a w => by
      fin_cases a
      · change algebraMap (ZMod 2) (fixedField r) (0 : ZMod 2) • w = (0 : ZMod 2) • w
        simp only [map_zero,zero_smul]
      · change algebraMap (ZMod 2) (fixedField r) (1 : ZMod 2) • w = (1 : ZMod 2) • w
        simp only [map_one,one_smul])
  have hb : Nat.card (fixedField r) ≤ 2 := h.coefficient_card_le_two (K := fixedField r) (by
    intro x d w
    apply c.injective
    change c (ρ x (c.symm (d • c w))) = c (c.symm (d • c (ρ x w)))
    rw [c.apply_symm_apply]
    change τ x (d • c w) = _
    rw [hlin,ht,c.symm_apply_apply]) hW
  rw [card_fixedField] at hb
  have hr : r ≤ 1 := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp (by simpa using hb)
  omega

/-- A whole binary rank-one component is impossible under the original
marked geometry and low-displacement witness in dimension at least six. -/
theorem not_binary_rank_one
    (h : Section10.Hypothesis ρ B v W X X₀)
    (h9 : Section09.ComponentHypothesis C ρ X L L
      (finrank (ZMod 2) (Additive X)))
    (hw : LowRankWitness ρ v X) (hd : 6 ≤ finrank (ZMod 2) V)
    (e : L ≃* SL(2,k)) (n : ℕ) (hn : 2 ≤ n) (hcard : Nat.card k = 2^n) : False := by
  obtain ⟨hrank,hcases⟩ := Section09.DefiningCharacteristic.rank_one_module_alternatives h9 e n hn hcard
  rcases hcases with ⟨hdim,_,hnat⟩ | ⟨r,hr,hnr,_,_,hherm⟩ | ⟨hn3,_,_,ht,_,_⟩
  · exact not_natural h h9 hw hd e n hcard hdim hnat
  · let : NeZero r := ⟨hr.ne'⟩
    apply not_hermitian h h9 hd r (by omega)
    obtain ⟨f,⟨c⟩⟩ := hherm
    refine ⟨e.trans (Atlas.fieldEquivSL 2 f),c.toLinearEquiv,?_⟩
    intro l w
    have hh := Representation.IntertwiningMap.isIntertwining _ _ c.toIntertwiningMap (e l) w
    change c (ρ (e.symm (e l)) w) = SL2.BinarySmall.hermitian r
      (Matrix.SpecialLinearGroup.map f.toRingHom (e l)) (c w) at hh
    rw [e.symm_apply_apply] at hh
    exact hh
  · exact not_triple h h9 hw e (hn3 ▸ hcard) ht
/-- The same exclusion uses the source's literal projective rank-one carrier. -/
theorem not_projective_binary_rank_one
    (h : Section10.Hypothesis ρ B v W X X₀)
    (h9 : Section09.ComponentHypothesis C ρ X L L
      (finrank (ZMod 2) (Additive X)))
    (hw : LowRankWitness ρ v X) (hd : 6 ≤ finrank (ZMod 2) V)
    {n : ℕ} (hn : 2 ≤ n) (model : ClassicalGroup.IsPSL L 2 (2^n)) : False := by
  obtain ⟨F,_,_,hcard,⟨e⟩⟩ := model
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  exact not_binary_rank_one h h9 hw hd
    (e.trans (Theory.PSL2.sl2QuotientEquiv F).symm) n hn hcard

/-- Every Bender-family carrier is excluded on the actual whole component:
linear, unitary and Suzuki, with no field-size or small-actor premise added. -/
theorem not_bender_model
    (h : Section10.Hypothesis ρ B v W X X₀)
    (h9 : Section09.ComponentHypothesis C ρ X L L
      (finrank (ZMod 2) (Additive X)))
    (hw : LowRankWitness ρ v X) (hd : 6 ≤ finrank (ZMod 2) V)
    (model : ClassificationModels.IsBenderModel L) : False := by
  cases model with
  | linear n hn hm => exact not_projective_binary_rank_one h h9 hw hd hn hm
  | unitary n hn hm =>
    obtain ⟨F,_,_,J,hcard,hconj,⟨e⟩⟩ := hm
    exact Section09.DefiningCharacteristic.TwistedExclusions.not_unitary_three_positive_exponent
      h9 J (by omega) hcard hconj (Or.inr ⟨e⟩)
  | suzuki n hn hm => exact h9.not_suzuki hn hm.some

end CFSG.Quasithin.ChapterG.Section11.WholeRankOne
