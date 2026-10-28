module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Nonsolvable
public import CFSG.Quasithin.ChapterG.Section11.WholeRankOne

/-!
# Rank-one components in both large-action source branches

The original fixed-point alternative bounds the coefficient field of a natural
SL₂ component by four. The Hermitian action of the elementary actor is linear
over its fixed half-field; the marked transvection geometry forces that field
to be binary. Both cases therefore have degree at most four and are excluded
by the large extraspecial order. The G.9 unitary and Suzuki exclusions leave
only the SL₂(8) triple tensor, with the literal component identification and
scalar-extension intertwiner, degree eight and original actor rank three.

The source application constructs the G.9 hypotheses from the original flag
and its actual quotient action. Normality and irreducibility of the selected
component are branch conditions. No low-rank witness is assumed: the separate
fixed-line clause of G.11.1(3) is retained throughout. The Hermitian transport
adapts the argument in `ChapterG.Section11.WholeRankOne` without changing that
shared module or its existing low-rank API.

This is a component reduction, not the whole-group catalogue of 14.4.2.
Excluding the remaining triple tensor using the original seed, handling the
other component branches and constructing the marked catalogue remain with
the large-case assembly.

Source: Aschbacher--Smith, G.9.3(6),(7),(16), G.11.7 and 14.4.2,
printed pp.354,366--368,1006--1007; `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups TensorProduct
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.RankOne
open ChapterG
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X L : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
  {C : GroupClass} {k : Type*} [Field k] [Finite k] [CharP k 2]
local instance : Algebra (ZMod 2) k := SL2.BinarySmall.binaryAlgebra

private theorem not_natural
    (h : Section10.Hypothesis ρ B v W X X₀)
    (h9 : Section09.ComponentHypothesis C ρ X L L
      (finrank (ZMod 2) (Additive X)))
    (halt : BinaryOffender.fixedSpace ρ X = Submodule.span (ZMod 2) {v} ∨
      Section11.LowRankWitness ρ v X)
    (hd : 6 ≤ finrank (ZMod 2) V)
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
  have ha : BinaryOffender.fixedSpace ρ X = Submodule.span (ZMod 2) {v} ∨
      ∃ a : X, a ≠ 1 ∧ finrank (ZMod 2) (LinearMap.range (ρ a - 1)) ≤ 2 := by
    rcases halt with hf | hw
    · exact Or.inl hf
    · obtain ⟨a,ha,ho,_,hr,_⟩ := hw.exists_involution h.point_ne_zero
      have ha1 : a ≠ 1 := by intro he; simp [he] at ho
      exact Or.inr ⟨⟨a,ha⟩,fun he => ha1 (congrArg Subtype.val he),hr⟩
  have hb := MarkedSemilinearPlane.card_le_four_of_natural_normal_component
    ρ h.faithful L e f.toLinearEquiv hcoord X v h.point_ne_zero ha n hcard
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


private theorem triple_of_binary_rank_one
    (h : Section10.Hypothesis ρ B v W X X₀)
    (h9 : Section09.ComponentHypothesis C ρ X L L
      (finrank (ZMod 2) (Additive X)))
    (halt : BinaryOffender.fixedSpace ρ X = Submodule.span (ZMod 2) {v} ∨
      Section11.LowRankWitness ρ v X)
    (hd : 6 ≤ finrank (ZMod 2) V)
    (e : L ≃* SL(2,k)) (n : ℕ) (hn : 2 ≤ n) (hcard : Nat.card k = 2^n) :
    n = 3 ∧ finrank (ZMod 2) V = 8 ∧ finrank (ZMod 2) (Additive X) = 3 ∧
      SL2.BinarySmall.IsTriple ((ρ.comp L.subtype).comp e.symm.toMonoidHom) := by
  obtain ⟨hrank,hcases⟩ := Section09.DefiningCharacteristic.rank_one_module_alternatives h9 e n hn hcard
  rcases hcases with ⟨hdim,_,hnat⟩ | ⟨r,hr,hnr,_,_,hherm⟩ | ⟨hn3,hd8,hr3,ht,_,_⟩
  · exact (not_natural h h9 halt hd e n hcard hdim hnat).elim
  · let : NeZero r := ⟨hr.ne'⟩
    apply (not_hermitian h h9 hd r (by omega) ?_).elim
    obtain ⟨f,⟨c⟩⟩ := hherm
    refine ⟨e.trans (Atlas.fieldEquivSL 2 f),c.toLinearEquiv,?_⟩
    intro l w
    have hh := Representation.IntertwiningMap.isIntertwining _ _ c.toIntertwiningMap (e l) w
    change c (ρ (e.symm (e l)) w) = SL2.BinarySmall.hermitian r
      (Matrix.SpecialLinearGroup.map f.toRingHom (e l)) (c w) at hh
    rw [e.symm_apply_apply] at hh
    exact hh
  · exact ⟨hn3,hd8,hr3,ht⟩

/-- The literal rank-one remainder, retaining the component and its action
on the scalar extension of the original space. -/
@[expose] def TripleModel (ρ : Representation (ZMod 2) G V) (X L : Subgroup G)
    [IsElementaryAbelian 2 X] : Prop :=
  finrank (ZMod 2) V = 8 ∧ finrank (ZMod 2) (Additive X) = 3 ∧
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2),
      letI : Algebra (ZMod 2) k := SL2.BinarySmall.binaryAlgebra
      ∃ e : L ≃* SL(2,k), Nat.card k = 8 ∧
        SL2.BinarySmall.IsTriple ((ρ.comp L.subtype).comp e.symm.toMonoidHom)

private theorem triple_of_bender
    (h : Section10.Hypothesis ρ B v W X X₀)
    (h9 : Section09.ComponentHypothesis C ρ X L L
      (finrank (ZMod 2) (Additive X)))
    (halt : BinaryOffender.fixedSpace ρ X = Submodule.span (ZMod 2) {v} ∨
      Section11.LowRankWitness ρ v X)
    (hd : 6 ≤ finrank (ZMod 2) V)
    (model : ClassificationModels.IsBenderModel L) : TripleModel ρ X L := by
  cases model with
  | linear n hn hm =>
    obtain ⟨k,_,_,hc,⟨e⟩⟩ := hm
    let : Fintype k := Fintype.ofFinite k
    let : CharP k 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hc)
    let e' := e.trans (Theory.PSL2.sl2QuotientEquiv k).symm
    obtain ⟨hn3,hd8,hr3,ht⟩ := triple_of_binary_rank_one h h9 halt hd e' n hn hc
    exact ⟨hd8,hr3,k,inferInstance,inferInstance,inferInstance,e',by simpa [hn3] using hc,ht⟩
  | unitary n hn hm =>
    obtain ⟨k,_,_,J,hcard,hconj,⟨e⟩⟩ := hm
    exact (Section09.DefiningCharacteristic.TwistedExclusions.not_unitary_three_positive_exponent
      h9 J (by omega) hcard hconj (Or.inr ⟨e⟩)).elim
  | suzuki n hn hm => exact (h9.not_suzuki hn hm.some).elim

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.RankOne

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- For the original large action, every normal irreducible Bender component
is the SL₂(8) triple tensor. Both source fixed-point clauses are included;
no low-rank or fixed-line hypothesis is added to the ambient assumptions. -/
theorem source_large_bender_component_triple (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (C : Subgroup F.TerminalHdot) [C.Normal] (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C, F.terminalDot (F.X g)⁆ ≠ ⊥)
    (hirr : IsIrreducible (F.terminalRepresentation.comp C.subtype))
    (model : ClassificationModels.IsBenderModel C) :
    RankOne.TripleModel F.terminalRepresentation (F.terminalDot (F.X g)) C := by
  obtain ⟨_,_,B,v,hyp,hline,_⟩ := source_terminal_marked_hypothesis F d earlier hq chosen
    structural alternatives hne g hgP hgH
  have hd : 6 ≤ finrank (ZMod 2) (Additive F.Uhat) := by
    have hcenter := (source_extraspecial_order d earlier hq chosen structural alternatives
      F hne hZ).1.center_order_p
    have hc : Nat.card F.U = 2 ^ (finrank (ZMod 2) (Additive F.Uhat) + 1) := by
      rw [card_eq_card_quotient_mul_card_subgroup (center F.U),hcenter]
      change Nat.card (Additive F.Uhat) * 2 = _
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,pow_succ]
    by_contra hn
    have hb := Nat.pow_le_pow_right (n := 2) (by decide)
      (by omega : finrank (ZMod 2) (Additive F.Uhat) + 1 ≤ 6)
    rw [← hc] at hb
    norm_num at hb
    omega
  have h9 : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
      F.terminalRepresentation (F.terminalDot (F.X g)) C C
      (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) := {
    toSetup := ChapterG.Section11.setup hyp
    quotient := source_terminal_cover F d chosen
    component := hC
    noncentral := hm
    normal_H := inferInstance
    irreducible := hirr
    components := Or.inl rfl }
  apply RankOne.triple_of_bender hyp h9 ?_ hd model
  rcases source_terminal_fixed_point_alternative d earlier hq chosen structural alternatives
      F hne g hgP hgH v hline with hf | ⟨a,_,hr,hv⟩
  · exact Or.inl hf
  · exact Or.inr ⟨a,a.property,hr,hv⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
