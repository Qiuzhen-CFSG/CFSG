module
public import Theory.Representation.SL3DoubledNaturalOffenders.Centralizer
public import Theory.Representation.ScalarMultiplicity
public import Theory.Representation.PSL3Two.SingerRestriction
public import Theory.Representation.BinaryOddDisplacement.PrimeDivisibility

/-!
# Two natural copies cannot commute with an equivalent component action

A Singer element has no nonzero fixed vector on any sum of natural
SL₃(2) modules. A commuting copy acts through the two-dimensional
multiplicity space; its Singer displacement must be divisible by three.
Fixed-point-free action would give displacement two, a contradiction.

Source application: Aschbacher--Smith 10.1.1(6), printed p.741.
-/
public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace BinaryLinearThree.DoubledNatural
open Matrix.PSL3Two.OuterInvolutionSinger
local notation "Space" => SL3DoubledNaturalOffenders.Space (ZMod 2)
local notation "action" => SL3DoubledNaturalOffenders.representation (ZMod 2)

/-- The specified Singer element fixes no nonzero vector in the doubled row. -/
private theorem singer_fixed_eq_zero (v : Space) (hv : action singer v = v) : v = 0 := by
  funext i
  apply (show v i ∈ (⊥ : Submodule (ZMod 2) Vector) from ?_)
  rw [← SingerRestriction.natural_fixedSpace_singer,mem_fixedSpace_zpowers_iff]
  exact congrFun hv i

/-- Two linearly equivalent doubled actions cannot commute elementwise. -/
theorem not_commuting_conjugate (τ : Space ≃ₗ[ZMod 2] Space) :
    ¬ ∀ a b v, τ (action a (τ.symm (action b v))) =
      action b (τ (action a (τ.symm v))) := by
  intro hc
  let ρ : Representation (ZMod 2) Group Space := τ.conjRingEquiv.toMonoidHom.comp action
  obtain ⟨μ,hμ⟩ := ScalarMultiplicity.exists_multiplicity W
    (fun f hf => SL3DoubledNaturalOffenders.natural_centralizer_scalar f.toAddMonoidHom hf)
    ρ hc
  have hρ (v : Space) (hv : ρ singer v = v) : v = 0 := by
    change τ (action singer (τ.symm v)) = v at hv
    have hh : action singer (τ.symm v) = τ.symm v := by
      apply τ.injective
      simpa only [LinearEquiv.apply_symm_apply] using hv
    have hz := singer_fixed_eq_zero _ hh
    exact τ.symm.injective (hz.trans τ.symm.map_zero.symm)
  have hf : fixedSpace μ (zpowers singer) = ⊥ := by
    apply _root_.eq_bot_iff.mpr
    intro c hc
    have hc' := (mem_fixedSpace_zpowers_iff μ singer c).mp hc
    obtain ⟨v,hv⟩ := exists_ne (0 : Vector)
    have hz : (fun i => c i • v) = (0 : Space) :=
      hρ _ (by rw [hμ,hc'])
    have hz' : c = 0 := by
      funext i
      have hi := congrFun hz i
      exact (smul_eq_zero.mp hi).resolve_right hv
    exact hz'
  have hp : IsPGroup 7 (zpowers singer) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers]
    change orderOf singer = 7
    let : Fact (Nat.Prime 7) := ⟨by decide⟩
    exact orderOf_eq_prime (by decide : singer ^ 7 = 1) (by decide : singer ≠ 1))
  have hd := orderOf_two_dvd_fixedCodim_of_isPGroup μ (by decide : Nat.Prime 7)
    (by decide) (zpowers singer) hp
  have hdim := fixedCodim_add_finrank μ (zpowers singer)
  rw [hf,finrank_bot,add_zero] at hdim
  rw [hdim] at hd
  have ho : orderOf (2 : ZMod 7) = 3 :=
    orderOf_eq_prime (by decide : (2 : ZMod 7)^3 = 1) (by decide : (2 : ZMod 7) ≠ 1)
  norm_num [ho] at hd

end BinaryLinearThree.DoubledNatural
