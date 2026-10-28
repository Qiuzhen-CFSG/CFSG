module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import Theory.SpecificGroups.SL2.NormalMonolith
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.AtlasPort.LinearGroups.SL2Order

/-!
# The matrix models in the surviving radical embedding

The prime in an SL₂ model is determined by its actual order. Odd normal
subgroups of SL₂ in odd characteristic are trivial, since every nontrivial
normal subgroup contains the central involution. Consequently an elementary
odd kernel in an SL₂ extension is its Fitting subgroup whenever that Fitting
subgroup has odd order. These facts identify the kernel without assuming a
splitting or a natural-module action.

At five, the center of SL₃ is trivial, so both large models in A.3.12(10)
give the same concrete PSL₃(ZMod 5) carrier.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
A.3.12(10), printed p.47, and proof of 1.3.8, printed p.513.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.FiveCase
open Section02.LocalModels
universe u
variable {B : Type u} [Group B]

/-- A prime-field model can be given over the specified prime field. -/
theorem isSL_prime_iff {s n : ℕ} (hs : s.Prime) :
    IsSL B n s ↔ Nonempty (B ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod s)) := by
  let : Fact s.Prime := ⟨hs⟩
  constructor
  · rintro ⟨F, _, _, hF, ⟨e⟩⟩
    let : Fintype F := Fintype.ofFinite F
    let f := ZMod.ringEquivOfPrime F hs (by simpa only [Nat.card_eq_fintype_card] using hF)
    exact ⟨e.trans (Atlas.fieldEquivSL n f.symm)⟩
  · rintro ⟨e⟩
    exact ⟨ZMod s, inferInstance, inferInstance, Nat.card_zmod s, ⟨e⟩⟩

/-- The exact order, rather than a family label, determines the SL₂ parameter. -/
theorem isSL_two_card {s : ℕ} (h : IsSL B 2 s) :
    Nat.card B = s * (s ^ 2 - 1) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, Atlas.card_sl_two, hF]

/-- The parameter of an actual SL₂(r) model agrees with the five-model. -/
theorem isSL_two_parameter_five {r : ℕ} (hr : r.Prime)
    (h : IsSL B 2 r) (h5 : IsSL B 2 5) : r = 5 := by
  have hc := (isSL_two_card h).symm.trans (isSL_two_card h5)
  norm_num at hc
  have hr2 := hr.two_le
  have hsq : 1 ≤ r ^ 2 := by nlinarith
  have hd := Nat.sub_add_cancel hsq
  nlinarith [sq_nonneg (r - 5 : ℤ)]

/-- No odd normal subgroup survives in an odd-characteristic SL₂ quotient. -/
theorem odd_normal_sl_two_eq_bot {s : ℕ} (hs : s.Prime) (hs3 : 3 < s)
    (D : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod s))) [D.Normal]
    (hD : Odd (Nat.card D)) : D = ⊥ := by
  let : Fact s.Prime := ⟨hs⟩
  have htwo : (2 : ZMod s) ≠ 0 := by
    intro h
    have hd : s ∣ 2 := (ZMod.natCast_eq_zero_iff 2 s).mp h
    have := Nat.le_of_dvd (by decide) hd
    omega
  apply Matrix.SpecialLinearGroup.eq_bot_of_neg_one_not_mem htwo D
  intro hm
  let z : D := ⟨-1, hm⟩
  have hz2 : z ^ 2 = 1 := by apply Subtype.ext; simp [z, pow_two]
  have hzne : z ≠ 1 := by
    intro he
    have he00 := congrArg (fun a : D => a.val.val 0 0) he
    have hneg : (-1 : ZMod s) = 1 := by simpa [z] using he00
    exact htwo (by linear_combination -hneg)
  have ho : orderOf z = 2 := orderOf_eq_prime hz2 hzne
  exact hD.not_two_dvd_nat (by simpa only [ho] using _root_.orderOf_dvd_natCard z)

/-- An odd normal subgroup lies in the specified elementary extension kernel. -/
theorem odd_normal_le_kernel {s : ℕ} (hs : s.Prime) (hs3 : 3 < s)
    (U D : Subgroup B) [U.Normal] [D.Normal]
    (e : B ⧸ U ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod s))
    (hD : Odd (Nat.card D)) : D ≤ U := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' U)
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective U)
  let : (D.map f).Normal := (inferInstance : D.Normal).map f hf
  have hbot : D.map f = ⊥ := odd_normal_sl_two_eq_bot hs hs3 _
    (hD.of_dvd_nat (D.card_map_dvd f))
  intro x hx
  have he : f x = 1 := (D.map_eq_bot_iff.mp hbot) hx
  exact (QuotientGroup.eq_one_iff x).mp (e.injective (by simpa [f] using he))

/-- Identify the actual kernel with F(B), using the oddness supplied by A.3.6. -/
theorem fitting_eq_extension_kernel [Finite B] {s : ℕ}
    (hs : s.Prime) (hs3 : 3 < s) (U : Subgroup B) [U.Normal]
    (hU : ElementaryModel s 2 U)
    (e : B ⧸ U ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod s))
    (hF : Odd (Nat.card (fittingSubgroup B))) : fittingSubgroup B = U := by
  apply le_antisymm (odd_normal_le_kernel hs hs3 U _ e hF)
  obtain ⟨eU⟩ := hU
  let := Group.nilpotent_of_mulEquiv eU.symm
  exact le_sSup ⟨inferInstance, inferInstance⟩

/-- At five the two covering possibilities have the same concrete carrier. -/
theorem large_five_model
    (h : ClassicalGroup.IsPSL B 3 5 ∨ IsSL B 3 5) :
    Nonempty (B ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 5)) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  rcases h with ⟨F, _, _, hF, ⟨e⟩⟩ | h
  · let : Fintype F := Fintype.ofFinite F
    let f := ZMod.ringEquivOfPrime F (by decide : Nat.Prime 5)
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    exact ⟨e.trans (Atlas.fieldEquivPSL 3 f.symm)⟩
  · obtain ⟨e⟩ := (isSL_prime_iff (by decide : Nat.Prime 5)).mp h
    have hc : center (Matrix.SpecialLinearGroup (Fin 3) (ZMod 5)) = ⊥ := by
      apply card_eq_one.mp
      rw [Atlas.ExceptionalSupport.card_sl_center]
      norm_num
    exact ⟨e.trans (QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq hc.symm))⟩

end CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.FiveCase
