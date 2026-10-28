module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledLinearInvolutions
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Module
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Initial local bound on the full linear-three pair normalizer

The actual linear normalizer acts by conjugation on the faithful full SL₃
image. Its literal involutions therefore satisfy the paired fixed-vector
bound. Binary dimension counting yields m ≥ 2n for that whole normalizer,
including its field and summand-exchanging operators.
Source: Aschbacher--Smith Table7.2.1 and 7.3.2, pp.698--699.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter7.NormalizedSource
open ChapterB.QuasisimpleSource ChapterE

/-- The initial involution parameter of the full marked normalizer is at least 2n. -/
theorem doubledLinear_normalizer_moduleM (F : BinaryField)
    (a : MulAut (Matrix.SpecialLinearGroup (Fin 3) F.Carrier))
    (hne : ¬ Nonempty ((linearNatural F 3).Equiv
      ((linearNatural F 3).comp a.toMonoidHom))) :
    2 * F.degree ≤ moduleM (normalizerRepresentation
      ((linearNatural F 3).prod ((linearNatural F 3).comp a.toMonoidHom))) := by
  let μ := (linearNatural F 3).prod ((linearNatural F 3).comp a.toMonoidHom)
  let τ := normalizerRepresentation μ
  let W := (Fin 3 → F.Carrier) × (Fin 3 → F.Carrier)
  have hF : Module.finrank (ZMod 2) F.Carrier = F.degree := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.Carrier)
    rw [Nat.card_zmod,F.card_eq] at hc
    exact (Nat.pow_right_injective (by decide : 1 < 2) hc).symm
  have hdim : Module.finrank (ZMod 2) W = 6 * F.degree := by
    simp [W,Module.finrank_prod,Module.finrank_pi_fintype,hF]
    omega
  apply le_csInf ⟨_,Set.mem_insert _ _⟩
  rintro d (rfl | ⟨t,ht,rfl⟩)
  · exact hdim ▸ (by omega)
  · change 2 * F.degree ≤ fixedCodim τ (zpowers t)
    have hi : Function.Injective (actionHom μ) := by
      intro g k hgk
      apply specialLinearNatural_injective 3
      apply LinearMap.ext
      intro v
      exact congrArg (fun z : actionImage μ => (z.val.val (v,0)).1) hgk
    let e := MulEquiv.ofBijective (actionHom μ) ⟨hi,μ.asGroupHom.rangeRestrict_surjective⟩
    let α := (e.trans ((actionImage μ).normalizerMonoidHom t)).trans e.symm
    let f := LinearMap.GeneralLinearGroup.toLinearEquiv t.val
    have hsq : ∀ v, f (f v) = v := by
      intro v
      have hpow : t^2=1 := by simpa only [ht] using pow_orderOf_eq_one t
      exact congrArg (fun z : linearNormalizer μ => z.val.val v) hpow
    have hfne : f ≠ LinearEquiv.refl _ _ := by
      intro he
      have ht1 : t=1 := by
        apply Subtype.ext
        apply Units.ext
        apply LinearMap.ext
        intro v
        exact LinearEquiv.congr_fun he v
      have hh := ht
      rw [ht1,orderOf_one] at hh
      omega
    have heα (g) : e (α g) = (actionImage μ).normalizerMonoidHom t (e g) := by
      simp only [α,MulEquiv.trans_apply,e.apply_symm_apply]
    have hf (g) (v : W) : f (μ g v) = μ (α g) (f v) := by
      have hh := congrArg Subtype.val (heα g)
      change μ.asGroupHom (α g) = t.val * μ.asGroupHom g * t.val⁻¹ at hh
      exact congrArg (fun z : (Module.End (ZMod 2) W)ˣ => z.val v)
        ((mul_inv_eq_iff_eq_mul.mp hh.symm))
    have hc := doubledLinear_involution_fixed_card F a α hne f hfne hsq hf
    let E : fixedSpace τ (zpowers t) ≃ {v : W // f v = v} := {
      toFun := fun v => ⟨v.val,(mem_fixedSpace_zpowers_iff τ t v.val).mp v.property⟩
      invFun := fun v => ⟨v.val,(mem_fixedSpace_zpowers_iff τ t v.val).mpr v.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    rw [←Nat.card_congr E,Module.natCard_eq_pow_finrank (K := ZMod 2),
      Nat.card_zmod,F.card_eq,←pow_mul] at hc
    have hk : Module.finrank (ZMod 2) (fixedSpace τ (zpowers t)) ≤ 4*F.degree := by
      have hb := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc
      omega
    have hs := fixedCodim_add_finrank τ (zpowers t)
    rw [hdim] at hs
    omega

end CFSG.Quasithin.Chapter7.NormalizedSource
