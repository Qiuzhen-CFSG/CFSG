module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledLinearNearOffendersFixed
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledLinearLocal
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank.SourceBound
public import Theory.GroupAction.PerfectCentralQuotient

/-!
# No near offenders on a nonbinary natural and twisted pair

The full normalizer has elementary two-rank at most 2n: conjugation on the
faithful SL3 image is injective on every elementary two-subgroup, and the
native PSL3 automorphism bound preserves the full scalar center.
An actor of order at most q has rank at most n and fixed codimension at
least 2n. A larger actor fixes at most q³ vectors and hence has codimension
at least 3n. For n>1 both inequalities give codimension greater than rank+1.
No quasithin ambient hypothesis or odd-prime displacement claim is used.
Source: Aschbacher--Smith H.4.1 and Table7.2.1, printed pp.383--385,698.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter7.NormalizedSource
open ChapterB.QuasisimpleSource ChapterE

/-- The full marked pair normalizer has two-rank at most twice the field degree. -/
theorem doubledLinear_normalizer_twoRank_le (F : BinaryField)
    (a : MulAut (Matrix.SpecialLinearGroup (Fin 3) F.Carrier))
    (hne : ¬ Nonempty ((linearNatural F 3).Equiv
      ((linearNatural F 3).comp a.toMonoidHom))) :
    primeRank 2 (linearNormalizer
      ((linearNatural F 3).prod ((linearNatural F 3).comp a.toMonoidHom))) ≤ 2*F.degree := by
  let σ := linearNatural F 3
  let τ := σ.comp a.toMonoidHom
  let μ := σ.prod τ
  let : IsIrreducible σ := ExtensionConsequences.linearNatural_irreducible F (by decide)
  let : IsIrreducible τ := (irreducible_comp_surjective_iff
    a.toMonoidHom a.surjective σ).mpr inferInstance
  have hi : Function.Injective (actionHom μ) := by
    intro g k hgk
    apply specialLinearNatural_injective 3
    apply LinearMap.ext
    intro v
    exact congrArg (fun z : actionImage μ => (z.val.val (v,0)).1) hgk
  let e := MulEquiv.ofBijective (actionHom μ) ⟨hi,μ.asGroupHom.rangeRestrict_surjective⟩
  have hr := irreducible_pair_normalizer_rank_le σ τ hne
  rw [←primeRank_equiv 2 (MulAut.congr e)] at hr
  let S := Matrix.SpecialLinearGroup (Fin 3) F.Carrier
  let : Group.IsPerfect S := Atlas.sl_perfect 3 (by decide)
  have hs := Theory.GroupTheory.primeRank_le_of_injective 2
    (quotientAut (center S)) MulAut.quotient_center_injective
  exact hr.trans (hs.trans (Matrix.PSL3Even.automorphism_two_rank_eq
    F.Carrier F.degree_pos F.card_eq).le)

/-- Every nontrivial elementary two-subgroup of the full nonbinary pair
normalizer has fixed codimension strictly above its rank plus one. -/
theorem doubledLinear_no_near_offender (F : BinaryField) (hn : 1 < F.degree)
    (a : MulAut (Matrix.SpecialLinearGroup (Fin 3) F.Carrier))
    (hne : ¬ Nonempty ((linearNatural F 3).Equiv
      ((linearNatural F 3).comp a.toMonoidHom)))
    (A : Subgroup (linearNormalizer
      ((linearNatural F 3).prod ((linearNatural F 3).comp a.toMonoidHom))))
    (hA : IsElementaryTwo A) :
    rank A + 1 < fixedCodim (normalizerRepresentation
      ((linearNatural F 3).prod ((linearNatural F 3).comp a.toMonoidHom))) A := by
  let μ := (linearNatural F 3).prod ((linearNatural F 3).comp a.toMonoidHom)
  let τ := normalizerRepresentation μ
  let W := (Fin 3 → F.Carrier) × (Fin 3 → F.Carrier)
  let : Finite (Module.End (ZMod 2) W) := Finite.of_injective
    (fun f : Module.End (ZMod 2) W => (f : W → W)) DFunLike.coe_injective
  change rank A + 1 < fixedCodim τ A
  let : IsElementaryAbelian 2 A := hA.2
  have hlow := (doubledLinear_normalizer_moduleM F a hne).trans
    (moduleM_le_fixedCodim τ hA)
  have hr : rank A ≤ 2*F.degree := by
    have hc := (primeRank_le_iff_elementary_card_le (linearNormalizer μ)).mp
      (doubledLinear_normalizer_twoRank_le F a hne) A hA.2
    have hh := Nat.log_mono_right (b := 2) hc
    simpa only [rank,Nat.log_pow (by decide : 1 < (2:ℕ))] using hh
  by_cases hsmall : Nat.card A ≤ Nat.card F.Carrier
  · have hh := Nat.log_mono_right (b := 2) hsmall
    rw [F.card_eq,Nat.log_pow (by decide : 1 < (2:ℕ))] at hh
    change rank A ≤ F.degree at hh
    omega
  · let f := (linearNormalizer μ).subtype.comp A.subtype
    have hfi : Function.Injective f := (linearNormalizer μ).subtype_injective.comp A.subtype_injective
    have hi : Function.Injective (actionHom μ) := by
      intro g k hgk
      apply specialLinearNatural_injective 3
      apply LinearMap.ext
      intro v
      exact congrArg (fun z : actionImage μ => (z.val.val (v,0)).1) hgk
    let e := MulEquiv.ofBijective (actionHom μ) ⟨hi,μ.asGroupHom.rangeRestrict_surjective⟩
    let α := (MulAut.congr e.symm).toMonoidHom.comp
      ((actionImage μ).normalizerMonoidHom.comp A.subtype)
    have heα (x : A) (g) : e (α x g) = (actionImage μ).normalizerMonoidHom x.val (e g) := by
      change e (e.symm ((actionImage μ).normalizerMonoidHom x.val (e g))) = _
      rw [e.apply_symm_apply]
    have hf (x : A) (g) (v : W) : (f x).val (μ g v) = μ (α x g) ((f x).val v) := by
      have hh := congrArg Subtype.val (heα x g)
      change μ.asGroupHom (α x g) = (f x) * μ.asGroupHom g * (f x)⁻¹ at hh
      exact congrArg (fun z : (Module.End (ZMod 2) W)ˣ => z.val v)
        (mul_inv_eq_iff_eq_mul.mp hh.symm)
    have hsq : ∀ x : A, x^2=1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 A)
    have hc := doubledLinear_large_two_actor_fixed_card F a hne f hfi hsq α hf
      (lt_of_not_ge hsmall)
    change Nat.card (fixedSpace τ A) ≤ Nat.card F.Carrier^3 at hc
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,F.card_eq,←pow_mul] at hc
    have hfix := (Nat.pow_le_pow_iff_right (by decide : 1 < (2:ℕ))).mp hc
    have hF : Module.finrank (ZMod 2) F.Carrier=F.degree := by
      have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.Carrier)
      rw [Nat.card_zmod,F.card_eq] at hh
      exact (Nat.pow_right_injective (by decide : 1 < (2:ℕ)) hh).symm
    have hdim : Module.finrank (ZMod 2) W=6*F.degree := by
      simp [W,Module.finrank_prod,Module.finrank_pi_fintype,hF]
      omega
    have hsum := fixedCodim_add_finrank τ A
    rw [hdim] at hsum
    omega

end CFSG.Quasithin.Chapter7.NormalizedSource
