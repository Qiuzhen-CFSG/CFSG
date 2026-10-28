module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.MarkedProduct.Concrete.Generation

/-!
# No strong elementary offenders on the binary orthogonal four-space

An elementary subgroup containing a plane exchange has the already established
strict fixed-vector/order bound. In the subgroup preserving both planes, the
two permutation signs are faithful: their kernel consists of cubic rotations.
The elementary subgroup therefore has order at most four. At order four it
contains an element reflecting both planes, which fixes four vectors; at order
two a nonidentity element fixes at most eight vectors. These bounds establish
the no-strong-offender inequality for every elementary action image, without
assuming an elementary lift to an ambient group.

This supplies the concrete model premise in the B.2.18 application for 15.4.12.
Source: Aschbacher--Smith, combined manuscript of 1 March 2004, B.2.18,
printed pp.80--81, and 15.4.12, printed pp.1160--1161.
-/

@[expose] public section
open Subgroup
open OrthogonalFourBinary OrthogonalFourBinary.TerminalLines OrthogonalFourBinary.SylowGeometry
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.MarkedProduct.Concrete
open FamilySource.ModuleStructure.BaumannPair

private theorem code_fixed_le_eight : ∀ i j : LineCode,
    (∃ v : Space, eval (i,j,false) v ≠ v) →
      Fintype.card {v : Space // eval (i,j,false) v = v} ≤ 8 := by decide +kernel

private theorem code_double_reflection_fixed : ∀ i j : LineCode,
    i.2 ≠ 0 → j.2 ≠ 0 →
      Fintype.card {v : Space // eval (i,j,false) v = v} = 4 := by decide +kernel

private theorem fixed_le_single (B : Subgroup OrthogonalFourBinary.IsometryGroup)
    (g : OrthogonalFourBinary.IsometryGroup) (hg : g ∈ B) :
    Nat.card (FixedVectors B) ≤ Nat.card {v : Space // g.val v = v} := by
  exact Nat.card_le_card_of_injective
    (fun v : FixedVectors B => (⟨v.val,v.property g hg⟩ : {v : Space // g.val v = v}))
    (fun a b h => Subtype.ext (congrArg (fun v : {v : Space // g.val v = v} => v.val) h))

private theorem base_nonidentity_fixed_le_eight (g : base) (hne : g.val ≠ 1) :
    Nat.card {v : Space // g.val.val v = v} ≤ 8 := by
  obtain ⟨⟨i,j,b⟩, hg⟩ := codeMap_bijective.surjective g.val
  have hb : b = false := by
    have h := (base_iff g.val).mp g.property
    rwa [←hg, show codeEquiv.symm (codeMap (i,j,b)) = (i,j,b) from
      codeEquiv.symm_apply_apply _] at h
  subst b
  rw [←hg]
  change Nat.card {v : Space // candidate (i,j,false) v = v} ≤ 8
  simp_rw [candidate_eval]
  rw [Nat.card_eq_fintype_card]
  apply code_fixed_le_eight
  by_contra! h
  apply hne
  rw [←hg]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  exact (candidate_eval (i,j,false) v).trans (h v)

private theorem double_sign_fixed_card (g : base) (hs : pairSign g = (-1,-1)) :
    Nat.card {v : Space // g.val.val v = v} = 4 := by
  obtain ⟨⟨i,j,b⟩, hg⟩ := codeMap_bijective.surjective g.val
  have hb : b = false := by
    have h := (base_iff g.val).mp g.property
    rwa [←hg, show codeEquiv.symm (codeMap (i,j,b)) = (i,j,b) from
      codeEquiv.symm_apply_apply _] at h
  subst b
  have hsign := baseEquiv_sign g
  change pairSign g = _ at hsign
  rw [hs, ←hg, show codeEquiv.symm (codeMap (i,j,false)) = (i,j,false) from
    codeEquiv.symm_apply_apply _] at hsign
  have hp : i.2 ≠ 0 ∧ j.2 ≠ 0 := by
    constructor
    · intro hi
      have hh := congrArg Prod.fst hsign
      simp [hi] at hh
    · intro hj
      have hh := congrArg Prod.snd hsign
      simp [hj] at hh
  rw [←hg]
  change Nat.card {v : Space // candidate (i,j,false) v = v} = 4
  simp_rw [candidate_eval]
  rw [Nat.card_eq_fintype_card]
  exact code_double_reflection_fixed i j hp.1 hp.2

/-- On an elementary subgroup of the base, the two signs are faithful. -/
theorem elementary_pairSign_injective
    (B : Subgroup OrthogonalFourBinary.IsometryGroup) [IsElementaryAbelian 2 B]
    (hB : B ≤ base) : Function.Injective (pairSign.comp (inclusion hB)) := by
  apply (injective_iff_map_eq_one _).mpr
  intro b hb
  have hr : b.val ∈ rotations := (pairSign_eq_one_iff (inclusion hB b)).mp hb
  have h2 : b.val ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) _ b.property
  obtain ⟨r,hr⟩ := hr
  have h3 : b.val ^ 3 = 1 := hr ▸ rotation_cube r
  apply Subtype.ext
  have hh := h3
  rw [show (3 : ℕ) = 2+1 from rfl, pow_succ, h2, one_mul] at hh
  exact hh

/-- Every elementary subgroup preserving the two planes has fixed-vector/order
product bounded by the sixteen vectors of the original natural space. -/
theorem base_elementary_fixed_bound
    (B : Subgroup OrthogonalFourBinary.IsometryGroup) [IsElementaryAbelian 2 B]
    (hB : B ≤ base) : Nat.card (FixedVectors B) * Nat.card B ≤ 16 := by
  classical
  let f := pairSign.comp (inclusion hB)
  have hf : Function.Injective f := elementary_pairSign_injective B hB
  have hu : Nat.card (ℤˣ × ℤˣ) = 4 := by rw [Nat.card_eq_fintype_card]; decide
  have hcard : Nat.card B ≤ 4 := by
    have h := Nat.card_le_card_of_injective f hf
    rwa [hu] at h
  have hdiv : Nat.card B ∣ 4 := by
    have h := Subgroup.card_dvd_of_injective f hf
    rwa [hu] at h
  by_cases hbot : B = ⊥
  · rw [hbot, card_bot, mul_one]
    have hs : Nat.card Space = 16 := by rw [Nat.card_eq_fintype_card]; decide
    rw [←hs]
    exact Nat.card_le_card_of_injective (fun v : FixedVectors (⊥ : Subgroup OrthogonalFourBinary.IsometryGroup) => v.val)
      Subtype.val_injective
  by_cases hsmall : Nat.card B ≤ 2
  · obtain ⟨g,hg⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
    have hfix := (fixed_le_single B g g.property).trans
      (base_nonidentity_fixed_le_eight ⟨g,hB g.property⟩ (fun hh => hg (Subtype.ext hh)))
    exact le_trans (Nat.mul_le_mul hfix hsmall) (by decide : 8*2≤16)
  have hfour : Nat.card B = 4 := by
    have hh : Nat.card B = 3 ∨ Nat.card B = 4 := by omega
    rcases hh with hh | hh
    · rw [hh] at hdiv
      norm_num at hdiv
    · exact hh
  have hsur : Function.Surjective f :=
    ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf,hfour.trans hu.symm⟩).2
  obtain ⟨g,hg⟩ := hsur (-1,-1)
  have hfix : Nat.card (FixedVectors B) ≤ 4 := by
    have hsingle := double_sign_fixed_card (inclusion hB g) hg
    exact (fixed_le_single B g g.property).trans_eq hsingle
  rw [hfour]
  exact le_trans (Nat.mul_le_mul_right 4 hfix) (by decide : 4*4≤16)

/-- The natural binary orthogonal four-space has no strong elementary offender. -/
theorem elementary_fixed_bound
    (B : Subgroup OrthogonalFourBinary.IsometryGroup) [IsElementaryAbelian 2 B] :
    Nat.card (FixedVectors B) * Nat.card B ≤ 16 := by
  by_cases hB : B ≤ base
  · exact base_elementary_fixed_bound B hB
  · obtain ⟨g,hg,hgn⟩ := SetLike.not_le_iff_exists.mp hB
    have hswap : (codeEquiv.symm g).2.2 = true := by
      simpa only [Bool.not_eq_false] using mt (base_iff g).mpr hgn
    exact (swapping_elementary_strict_fixed_bound B g hg hswap).le


/-- The rank formulation used in Baumann's no-strong-offender premise. -/
theorem elementary_rank_le_fixed_codim
    (B : Subgroup OrthogonalFourBinary.IsometryGroup) [IsElementaryAbelian 2 B] :
    Nat.log 2 (Nat.card B) ≤ 4 - Nat.log 2 (Nat.card (FixedVectors B)) := by
  let : Nonempty (FixedVectors B) := ⟨⟨0,by intro g _; exact map_zero g.val⟩⟩
  have hpow : 2 ^ (Nat.log 2 (Nat.card (FixedVectors B)) + Nat.log 2 (Nat.card B)) ≤
      2 ^ 4 := by
    rw [pow_add]
    exact (Nat.mul_le_mul (Nat.pow_log_le_self 2 Nat.card_pos.ne')
      (Nat.pow_log_le_self 2 Nat.card_pos.ne')).trans (elementary_fixed_bound B)
  have hsum := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hpow
  omega

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.MarkedProduct.Concrete
