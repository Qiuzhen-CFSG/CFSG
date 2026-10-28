module

public import Theory.GroupAction.CubicBorelRigidity
public import Theory.SpecificGroups.SL2.EvenBorelResidual.Semilinear
public import Theory.GroupTheory.PCoreImage
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.SemilinearCoverage

/-!
# Cubic Borel rigidity for binary projective linear groups

For a finite field of order `2^e`, `e ≥ 2`, every cubic automorphism of the
actual projective special linear group which fixes a Sylow two-subgroup and
is trivial on its normalizer quotient is trivial.  Sylow conjugacy aligns the
specified Sylow with the upper Borel; semilinear coverage then separates the
field actor from the inner actor.  The three-free normalizer forces the field
actor to fix the residual torus, and the remaining inner actor has order both
three and prime to three.

Source: Aschbacher--Smith, proof of 15.3.49(k), printed p.1144.
-/

@[expose] public section

open scoped MatrixGroups
open Subgroup BenderSuzuki.Converse Atlas

namespace Matrix.ProjectiveSpecialLinearGroup
open OddBorel
open EvenBorelResidual
open EvenBorelResidual.Semilinear

private theorem benderFieldAut_eq_fieldEquiv {F : Type*} [Field F] [CharP F 2]
    (σ : F ≃+* F) :
    BenderSuzuki.ZD.Linear.fieldAut σ = Atlas.fieldEquivPSL 2 σ := by
  ext x
  obtain ⟨g, rfl⟩ := _root_.BenderSuzuki.Converse.pi_surjective x
  rw [BenderSuzuki.ZD.Linear.fieldAut_apply_pi]
  change _ = Atlas.fieldEquivPSL 2 σ (QuotientGroup.mk' _ g)
  rw [Atlas.fieldEquivPSL_mk]
  rfl

private theorem three_residual_units_eq_top {F : Type*} [Field F] [Finite F]
    (hcop : Nat.Coprime 3 (Nat.card F - 1)) :
    pResidual 3 Fˣ = ⊤ := by
  apply (pResidual_eq_top_iff 3 Fˣ).mpr
  intro N hN hP
  apply top_unique
  have hcard : Nat.card (Fˣ ⧸ N) ∣ Nat.card Fˣ := by
    exact Subgroup.card_quotient_dvd_card N
  have hpow : ∃ k : ℕ, Nat.card (Fˣ ⧸ N) = 3 ^ k := by
    let : Fact (Nat.Prime 3) := ⟨by decide⟩
    exact (IsPGroup.iff_card.mp hP)
  obtain ⟨k, hk⟩ := hpow
  by_cases hk0 : k = 0
  · intro x _
    have hqone : Nat.card (Fˣ ⧸ N) = 1 := by simpa [hk0] using hk
    have hsub : Subsingleton (Fˣ ⧸ N) :=
      (Nat.card_eq_one_iff_unique.mp hqone).1
    apply (QuotientGroup.eq_one_iff x).mp
    exact Subsingleton.elim _ _
  · have hcardUnits : Nat.card Fˣ = Nat.card F - 1 := by
      rw [Nat.card_units]
    have h3quot : 3 ∣ Nat.card (Fˣ ⧸ N) := by
      rw [hk]
      exact dvd_pow_self 3 hk0
    have h3q : 3 ∣ Nat.card Fˣ := h3quot.trans hcard
    have h3minus : 3 ∣ Nat.card F - 1 := by simpa [hcardUnits] using h3q
    have hgcd : 3 ∣ Nat.gcd 3 (Nat.card F - 1) :=
      Nat.dvd_gcd (dvd_refl 3) h3minus
    rw [hcop.gcd_eq_one] at hgcd
    omega

/-- Cubic Borel rigidity for the actual binary projective special linear group. -/
theorem cubicBorelRigid (F : Type*) [Field F] [Finite F] (e : ℕ) (_he : 2 ≤ e)
    (hF : Nat.card F = 2 ^ e) :
    MulAut.CubicBorelRigid (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
  let _ := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  intro P hN α hα hP hB
  have hPmap : (P : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)).map
      α.toMonoidHom = P := by
    have hle : (P : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)).map
        α.toMonoidHom ≤ P := by
      rintro _ ⟨x, hx, rfl⟩
      exact hP x hx
    let Q : Sylow 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
      P.mapSurjective (f := α.toMonoidHom) α.surjective
    have hQ : (Q : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) =
        (P : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)).map α.toMonoidHom := rfl
    have hmax : (P : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) = Q :=
      Q.is_maximal' P.isPGroup' (by simpa [hQ] using hle)
    exact hQ.symm.trans hmax.symm
  have hcoverage : ∀ β : MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F),
      ∃ (g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) (σ : F ≃+* F),
        β = MulAut.conj g * Atlas.fieldEquivPSL 2 σ := by
    intro β
    obtain ⟨g, σ, hg⟩ := BenderSuzuki.ZD.Linear.semilinear_coverage β
    refine ⟨g, σ, hg.trans ?_⟩
    rw [benderFieldAut_eq_fieldEquiv]
  obtain ⟨c, g, σ, hcU, hcB, hβ⟩ :=
    aligned_semilinear_of_coverage F P α hPmap hcoverage
  let N := normalizer (P : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))
  let B := borel F
  let e₀ := MulAut.conj c
  let β := MulAut.congr e₀.symm α
  have hβpow : β ^ 3 = 1 := by
    dsimp [β]
    rw [← map_pow, hα, map_one]
  have hcore : N.pCoreIn 2 = (P : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) := by
    exact sylowNormalizer_twoCoreIn F hF P
  have hfixN : FixesResidualTorus N α := by
    intro x hx
    have hxN : x ∈ N := by
      apply (show (pResidual 3 N).map N.subtype ⊔ N.pCoreIn 2 ≤ N from
        sup_le (map_subtype_le _) (pCoreIn_le 2 N))
      exact hx
    have hδ : α x * x⁻¹ ∈ N.pCoreIn 2 := by
      rw [hcore]
      exact hB x hxN
    have hnormCore : N ≤ normalizer (N.pCoreIn 2 : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) :=
      N.le_normalizer.trans
        (Subgroup.normalizer_le_normalizer_characteristic_image N (pCore 2 N))
    have hxnorm : x⁻¹ ∈ normalizer (N.pCoreIn 2 : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) :=
      hnormCore (N.inv_mem hxN)
    have hc := ((mem_normalizer_iff.mp hxnorm) (α x * x⁻¹)).mp hδ
    simpa [mul_assoc] using hc
  have hcong : MulAut.congr e₀ β = α := by
    dsimp [β]
    change (MulAut.congr e₀) ((MulAut.congr e₀).symm α) = α
    exact (MulAut.congr e₀).apply_symm_apply α
  have hfixB : FixesResidualTorus B β := by
    apply (fixesResidualTorus_map_iff e₀ B β).mp
    rw [hcB, hcong]
    exact hfixN
  have hcardBN : Nat.card B = Nat.card N := by
    let eB : B ≃* N :=
      (equivMapOfInjective B e₀.toMonoidHom e₀.injective).trans
        (MulEquiv.subgroupCongr hcB)
    exact Nat.card_congr eB.toEquiv
  have hthreeB : ¬ 3 ∣ Nat.card B := by
    intro hd
    apply hN
    rwa [← hcardBN]
  have hnot : ¬ 3 ∣ Nat.card F - 1 := by
    intro hd
    apply hthreeB
    rw [card_borel]
    exact dvd_mul_of_dvd_right hd _
  have hcop : Nat.Coprime 3 (Nat.card F - 1) :=
    (Nat.prime_three.coprime_iff_not_dvd).mpr hnot
  have hres : pResidual 3 Fˣ = ⊤ := three_residual_units_eq_top hcop
  have hfixActor : FixesResidualTorus B (MulAut.conj (g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) *
      Atlas.fieldEquivPSL 2 σ) := by
    rw [← hβ]
    exact hfixB
  have hunits : ∀ u ∈ pResidual 3 Fˣ, Units.map σ.toMonoidHom u = u :=
    (fixesResidualTorus_iff F hF g σ).mp hfixActor
  have hσ : σ = 1 := by
    ext x
    by_cases hx : x = 0
    · subst x
      exact map_zero _
    · have hu := hunits (Units.mk0 x hx) (by rw [hres]; trivial)
      exact congrArg Units.val hu
  have hfieldone : Atlas.fieldEquivPSL 2 (1 : F ≃+* F) = 1 := by
    change Atlas.RankOneFieldAutomorphisms.pslFieldAction (1 : F ≃+* F) = 1
    exact Atlas.RankOneFieldAutomorphisms.pslFieldAction.map_one
  have hβinner : β = MulAut.conj (g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
    dsimp [β, e₀]
    rw [hβ, hσ, hfieldone, mul_one]
  have hconjpow : MulAut.conj (g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) ^ 3 = 1 := by
    rw [← hβinner, hβpow]
  have hgcenter : (g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) ^ 3 ∈
      Subgroup.center (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
    rw [mem_center_iff]
    intro x
    have hh : MulAut.conj ((g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) ^ 3) = 1 := by
      rw [map_pow, hconjpow]
    have hx := MulEquiv.congr_fun hh x
    change (g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) ^ 3 * x *
      ((g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) ^ 3)⁻¹ = x at hx
    exact (mul_inv_eq_iff_eq_mul.mp hx).symm
  have hg3 : (g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) ^ 3 = 1 := by
    simpa only [Atlas.RankOneFieldAutomorphisms.psl_center_eq_bot, mem_bot] using hgcenter
  have horder3 : orderOf (g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one hg3
  have horderB : orderOf (g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) ∣ Nat.card B := by
    exact Subgroup.orderOf_dvd_natCard B g.property
  have hgorder : orderOf (g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) = 1 := by
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp horder3 with h1 | h3
    · exact h1
    · exfalso
      apply hthreeB
      exact h3 ▸ horderB
  have hg1 : (g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) = 1 :=
    orderOf_eq_one_iff.mp hgorder
  have hβone : β = 1 := by
    rw [hβinner, hg1]
    ext x
    simp
  have hαone : α = 1 := by
    calc
      α = MulAut.congr e₀ β := hcong.symm
      _ = MulAut.congr e₀ 1 := by rw [hβone]
      _ = 1 := map_one _
  exact hαone

end Matrix.ProjectiveSpecialLinearGroup
