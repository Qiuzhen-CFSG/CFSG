module
public import Theory.SpecificGroups.SL2.SylowNormalizerTorusAction
public import Theory.SpecificGroups.SL2.NormalBorelCore
public import Theory.FieldTheory.ScalarTwistedFixedPoints.Triangular

/-!
# Quintic detection of the field part in degree four

Five distinct units fixed by a field automorphism of F₁₆ force it to be
trivial: a proper fixed field has at most four elements. Consequently a
Sylow-preserving automorphism of PSL₂(16) whose displacements on an actual
order-five Borel subgroup lie in the Sylow subgroup is inner. The original
Sylow and order-five subgroup are retained throughout.

This is the field detector needed to identify O₂(XT) in the final branch
of Aschbacher--Smith 6.1.4, printed p.665. The ambient core identity is a
separate application.
-/

public noncomputable section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {F : Type*} [Field F] [Finite F]

/-- Five fixed units detect every automorphism of the field of order sixteen. -/
theorem field_sixteen_eq_one_of_five_fixed_units
    {D : Type*} [Finite D] (hF : Nat.card F = 16) (hD : Nat.card D = 5)
    (f : D → Fˣ) (hf : Function.Injective f) (σ : F ≃+* F)
    (hfix : ∀ d, Units.map σ.toMonoidHom (f d) = f d) : σ = 1 := by
  by_contra hne
  let j : D → FixedBy.subfield F σ := fun d =>
    ⟨f d,congrArg Units.val (hfix d)⟩
  have hj : Function.Injective j := by
    intro d e he
    exact hf (Units.ext (congrArg Subtype.val he))
  have hc := Nat.card_le_card_of_injective j hj
  rw [hD] at hc
  have hs := FiniteField.card_fixed_sq_le σ hne
  rw [hF] at hs
  nlinarith

variable [CharP F 2]

/-- In PSL₂(16), a Sylow-preserving actor trivial on the quintic torus
modulo the original Sylow has no field part. -/
theorem quintic_sylow_displacements_inner
    (hF : Nat.card F = 16) (S : Sylow 2 PSL(2,F))
    (D : Subgroup PSL(2,F)) (hD : Nat.card D = 5)
    (hDN : D ≤ normalizer (S : Set PSL(2,F)))
    (a : MulAut PSL(2,F)) (ha : (S : Subgroup PSL(2,F)).map a.toMonoidHom = S)
    (hfix : ∀ d ∈ D, d⁻¹ * a d ∈ (S : Subgroup PSL(2,F))) :
    ∃ g, a = MulAut.conj g := by
  let e := (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).symm
  let b := MulAut.congr e a
  have hb (x : PSL(2,F)) : e (a x) = b (e x) := by
    change e (a x) = e (a (e.symm (e x)))
    rw [e.symm_apply_apply]
  obtain ⟨f,σ,hf,hker,hact⟩ :=
    Matrix.SpecialLinearGroup.exists_sylowNormalizer_torus_action
      e.toMonoidHom e.surjective S
      (by rw [(MonoidHom.ker_eq_bot_iff _).mpr e.injective]; exact bot_le) a b hb ha
  let N := normalizer (S : Set PSL(2,F))
  have hNa : N.map a.toMonoidHom = N := by
    change (normalizer ((S : Subgroup PSL(2,F)) : Set PSL(2,F))).map a.toMonoidHom = _
    rw [map_normalizer_eq_of_bijective (S : Subgroup PSL(2,F)) (f := a.toMonoidHom) a.bijective,ha]
    rfl
  let aN : MulAut N := (a.subgroupMap N).trans (MulEquiv.subgroupCongr hNa)
  let fD : D →* Fˣ := f.comp (inclusion hDN)
  have hdis : Disjoint (S : Subgroup PSL(2,F)) D := by
    obtain ⟨k,hk⟩ := S.isPGroup'.exists_card_eq
    exact disjoint_of_coprime_natCard (by rw [hk,hD]; exact (by decide : Nat.Coprime 2 5).pow_left k)
  have hfD : Function.Injective fD := by
    apply (injective_iff_map_eq_one _).mpr
    intro d hd
    apply Subtype.ext
    exact disjoint_def.mp hdis ((hker (inclusion hDN d)).mp hd) d.property
  have hσ : σ = 1 := by
    apply field_sixteen_eq_one_of_five_fixed_units hF hD fD hfD σ
    intro d
    let x : N := inclusion hDN d
    have hy := (hker (x⁻¹ * aN x)).mpr (hfix d d.property)
    rw [map_mul,map_inv,inv_mul_eq_one] at hy
    have hh := hact x (aN x) rfl
    exact hh.symm.trans hy.symm
  apply Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.Semilinear.inner_of_sylow_borel_quotient_fixed
    (n := 4) (by simpa using hF) S a ha
  intro x hx
  let xx : N := ⟨x,hx⟩
  have hh := hact xx (aN xx) rfl
  have he : f (aN xx) = f xx := by
    rw [hσ] at hh
    exact hh
  apply (hker (xx⁻¹ * aN xx)).mp
  rw [map_mul,map_inv,he,inv_mul_cancel]

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
