module
public import Theory.SpecificGroups.SL2.SylowTorusAutomorphisms
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Mathlib.GroupTheory.Exponent
public import Theory.GroupTheory.SolvableOuterQuotient


/-!
# The inner kernel of a diagonal and field action

For a binary SL₂ pair, a diagonal-plus-field automorphism is inner exactly
when both coefficient automorphisms are trivial. This follows by taking
traces in each factor. The diagonal parameters on that kernel are unique
and therefore form multiplicative characters. For a faithful action the
characters are injective and the kernel exponent divides the field order
minus one, without squaring this exponent for the two factors.

The original Chapter 10 application identifies this kernel with the literal
Hall intersection with L₀. Source: Aschbacher--Smith 10.2.3, printed p.745,
the decomposition B_H = B⁺F before eliminating the field factor.
-/

public noncomputable section
open Subgroup Matrix
open scoped MatrixGroups
open BenderSuzuki.ZD.Linear
namespace Matrix.SpecialLinearGroup
variable {F : Type*} [Field F] [CharP F 2]

noncomputable def splitDiagonalHom : Fˣ →* SL(2,F) :=
  (rankOneBorel F).subtype.comp borelDiagonalHom

omit [CharP F 2] in
theorem splitDiagonalHom_apply (a : Fˣ) :
    splitDiagonalHom a = diag2 (a:F) a.ne_zero := by rfl

omit [CharP F 2] in
theorem splitDiagonalHom_injective : Function.Injective (splitDiagonalHom (F := F)) := by
  intro a b he
  apply Units.ext
  have hh := congrArg (fun g : SL(2,F) => g.val 0 0) he
  simpa [splitDiagonalHom,borelDiagonalHom,diag2_coe'] using hh

noncomputable def splitDiagonalPairAction : Fˣ × Fˣ →* MulAut (SL(2,F) × SL(2,F)) :=
  MulAut.conj.comp ((splitDiagonalHom (F := F)).prodMap splitDiagonalHom)

omit [CharP F 2] in
theorem splitDiagonalPairAction_apply (a : Fˣ × Fˣ) (x : SL(2,F) × SL(2,F)) :
    splitDiagonalPairAction a x =
      (splitDiagonalHom a.1,splitDiagonalHom a.2) * x *
        (splitDiagonalHom a.1,splitDiagonalHom a.2)⁻¹ := by rfl

theorem splitDiagonalPairAction_injective :
    Function.Injective (splitDiagonalPairAction (F := F)) := by
  have hz : center (SL(2,F) × SL(2,F)) = ⊥ := by
    rw [Subgroup.center_prod,Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot,bot_prod_bot]
  apply (Theory.GroupTheory.conj_injective_of_center_eq_bot hz).comp
  intro a b he
  exact Prod.ext (splitDiagonalHom_injective (congrArg Prod.fst he))
    (splitDiagonalHom_injective (congrArg Prod.snd he))

omit [CharP F 2] in
private theorem field_eq_one_of_diagonal_field_inner (d : Fˣ) (σ : F ≃+* F)
    (g : SL(2,F))
    (he : MulAut.conj (splitDiagonalHom d) * sl2FieldAut σ = MulAut.conj g) : σ = 1 := by
  apply Atlas.RankOneFieldAutomorphisms.field_eq_one_of_SL_inner σ
    ((splitDiagonalHom d)⁻¹*g)
  change sl2FieldAut σ = _
  rw [map_mul,map_inv]
  exact eq_inv_mul_iff_mul_eq.mpr he

variable {A : Type*} [Group A]

omit [CharP F 2] in
theorem pair_diagonal_field_inner_iff
    (ρ : A →* MulAut (SL(2,F) × SL(2,F)))
    (φ : A →* ((F ≃+* F) × (F ≃+* F)))
    (hd : ∀ b, ∃ d : Fˣ × Fˣ, ρ b =
      (MulAut.conj (splitDiagonalHom d.1) * sl2FieldAut (φ b).1).prodCongr
        (MulAut.conj (splitDiagonalHom d.2) * sl2FieldAut (φ b).2)) (b : A) :
    φ b = 1 ↔ ρ b ∈ MulAut.innerSubgroup (SL(2,F) × SL(2,F)) := by
  obtain ⟨d,hd⟩ := hd b
  constructor
  · intro hb
    refine ⟨(splitDiagonalHom d.1,splitDiagonalHom d.2),?_⟩
    rw [hd,hb]
    ext x <;> rfl
  · rintro ⟨g,hg⟩
    have h1 : MulAut.conj (splitDiagonalHom d.1) * sl2FieldAut (φ b).1 =
        MulAut.conj g.1 := by
      apply MulEquiv.ext
      intro x
      have hh := congrArg Prod.fst (MulEquiv.congr_fun (hd.symm.trans hg.symm) (x,1))
      exact hh
    have h2 : MulAut.conj (splitDiagonalHom d.2) * sl2FieldAut (φ b).2 =
        MulAut.conj g.2 := by
      apply MulEquiv.ext
      intro x
      have hh := congrArg Prod.snd (MulEquiv.congr_fun (hd.symm.trans hg.symm) (1,x))
      exact hh
    exact Prod.ext (field_eq_one_of_diagonal_field_inner d.1 (φ b).1 g.1 h1)
      (field_eq_one_of_diagonal_field_inner d.2 (φ b).2 g.2 h2)

theorem exists_pair_field_kernel_characters
    (ρ : A →* MulAut (SL(2,F) × SL(2,F)))
    (φ : A →* ((F ≃+* F) × (F ≃+* F)))
    (hd : ∀ b, ∃ d : Fˣ × Fˣ, ρ b =
      (MulAut.conj (splitDiagonalHom d.1) * sl2FieldAut (φ b).1).prodCongr
        (MulAut.conj (splitDiagonalHom d.2) * sl2FieldAut (φ b).2)) :
    ∃ χ : φ.ker →* Fˣ × Fˣ,
      (splitDiagonalPairAction (F := F)).comp χ = ρ.comp φ.ker.subtype := by
  classical
  have hex (b : φ.ker) : ∃ d : Fˣ × Fˣ, splitDiagonalPairAction d = ρ b := by
    obtain ⟨d,he⟩ := hd b
    refine ⟨d,?_⟩
    rw [he,show φ b = 1 from b.property]
    ext x <;> rfl
  let χ : φ.ker →* Fˣ × Fˣ := {
    toFun b := (hex b).choose
    map_one' := by
      apply splitDiagonalPairAction_injective
      rw [(hex 1).choose_spec,map_one]
      exact ρ.map_one
    map_mul' b c := by
      apply splitDiagonalPairAction_injective
      rw [(hex (b*c)).choose_spec,map_mul,(hex b).choose_spec,(hex c).choose_spec]
      exact ρ.map_mul b c }
  exact ⟨χ,MonoidHom.ext (fun b => (hex b).choose_spec)⟩

omit [CharP F 2] in
theorem pair_field_kernel_characters_injective
    (ρ : A →* MulAut (SL(2,F) × SL(2,F))) (hi : Function.Injective ρ)
    (φ : A →* ((F ≃+* F) × (F ≃+* F)))
    (χ : φ.ker →* Fˣ × Fˣ)
    (hχ : (splitDiagonalPairAction (F := F)).comp χ = ρ.comp φ.ker.subtype) :
    Function.Injective χ := by
  intro a b he
  apply Subtype.ext
  apply hi
  have hh := congrArg (splitDiagonalPairAction (F := F)) he
  exact (DFunLike.congr_fun hχ a).symm.trans (hh.trans (DFunLike.congr_fun hχ b))

omit [CharP F 2] in
theorem pair_field_kernel_exponent_dvd [Finite F]
    (ρ : A →* MulAut (SL(2,F) × SL(2,F))) (hi : Function.Injective ρ)
    (φ : A →* ((F ≃+* F) × (F ≃+* F)))
    (χ : φ.ker →* Fˣ × Fˣ)
    (hχ : (splitDiagonalPairAction (F := F)).comp χ = ρ.comp φ.ker.subtype) :
    Monoid.exponent φ.ker ∣ Nat.card F - 1 := by
  have h := Monoid.exponent_dvd_of_monoidHom χ
    (pair_field_kernel_characters_injective ρ hi φ χ hχ)
  rw [Monoid.exponent_prod] at h
  change Monoid.exponent φ.ker ∣ Nat.lcm (Monoid.exponent Fˣ) (Monoid.exponent Fˣ) at h
  rw [Nat.lcm_self] at h
  exact h.trans (by simpa only [Nat.card_units] using Group.exponent_dvd_nat_card (G := Fˣ))
end Matrix.SpecialLinearGroup
