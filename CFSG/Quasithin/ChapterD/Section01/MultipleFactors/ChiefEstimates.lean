module
public import CFSG.Quasithin.ChapterD.Section01.ChiefFactors
public import Theory.Representation.BinaryOffender.QuadraticImageBound
public import Stellmacher.CentralizerQuotientRepresentation

/-!
# The actual chief-factor rank estimates in D.1.3

Quadraticity descends from U to its literal group chief quotients. On each
noncentral quotient, a lower quadratic ratio of one gives the source bound
m(A/C_A(U_i)) ≤ m(U_i/C_(U_i)(A)). Identifying the relative kernel with
A ∩ R₂ makes every denominator m(A/(A ∩ R₂)), as required by D.1.3(n).
We also derive the upper estimate from maximal elementary order, rather than
postulating an offender inequality. The parabolic centralizer and ratio-one
inputs are kept explicit for the earlier-source assembly.

Source: Aschbacher--Smith, D.1.3, printed pp.173--175; the retained exact
chief-factor kernels are also used in 3.1.9(3), printed p.577.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterD.MultipleFactors
open Subgroup NoncentralChiefRefinement Representation Representation.BinaryOffender
open scoped ENNReal IsMulCommutative
variable {H : Type*} [Group H] [Finite H]
  (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]

omit [Finite H] in
/-- Quadraticity on U descends to the actual chief quotient and its action. -/
theorem chiefFactor_quadratic (s : SeriesOn U) {A : Subgroup H}
    (hquad : IsQuadratic (normalRepresentation U) A) (i : Fin s.series.length) :
    IsQuadratic (s.factorRepresentation i) A := by
  apply quadratic_of_equivariant_surjection (s.linearFactor i)
    (s.factorRepresentation i) (s.factorLinearEquiv i).toLinearMap
    (s.factorLinearEquiv i).surjective (s.factorLinearEquiv_equivariant i) A
  exact quadratic_section (normalRepresentation U) _ _ hquad

/-- The kernel on a literal noncentral chief factor supplies its rank denominator.
The two additional inputs are the earlier parabolic kernel identity and ratio bound. -/
theorem chiefFactor_rank_lower (s : SeriesOn U) (A R₂ : Subgroup H)
    [IsElementaryAbelian 2 A] (hquad : IsQuadratic (normalRepresentation U) A)
    (i : Fin s.series.length)
    (hkernel : A ⊓ (s.factorRepresentation i).ker = A ⊓ R₂)
    (hratio : 1 ≤ quadraticRatio (imageRepresentation (s.factorRepresentation i))) :
    Nat.log 2 (R₂.relIndex A) ≤ fixedCodim (s.factorRepresentation i) A := by
  have h := quadratic_image_rank_le (s.factorRepresentation i)
    (chiefFactor_quadratic U s hquad i) hratio
  have he : (s.factorRepresentation i).ker.relIndex A = R₂.relIndex A := by
    rw [← inf_relIndex_left, hkernel, inf_relIndex_left]
  rwa [he] at h

/-- Equation (n), now with local ranks constructed from the actual factor actions. -/
theorem chief_rank_lower (s : SeriesOn U) (A R₂ : Subgroup H)
    [IsElementaryAbelian 2 A] (hquad : IsQuadratic (normalRepresentation U) A)
    (hkernel : ∀ i, ¬ s.Central i → A ⊓ (s.factorRepresentation i).ker = A ⊓ R₂)
    (hratio : ∀ i, ¬ s.Central i →
      1 ≤ quadraticRatio (imageRepresentation (s.factorRepresentation i))) :
    (s.noncentralCount : ℝ) * (Nat.log 2 (R₂.relIndex A) : ℝ) ≤
      fixedCodim (normalRepresentation U) A := by
  apply qrc_chief_factor_lower U s A
  intro i hi
  exact_mod_cast chiefFactor_rank_lower U s A R₂ hquad i (hkernel i hi) (hratio i hi)

omit [Finite H] in
/-- The literal normal action has centralizer kernel. -/
theorem normalRepresentation_ker :
    (normalRepresentation U).ker = centralizer (U : Set H) := by
  ext h
  constructor
  · intro hh u hu
    have he := congrArg (fun f : Module.End (ZMod 2) (Additive U) =>
      ((f (Additive.ofMul ⟨u, hu⟩)).toMul : H)) hh
    change h * u * h⁻¹ = u at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hh
    apply LinearMap.ext
    intro u
    apply Additive.toMul.injective
    apply Subtype.ext
    change h * (u.toMul : H) * h⁻¹ = u.toMul
    rw [← hh u.toMul u.toMul.property, mul_inv_cancel_right]

/-- B.2.4.1 in the action convention of the chief filtration: maximal elementary
order bounds fixed codimension by the rank of the faithful actor image. -/
theorem maxElementary_fixedCodim_le (S A : Subgroup H) (hUS : U ≤ S)
    (hA : A ∈ Stellmacher.elementaryAbelianMaxSubgroups S) :
    fixedCodim (normalRepresentation U) A ≤
      Nat.log 2 ((centralizer (U : Set H)).relIndex A) := by
  let f := actionHom (normalRepresentation U)
  have hk : f.ker = centralizer (U : Set H) :=
    (actionHom_ker_eq _).trans (normalRepresentation_ker U)
  let σ := NormalElementaryQuotient.representation U f
    (normalRepresentation U).asGroupHom.rangeRestrict_surjective hk
  have he : ∀ g v, (LinearEquiv.refl (ZMod 2) (Additive U))
      (normalRepresentation U g v) = σ (f g)
        ((LinearEquiv.refl (ZMod 2) (Additive U)) v) := by
    intro g v
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (NormalElementaryQuotient.representation_apply U f
      (normalRepresentation U).asGroupHom.rangeRestrict_surjective hk g v).symm
  have hcod := fixedCodim_map_equivariant (normalRepresentation U) σ f
    (LinearEquiv.refl (ZMod 2) (Additive U)) he A
  by_cases htriv : A ≤ f.ker
  · have hf : fixedSpace (normalRepresentation U) A = ⊤ := by
      apply top_unique
      intro v _ a
      have ha : normalRepresentation U (a : H) = 1 := by
        have hh := htriv a.property
        rwa [actionHom_ker_eq] at hh
      exact LinearMap.congr_fun ha v
    rw [(fixedCodim_eq_zero_iff _ _).mpr hf]
    exact Nat.zero_le _
  · have h := (NormalElementaryQuotient.maxElementary_isOffender U f
      (normalRepresentation U).asGroupHom.rangeRestrict_surjective hk S A hUS hA htriv).2
    rw [← hcod] at h
    change fixedCodim (normalRepresentation U) A ≤ rank (actionSubgroup (normalRepresentation U) A) at h
    rwa [rank_actionSubgroup_eq_log_relIndex, normalRepresentation_ker] at h

omit [U.Normal] [IsElementaryAbelian 2 U] in
/-- Splitting the faithful action rank at A ∩ R₂ gives equation (l).
The centralizer containment is the earlier parabolic input. -/
theorem action_rank_decomposition (A R₂ : Subgroup H) [IsElementaryAbelian 2 A]
    (hkernel : A ⊓ centralizer (U : Set H) ≤ R₂) :
    (Nat.log 2 ((centralizer (U : Set H)).relIndex A) : ℝ) =
      (Nat.log 2 (R₂.relIndex A) : ℝ) +
        (Nat.log 2 ((centralizer (U : Set H)).relIndex (A ⊓ R₂)) : ℝ) := by
  let B := A ⊓ R₂
  let C := A ⊓ centralizer (U : Set H)
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le (inf_le_left : B ≤ A)
  have hCB : C ≤ B := le_inf inf_le_left hkernel
  have hCA := rank_sub_rank_eq_log_relIndex A C inf_le_left
  have hBA := rank_sub_rank_eq_log_relIndex A B inf_le_left
  have hBC := rank_sub_rank_eq_log_relIndex B C hCB
  have he : C.relIndex B = (centralizer (U : Set H)).relIndex B := by
    rw [← inf_relIndex_right (centralizer (U : Set H)) B]
    congr 1
    dsimp [B, C]
    apply le_antisymm
    · exact le_inf inf_le_right hCB
    · exact le_inf (inf_le_right.trans inf_le_left) inf_le_left
  rw [he] at hBC
  dsimp [C] at hCA
  dsimp [B] at hBA hBC
  rw [inf_relIndex_left] at hCA hBA
  linarith

/-- Noncontainment in the two-core gives a positive literal quotient rank. -/
theorem quotient_rank_pos (A R₂ : Subgroup H) [IsElementaryAbelian 2 A]
    (hA : ¬ A ≤ R₂) : 0 < Nat.log 2 (R₂.relIndex A) := by
  have hpos : 0 < R₂.relIndex A := by
    rw [relIndex_eq_two_pow_quotient_finrank]
    positivity
  have hne : R₂.relIndex A ≠ 1 := fun he => hA (relIndex_eq_one.mp he)
  exact Nat.log_pos Nat.one_lt_two (by omega)

/-- The replacement upper estimate (k)--(l) follows from maximal elementary order. -/
theorem maxElementary_rank_upper (S A R₂ : Subgroup H) (hUS : U ≤ S)
    (hA : A ∈ Stellmacher.elementaryAbelianMaxSubgroups S)
    (hkernel : A ⊓ centralizer (U : Set H) ≤ R₂) :
    (fixedCodim (normalRepresentation U) A : ℝ) ≤
      (Nat.log 2 (R₂.relIndex A) : ℝ) +
        (Nat.log 2 ((centralizer (U : Set H)).relIndex (A ⊓ R₂)) : ℝ) := by
  let : IsElementaryAbelian 2 A := hA.2.1
  rw [← action_rank_decomposition U A R₂ hkernel]
  exact_mod_cast maxElementary_fixedCodim_le U S A hUS hA

/-- Before using a finite real ratio, the chief estimates force B=A∩R₂
to act nontrivially on U. This is the contradiction on printed p.173. -/
theorem core_intersection_nontrivial_action (s : SeriesOn U) (S A R₂ : Subgroup H)
    (hUS : U ≤ S) (hA : A ∈ Stellmacher.elementaryAbelianMaxSubgroups S)
    (hAR : ¬ A ≤ R₂) (hc : 1 < s.noncentralCount)
    (hquad : IsQuadratic (normalRepresentation U) A)
    (hkernel : A ⊓ centralizer (U : Set H) ≤ R₂)
    (hfactor : ∀ i, ¬ s.Central i → A ⊓ (s.factorRepresentation i).ker = A ⊓ R₂)
    (hratio : ∀ i, ¬ s.Central i →
      1 ≤ quadraticRatio (imageRepresentation (s.factorRepresentation i))) :
    ¬ A ⊓ R₂ ≤ centralizer (U : Set H) := by
  let : IsElementaryAbelian 2 A := hA.2.1
  have hlo := chief_rank_lower U s A R₂ hquad hfactor hratio
  have hup := maxElementary_rank_upper U S A R₂ hUS hA hkernel
  have hpos : (0 : ℝ) < Nat.log 2 (R₂.relIndex A) := by
    exact_mod_cast quotient_rank_pos A R₂ hAR
  have hcount : (2 : ℝ) ≤ s.noncentralCount := by exact_mod_cast hc
  intro htriv
  simp only [relIndex_eq_one.mpr htriv, Nat.log_of_lt (by decide : 1 < 2), Nat.cast_zero, add_zero] at hup
  nlinarith

end CFSG.Quasithin.ChapterD.MultipleFactors
