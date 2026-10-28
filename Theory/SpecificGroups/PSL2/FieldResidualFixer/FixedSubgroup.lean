module

public import Theory.SpecificGroups.PSL2.RankOneRoots
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.SemilinearCoverage
public import Mathlib.FieldTheory.Fixed
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# The full pointwise fixer of a binary PSL₂ fixed-field subgroup

Semilinear coverage writes every automorphism as an inner factor followed by
an actual coefficient automorphism. Fixing the parameter-one upper transvection
and the Weyl involution kills the inner factor. The remaining coefficient
automorphism fixes every element of the coefficient fixed field. Finite Galois
theory bounds these automorphisms by the order of the original involution.
Thus the bound includes every automorphism of the ambient projective group.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the linear-two
field row in 16.1.4(4), 16.1.7(3a), and its exclusion in 16.3.5, printed
pp.1171–1173 and 1178–1179 of `refs/quasithin.pdf`.

Adapted from the checked `LinearTwo.FieldFixer` development of task
`qt-16-03-field-component-fixer-psl2`; the original module is preserved.
This Theory extension also supplies the fixed-subgroup branch of 16.4.9(1).
-/

public section
open Subgroup Matrix BenderSuzuki.Converse BenderSuzuki.MatrixGroups BenderSuzuki.ZD.Linear

namespace Theory.PSL2.FieldResidualFixer
variable {F : Type*} [Field F] [CharP F 2]

private theorem field_uni (σ : F ≃+* F) (t : F) :
    fieldAut σ (pi F (uni t)) = pi F (uni (σ t)) := by
  rw [fieldAut_apply_pi]
  congr 1
  ext i j
  change σ ((uni t).val i j) = (uni (σ t)).val i j
  fin_cases i <;> fin_cases j <;> simp [uni]

private theorem field_weyl (σ : F ≃+* F) :
    fieldAut σ (pi F (weyl F)) = pi F (weyl F) := by
  rw [fieldAut_apply_pi]
  congr 1
  ext i j
  change σ ((weyl F).val i j) = (weyl F).val i j
  fin_cases i <;> fin_cases j <;> simp [weyl]

private theorem inner_parameter_eq_one (g : PSL2MatrixGroup F)
    (hu : g * pi F (uni 1) = pi F (uni 1) * g)
    (hw : g * pi F (weyl F) = pi F (weyl F) * g) : g = 1 := by
  have hg : g ∈ PUnip F := by
    rw [← Theory.PSL2.centralizer_root_eq (one_ne_zero : (1 : F) ≠ 0)]
    exact mem_centralizer_singleton_iff.mpr hu
  obtain ⟨A, hA, rfl⟩ := hg
  obtain ⟨t, rfl⟩ := (mem_Unip_iff A).mp hA
  have hm : uni t * weyl F = weyl F * uni t := pi_injective (by
    simpa only [map_mul] using hw)
  have ht : t = 0 := by
    have hh := congrArg (fun x : SL2 F => x.val 0 0) hm
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using hh
  simp only [ht, uni_zero, map_one]

private theorem eq_field_of_fixes_fixed [Finite F] (σ : F ≃+* F)
    (a : MulAut (PSL2MatrixGroup F))
    (ha : a ∈ fixingSubgroup (MulAut (PSL2MatrixGroup F))
      ((fieldAut σ).fixedSubgroup : Set (PSL2MatrixGroup F))) :
    ∃ τ : F ≃+* F, a = fieldAut τ ∧
      τ ∈ fixingSubgroup (F ≃+* F) (FixedBy.subfield F σ : Set F) := by
  obtain ⟨g, τ, he⟩ := semilinear_coverage a
  have hfix := (mem_fixingSubgroup_iff _).mp ha
  have hu : a (pi F (uni 1)) = pi F (uni 1) :=
    hfix _ ((MulAut.mem_fixedSubgroup _ _).mpr (by rw [field_uni, map_one]))
  have hw : a (pi F (weyl F)) = pi F (weyl F) :=
    hfix _ ((MulAut.mem_fixedSubgroup _ _).mpr (field_weyl σ))
  have hg : g = 1 := inner_parameter_eq_one g (by
    rw [he] at hu
    change g * fieldAut τ (pi F (uni 1)) * g⁻¹ = _ at hu
    rw [field_uni, map_one] at hu
    exact mul_inv_eq_iff_eq_mul.mp hu) (by
    rw [he] at hw
    change g * fieldAut τ (pi F (weyl F)) * g⁻¹ = _ at hw
    rw [field_weyl] at hw
    exact mul_inv_eq_iff_eq_mul.mp hw)
  have he' : a = fieldAut τ := by simpa only [hg, map_one, one_mul] using he
  refine ⟨τ, he', (mem_fixingSubgroup_iff _).mpr ?_⟩
  intro x hx
  change σ x = x at hx
  have hu : a (pi F (uni x)) = pi F (uni x) :=
    hfix _ ((MulAut.mem_fixedSubgroup _ _).mpr (by rw [field_uni, hx]))
  rw [he', field_uni] at hu
  have hm := pi_injective hu
  exact congrArg (fun A : SL2 F => A.val 0 1) hm

omit [CharP F 2] in
theorem field_fixer_card_le_two [Finite F] (σ : F ≃+* F)
    (hσ : orderOf σ = 2) :
    Nat.card (fixingSubgroup (F ≃+* F) (FixedBy.subfield F σ : Set F)) ≤ 2 := by
  let H := zpowers σ
  let F₀ := FixedPoints.subfield H F
  let : Finite H := Finite.of_injective
    (fun g : H => (g.val : F → F)) (fun a b h => Subtype.ext (DFunLike.coe_injective h))
  let : Fintype H := Fintype.ofFinite H
  let f : fixingSubgroup (F ≃+* F) (FixedBy.subfield F σ : Set F) → (F ≃ₐ[F₀] F) :=
    fun τ => AlgEquiv.ofRingEquiv (f := τ.val) (fun x =>
      (mem_fixingSubgroup_iff _).mp τ.property x.val
        (x.property ⟨σ, mem_zpowers σ⟩))
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    ext x
    exact DFunLike.congr_fun hab x
  calc
    _ ≤ Nat.card (F ≃ₐ[F₀] F) := Nat.card_le_card_of_injective f hf
    _ = Nat.card H := (Nat.card_congr (FixedPoints.toAlgAutMulEquiv H F).toEquiv).symm
    _ = 2 := by rw [Nat.card_zpowers, hσ]

/-- The pointwise fixer in the full automorphism group has order at most two. -/
theorem card_fixing_fixedSubgroup_le_two [Finite F] (σ : F ≃+* F)
    (hσ : orderOf σ = 2) :
    Nat.card (fixingSubgroup (MulAut (PSL2MatrixGroup F))
      ((fieldAut σ).fixedSubgroup : Set (PSL2MatrixGroup F))) ≤ 2 := by
  classical
  let : Finite (F ≃+* F) := Finite.of_injective
    (fun τ : F ≃+* F => (τ : F → F)) DFunLike.coe_injective
  let A := fixingSubgroup (MulAut (PSL2MatrixGroup F))
    ((fieldAut σ).fixedSubgroup : Set (PSL2MatrixGroup F))
  let τ : A → (F ≃+* F) := fun a => (eq_field_of_fixes_fixed σ a.val a.property).choose
  have hτ (a : A) : a.val = fieldAut (τ a) ∧
      τ a ∈ fixingSubgroup (F ≃+* F) (FixedBy.subfield F σ : Set F) :=
    (eq_field_of_fixes_fixed σ a.val a.property).choose_spec
  let f : A → fixingSubgroup (F ≃+* F) (FixedBy.subfield F σ : Set F) :=
    fun a => ⟨τ a, (hτ a).2⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    rw [(hτ a).1, (hτ b).1]
    exact congrArg fieldAut (congrArg Subtype.val hab)
  exact (Nat.card_le_card_of_injective f hf).trans (field_fixer_card_le_two σ hσ)

end Theory.PSL2.FieldResidualFixer
