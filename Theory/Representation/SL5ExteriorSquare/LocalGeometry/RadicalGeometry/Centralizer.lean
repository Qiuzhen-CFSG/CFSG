module
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.RadicalGeometry.Centralizer.Matrix
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.ModuleFactors.NaturalFour
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Shear conjugation and the literal centralizer quotient

The four-space parabolic conjugates last-column shears through its actual
natural action on Γ₄; the same action occurs on V/V₆. The pointwise
centralizer C of V₃ + V₃' has quotient C/U ≃ F₂, whose nonidentity element
sends e₄ to e₄ + e₁. Finally the index bound |A:A∩U| ≤ 2 and the source
small-index fixed-space property force A to centralize V₆, hence A ≤ U.
No identification of U with a two-core is needed here.

Source: Aschbacher--Smith 12.5.7 and 12.5.10, printed pp.820--821
(PDF pp.837--838), with the fixed-space clause of E.3.8.
-/

@[expose] public section
namespace Representation.SL5ExteriorSquare
open SL5TenDimensional
open scoped BigOperators

/-- The bottom row of an element of the four-space parabolic is e₅ᵀ. -/
theorem parabolic_four_last_row (g : Group) (hg : g ∈ parabolic 4) :
    ∀ j : Fin 5, g.val 4 j = if j = 4 then 1 else 0 := by
  have hlow := (mem_parabolic_iff_lowerLeft_zero 4 g).mp hg
  have hdne : g.val 4 4 ≠ 0 := by
    intro hd
    apply g.row_ne_zero 4
    funext j
    fin_cases j <;> simp [hlow, hd]
  have hd : g.val 4 4 = 1 :=
    ((by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) _).resolve_left hdne
  intro j
  fin_cases j <;> simp [hlow, hd]

/-- Conjugation on U is the upper-left block of the natural action. -/
theorem parabolic_conjugate_shear (g : Group) (hg : g ∈ parabolic 4)
    (u : ShearParameter) :
    g * shear u * g⁻¹ = shear ((upperLeft g).mulVec u) := by
  have hm : g * shear u = shear ((upperLeft g).mulVec u) * g := by
    have hl := parabolic_four_last_row g hg
    apply Subtype.ext
    ext i j
    change (∑ k, g.val i k * (shear u).val k j) =
      ∑ k, (shear ((upperLeft g).mulVec u)).val i k * g.val k j
    simp only [matrix_shear]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, upperLeft, hl] <;> ring
  rw [hm, mul_assoc, mul_inv_cancel, mul_one]

/-- The existing natural-flag chart sends shear parameters to their literal vectors. -/
theorem shearNatural_eq_flagEquiv (u : ShearParameter) :
    shearNatural u = ((naturalFlagEquiv 4 (by decide)).symm u).val := by
  ext i
  fin_cases i <;> simp [shearNatural, naturalFlagEquiv]

/-- The parameter action is the actual action on Γ₄ in the natural module. -/
theorem natural_action_shearNatural (g : Group) (hg : g ∈ parabolic 4)
    (u : ShearParameter) :
    specialLinearNatural 5 g (shearNatural u) = shearNatural ((upperLeft g).mulVec u) := by
  have hl := parabolic_four_last_row g hg
  change g.val.mulVec (shearNatural u) = _
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, shearNatural, upperLeft, hl]

/-- V/V₆ carries the same actual natural action as the shear parameters. -/
theorem parabolic_shearQuotient_action (g : Group) (hg : g ∈ parabolic 4) (v : V) :
    shearQuotient (exteriorAction 2 g v) = (upperLeft g).mulVec (shearQuotient v) := by
  exact shearQuotient_action g hg v

/-- The nontrivial coset representative acts by e₄ ↦ e₄ + e₁ on Γ₄. -/
theorem tau_natural_action (u : ShearParameter) :
    specialLinearNatural 5 tau (shearNatural u) =
      shearNatural ![u 0 + u 3, u 1, u 2, u 3] := by
  change tau.val.mulVec _ = _
  rw [tau_matrix]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, shearNatural]

theorem tau_mem_C : tau ∈ C := by
  constructor
  · apply (mem_parabolic_iff_lowerLeft_zero 4 tau).mpr
    intro i j hi hj
    rw [tau_matrix]
    fin_cases i <;> fin_cases j <;> simp_all
  · have hf : V₃ ⊔ V₃' ≤ fixedSpace tau := by
      rw [V₃, V₃', ← coordinateSpan_union]
      apply Submodule.span_le.mpr
      rintro v ⟨i, hi, rfl⟩
      apply (mem_fixedSpace tau (basis i)).mpr
      apply coordinates.injective
      rw [coordinates_action, coordinates_basis]
      ext j
      fin_cases i <;> simp_all
      all_goals fin_cases j <;> simp [actionMatrix, tau_matrix, pair]
    intro v hv
    exact (mem_fixedSpace _ _).mp (hf hv)

/-- The single nontrivial upper-left entry is the quotient homomorphism C → F₂. -/
def centralizerBit : C →* Multiplicative (ZMod 2) where
  toFun g := Multiplicative.ofAdd (g.val.val 0 3)
  map_one' := by rfl
  map_mul' g h := by
    change (g.val * h.val).val 0 3 = g.val.val 0 3 + h.val.val 0 3
    rcases C_eq_shear_or_shear_mul_tau g g.property with hg | hg <;>
      rcases C_eq_shear_or_shear_mul_tau h h.property with hh | hh <;>
      rw [hg, hh]
    all_goals simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
    all_goals simp [matrix_shear, tau_matrix, Fin.sum_univ_succ]

@[simp] theorem centralizerBit_tau :
    centralizerBit ⟨tau, tau_mem_C⟩ = Multiplicative.ofAdd 1 := by
  change tau.val 0 3 = 1
  simp [tau_matrix]

theorem centralizerBit_surjective : Function.Surjective centralizerBit := by
  intro c
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) c.toAdd with hc | hc
  · refine ⟨1, ?_⟩
    rw [map_one]
    exact congrArg Multiplicative.ofAdd hc.symm
  · exact ⟨⟨tau, tau_mem_C⟩, centralizerBit_tau.trans (congrArg Multiplicative.ofAdd hc.symm)⟩

/-- The kernel is literally U as a subgroup of C. -/
theorem centralizerBit_ker : centralizerBit.ker = shearSubgroup.subgroupOf C := by
  ext g
  change g.val.val 0 3 = 0 ↔ g.val ∈ shearSubgroup
  constructor
  · intro hz
    rcases C_eq_shear_or_shear_mul_tau g g.property with hg | hg
    · exact (mem_shearSubgroup _).mpr ⟨_, hg.symm⟩
    · rw [hg] at hz
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply] at hz
      simp [matrix_shear, tau_matrix, Fin.sum_univ_succ] at hz
  · intro hg
    obtain ⟨u, hu⟩ := (mem_shearSubgroup _).mp hg
    rw [← hu, matrix_shear]
    rfl

instance shearSubgroup_normal_in_C : (shearSubgroup.subgroupOf C).Normal := by
  rw [← centralizerBit_ker]
  infer_instance

/-- The literal centralizer quotient has order two. -/
noncomputable def centralizerQuotientEquiv :
    (C ⧸ shearSubgroup.subgroupOf C) ≃* Multiplicative (ZMod 2) :=
  (QuotientGroup.quotientMulEquivOfEq centralizerBit_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective centralizerBit centralizerBit_surjective)

@[simp] theorem centralizerQuotientEquiv_mk (g : C) :
    centralizerQuotientEquiv (QuotientGroup.mk g) = centralizerBit g := rfl

/-- Every coset acts on Γ₄ by its quotient bit, so the nonidentity quotient
class is precisely the transvection e₄ ↦ e₄ + e₁. -/
theorem centralizer_quotient_natural_action (g : C) (u : ShearParameter) :
    specialLinearNatural 5 g.val (shearNatural u) =
      shearNatural ![u 0 + (centralizerQuotientEquiv (QuotientGroup.mk g)).toAdd * u 3,
        u 1, u 2, u 3] := by
  rw [natural_action_shearNatural g.val g.property.1, centralizerQuotientEquiv_mk]
  change shearNatural ((upperLeft g.val).mulVec u) =
    shearNatural ![u 0 + g.val.val 0 3 * u 3, u 1, u 2, u 3]
  congr 1
  rcases C_eq_shear_or_shear_mul_tau g.val g.property with hg | hg <;> rw [hg]
  all_goals
    ext i
    simp only [Matrix.mulVec, dotProduct]
    simp only [upperLeft, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
    fin_cases i <;> simp [matrix_shear, tau_matrix, Fin.sum_univ_succ]

/-- The unique nonidentity quotient element sends the fourth natural basis
vector to its sum with the first, using the literal quotient map. -/
theorem nonidentity_centralizer_quotient_action (g : C)
    (hg : (QuotientGroup.mk g : C ⧸ shearSubgroup.subgroupOf C) ≠ 1) :
    specialLinearNatural 5 g.val (shearNatural (Pi.single 3 1)) =
      shearNatural (Pi.single 3 1 + Pi.single 0 1) := by
  have hn : (centralizerQuotientEquiv (QuotientGroup.mk g)).toAdd ≠ 0 := by
    intro hz
    apply hg
    apply centralizerQuotientEquiv.injective
    rw [map_one]
    exact congrArg Multiplicative.ofAdd hz
  have ho : (centralizerQuotientEquiv (QuotientGroup.mk g)).toAdd = 1 :=
    ((by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) _).resolve_left hn
  rw [centralizer_quotient_natural_action, ho]
  congr 1
  ext i
  fin_cases i <;> simp

theorem shear_relIndex_C : shearSubgroup.relIndex C = 2 := by
  change Nat.card (C ⧸ shearSubgroup.subgroupOf C) = 2
  rw [Nat.card_congr centralizerQuotientEquiv.toEquiv]
  exact Nat.card_zmod 2

/-- The index used in E.3.8 is the literal relative index of A ∩ U in A. -/
theorem inf_shear_relIndex_le_two {A : Subgroup Group} (hA : A ≤ C) :
    (A ⊓ shearSubgroup).relIndex A ≤ 2 := by
  rw [Subgroup.inf_relIndex_left]
  have hn : shearSubgroup.relIndex C ≠ 0 := by rw [shear_relIndex_C]; decide
  have hi : shearSubgroup.relIndex A ≤ shearSubgroup.relIndex C :=
    Subgroup.relIndex_le_of_le_right (H := shearSubgroup) (K := A) (L := C) hA hn
  simpa only [shear_relIndex_C] using hi

/-- The A₂ fixed-space clause forces A into U. This applies in particular to
source elementary abelian subgroups, without any offender inequality. -/
theorem le_shearSubgroup_of_smallIndex_two {A : Subgroup Group}
    (hA : A ≤ C) (hfixed : HasSmallIndexFixedSpaceProperty 2 A) : A ≤ shearSubgroup := by
  have hi := inf_shear_relIndex_le_two hA
  have hlog : Nat.log 2 ((A ⊓ shearSubgroup).relIndex A) < 2 :=
    Nat.log_lt_of_lt_pow' (by decide) (by omega)
  have he := hfixed (A ⊓ shearSubgroup) inf_le_left hlog
  have hv : V₆ ≤ BinaryOffender.fixedSpace (exteriorAction 2) A := by
    rw [he, ← fixedSpace_shearSubgroup]
    intro v hv b
    exact hv ⟨b.val, b.property.2⟩
  intro g hg
  rw [← pointwiseV₆_eq_shearSubgroup]
  refine ⟨(hA hg).1, ?_⟩
  intro v hv6
  exact hv hv6 ⟨g, hg⟩

end Representation.SL5ExteriorSquare
