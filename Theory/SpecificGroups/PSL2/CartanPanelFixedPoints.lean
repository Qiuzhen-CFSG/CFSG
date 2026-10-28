module
public import Theory.GroupAction.CartanPanelFixedPoints.Supplements
public import Theory.SpecificGroups.SL2.EvenBorelResidual
public import BenderSuzuki.External.Huppert.II.theorem_6_14
public import Mathlib.GroupTheory.IsPerfect

/-!
# Cartan fixed pairs in even PSL₂

A nonidentity diagonal unit in characteristic two has distinct eigenvalues,
so its only projective fixed points are the two coordinate lines. Its
conjugation action on the upper root group is fixed-point-free. The finite
commutator bijection then places a conjugate of this element in any supplied
Borel supplement. The actual orbit map and Sylow conjugacy yield the
left-coset theorem for arbitrary Sylows and complements.

Perfectness excludes the field of order two: the actual PSL₂(2) isomorphism
with S₃ would give a nontrivial sign character of a perfect group.
Source: the elementary rank-one matrix calculation, with Huppert II.6.14(1)
for the small model; the Borel conventions are those of `EvenBorelResidual`.
-/

public section
open BenderSuzuki.Converse Matrix Projectivization
open scoped LinearAlgebra.Projectivization MatrixGroups
namespace Theory.PSL2.CartanPanel
variable {F : Type*} [Field F]

/-- A determinant-one diagonal matrix with distinct entries fixes just the two coordinate points. -/
theorem diagonal_fixed_pair (a : Fˣ) (ha : (a : F) ≠ (a : F)⁻¹) (ω : P1 F) :
    tor a • ω = ω ↔ ω = pInf F ∨ ω = pZero F := by
  constructor
  · induction ω using Projectivization.ind with | h v hv =>
      intro h
      rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff'] at h
      obtain ⟨c, hc⟩ := h
      have h0 : c * v 0 = (a : F) * v 0 := by
        simpa [BenderSuzuki.Converse.smul_eq_mulVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hc 0
      have h1 : c * v 1 = (a : F)⁻¹ * v 1 := by
        simpa [BenderSuzuki.Converse.smul_eq_mulVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hc 1
      by_cases hv1 : v 1 = 0
      · left
        rw [pInf, Projectivization.mk_eq_mk_iff']
        refine ⟨v 0, ?_⟩
        funext i
        fin_cases i <;> simp [hv1]
      · have hc' : c = (a : F)⁻¹ := mul_right_cancel₀ hv1 h1
        have hv0 : v 0 = 0 := by
          have he : ((a : F)⁻¹ - (a : F)) * v 0 = 0 := by
            rw [sub_mul, ← h0, hc', sub_self]
          exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr ha.symm)
        right
        rw [pZero, Projectivization.mk_eq_mk_iff']
        refine ⟨v 1, ?_⟩
        funext i
        fin_cases i <;> simp [hv0]
  · have ht : tor a ∈ Torus F := by rw [Torus_eq_range]; exact ⟨a, rfl⟩
    rintro (rfl | rfl)
    · exact ht.1
    · exact ht.2

variable [CharP F 2]
/-- In characteristic two every nonidentity field unit has distinct diagonal eigenvalues. -/
theorem diagonal_distinct (a : Fˣ) (ha : a ≠ 1) : (a : F) ≠ (a : F)⁻¹ := by
  intro he
  have hs : (a : F)^2 = 1^2 := by
    calc
      (a : F)^2 = (a : F)⁻¹ * (a : F) := by
        rw [pow_two]
        exact congrArg (fun x : F => x * (a : F)) he
      _ = 1^2 := by rw [inv_mul_cancel₀ a.ne_zero, one_pow]
  exact ha (Units.ext (CharTwo.sq_injective hs))


variable [Finite F]
open Theory.CartanPanel Matrix.ProjectiveSpecialLinearGroup
open OddBorel EvenBorelResidual

/-- The supplied complement contains a sharp fixed-pair element on the natural projective line. -/
theorem supplement_two_fixed (hq : 2 < Nat.card F) (D : Subgroup PSL(2,F))
    (hD : D ≤ borel F) (hsup : kernel F ⊔ D = borel F) :
    ∃ d ∈ D, ∃ β : P1 F, β ≠ pInf F ∧
      ∀ ω : P1 F, d • ω = ω ↔ ω = pInf F ∨ ω = β := by
  have hc : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  let : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp hc
  obtain ⟨a, ha⟩ := exists_ne (1 : Fˣ)
  let t := torusHom F a
  have ht : t ∈ complement F := ⟨a, rfl⟩
  have htne : (⟨t, ht⟩ : complement F) ≠ 1 := by
    intro he
    have he' : torusHom F a = torusHom F 1 := by
      simpa only [Subgroup.coe_one, map_one] using congrArg Subtype.val he
    exact ha (((pi_injective (F := F)).comp (torHom_injective (F := F))) he')
  have hβ : pZero F ≠ pInf F := by
    intro he
    apply PWeyl_notMem_PBorel (F := F)
    exact PWeyl_smul_pInf.trans he
  apply two_fixed_in_supplement (kernel F) D (pInf F) (pZero F) hβ _ _ t
    (complement_normalizes F ht) _ _ _
  · change kernel F ≤ PBorel F
    rw [← borel_eq_PBorel F]
    exact le_sup_left
  · rwa [normalizer_kernel F]
  · rw [hsup]
    exact (show complement F ≤ borel F from le_sup_right) ht
  · intro r hr
    exact fixedPointFree F ⟨t, ht⟩ htne r hr
  · intro ω
    exact diagonal_fixed_pair a (diagonal_distinct a ha) ω

/-- Arbitrary Sylow normalizers and arbitrary supplied odd complements in even PSL₂. -/
theorem sylow_two_fixed_cosets (hq : 2 < Nat.card F) (T : Sylow 2 PSL(2,F)) :
    SylowHasTwoFixedCosets T := by
  apply all_sylows (standardSylow F) _ T
  intro D hD _hodd _hdis hsup
  have hN : Subgroup.normalizer (standardSylow F : Set PSL(2,F)) = borel F := by
    change Subgroup.normalizer ((standardSylow F : Subgroup PSL(2,F)) : Set PSL(2,F)) = _
    rw [coe_standardSylow, normalizer_kernel]
  apply two_fixed_cosets _ D (pInf F) (hN.trans (borel_eq_PBorel F))
    (fun x => MulAction.exists_smul_eq PSL(2,F) _ x)
  apply supplement_two_fixed hq D (hN ▸ hD)
  simpa only [coe_standardSylow, hN] using hsup

omit [CharP F 2] in
/-- Perfectness excludes PSL₂(2), via its actual isomorphism with S₃ and the sign map. -/
theorem card_gt_two_of_perfect [Group.IsPerfect PSL(2,F)] : 2 < Nat.card F := by
  by_contra h
  have hF : Nat.card F = 2 := by have := Finite.one_lt_card (α := F); omega
  obtain ⟨e⟩ := BenderSuzuki.External.huppert_II_6_14_a_psl2_card_two hF
  let : Group.IsPerfect (Equiv.Perm (Fin 3)) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hk := Abelianization.commutator_subset_ker (Equiv.Perm.sign : Equiv.Perm (Fin 3) →* ℤˣ)
  have he : Equiv.Perm.sign (Equiv.swap (0 : Fin 3) 1) = 1 := by
    apply hk
    rw [Group.IsPerfect.commutator_eq_top]
    trivial
  norm_num at he

/-- The perfect even PSL₂ branch, including the proof that its small parameter is impossible. -/
theorem perfect_sylow_two_fixed_cosets [Group.IsPerfect PSL(2,F)]
    (T : Sylow 2 PSL(2,F)) : SylowHasTwoFixedCosets T :=
  sylow_two_fixed_cosets card_gt_two_of_perfect T
end Theory.PSL2.CartanPanel
