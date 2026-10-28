module

public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.LocalActors.Outer
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.Representation.BinaryOffender.RestrictionComparison
public import Theory.GroupTheory.DoubleCoverCentralizer.TwoCentralSylow

/-!
# Reductions to the remaining local action calculations in H.11

Faithful quadratic binary actors are elementary abelian. If a quadratic actor
contains an involution t, it lies in the kernel of C_G(t) on [V,t]. Thus a
bound of four on this kernel, and two on its residual intersection, force a
noncyclic actor containing a non-two-central involution to have order four
and contain an outer involution. The proved outer displacement calculation
then gives the strict codimension bound.

Separately, an inner/outer involution pair with common fixed dimension at most
three bounds the fixed space of every subgroup containing the pair and gives
a fixed-space span of dimension at least eight.

Both reductions retain their action premises explicitly. They do not establish
H.11.1(4),(5) until the fixed-pair existence and displacement-kernel calculations
are supplied. Two-centrality here is membership in the center of an actual
Sylow two-subgroup of G.
Source: Aschbacher–Smith H.11.1, printed pp.392–393, combined manuscript of
1 March 2004.
-/

public section

open Subgroup Representation.BinaryOffender Sporadic.Mathieu
open Theory.GroupTheory.DoubleCoverCentralizer
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.LocalActors

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- The kernel of C_G(t) on the actual displacement space [V,t]. -/
@[expose] noncomputable def involutionDisplacementFixer (ρ : Representation (ZMod 2) G V)
    (t : G) : Subgroup G :=
  subspaceKernel ρ (LinearMap.range (ρ t - LinearMap.id)) (centralizer ({t} : Set G))

/-- Faithfulness turns quadratic binary action into an elementary actor. -/
theorem elementary_of_quadratic (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) (A : Subgroup G) (hA : IsQuadratic ρ A) :
    IsElementaryAbelian 2 A := by
  have hneg (v : V) : -v = v := by
    have hv : v + v = 0 := by
      simpa only [add_smul, one_smul, zero_smul] using
        congrArg (fun c : ZMod 2 => c • v) (by decide : (1 : ZMod 2) + 1 = 0)
    exact neg_eq_of_add_eq_zero_left hv
  have hs (a : G) (ha : a ∈ A) : a ^ 2 = 1 := by
    apply hρ
    ext v
    have hh := hA a ha a ha v
    change ρ a (ρ a v - v) = ρ a v - v at hh
    rw [map_sub] at hh
    have he : ρ a (ρ a v) + ρ a v = v + ρ a v := by
      simpa only [map_sub, sub_eq_add_neg, hneg, add_comm (ρ a v) v] using hh
    simpa only [pow_two, map_mul, Module.End.mul_apply, map_one, Module.End.one_apply]
      using add_right_cancel he
  have hi (a : A) : a⁻¹ = a := by
    apply inv_eq_of_mul_eq_one_left
    apply Subtype.ext
    simpa only [pow_two, Subgroup.coe_mul, Subgroup.coe_one] using hs a a.property
  refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
  · calc
      a * b = (a * b)⁻¹ := (hi _).symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev _ _
      _ = b * a := by rw [hi, hi]
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro a
    exact Subtype.ext (hs a a.property)

/-- A quadratic actor fixes every displacement of each of its elements. -/
theorem quadratic_le_displacementFixer (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) {A : Subgroup G} (hA : IsQuadratic ρ A)
    {t : G} (ht : t ∈ A) : A ≤ involutionDisplacementFixer ρ t := by
  let := elementary_of_quadratic ρ hρ A hA
  intro a ha
  refine ⟨mem_centralizer_singleton_iff.mpr ?_, ?_⟩
  · exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : A) (⟨t, ht⟩ : A))
  · rintro w ⟨v, rfl⟩
    exact hA a ha t ht v

private theorem four_le_card_of_noncyclic (A : Type*) [Group A] [Finite A]
    (hn : ¬ IsCyclic A) : 4 ≤ Nat.card A := by
  by_contra hc
  have hlo : 0 < Nat.card A := Nat.card_pos
  have hhi : Nat.card A ≤ 3 := by omega
  interval_cases hcard : Nat.card A
  · have : Subsingleton A := (Nat.card_eq_one_iff_unique.mp hcard).1
    exact hn inferInstance
  · exact hn (isCyclic_of_prime_card hcard)
  · exact hn (isCyclic_of_prime_card hcard)

variable [Finite G] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (h : M12ModuleInput ρ) (d : AmbientExtension ρ h)

include d in
/-- Conditional H.11.1(5) reduction; the two fixer bounds remain obligations. -/
theorem quadratic_alternative_of_fixer_bounds (hfusion : OuterInvolutionFusion)
    (hfix : ∀ t : G, orderOf t = 2 → ¬ TwoCentral t →
      Nat.card (involutionDisplacementFixer ρ t) ≤ 4 ∧
      Nat.card (involutionDisplacementFixer ρ t ⊓ solvableResidual G : Subgroup G) ≤ 2)
    (A : Subgroup G) (hA : IsQuadratic ρ A) (hn : ¬ IsCyclic A) :
    (∀ a ∈ A, a ≠ 1 → TwoCentral a) ∨ (rank A = 2 ∧ 4 < fixedCodim ρ A) := by
  classical
  by_cases hc : ∀ a ∈ A, a ≠ 1 → TwoCentral a
  · exact Or.inl hc
  push Not at hc
  obtain ⟨t, htA, ht1, htc⟩ := hc
  let := elementary_of_quadratic ρ h.faithful A hA
  have ht : orderOf t = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian t htA) ht1
  obtain ⟨hK, hKL⟩ := hfix t ht htc
  have hAK := quadratic_le_displacementFixer ρ h.faithful hA htA
  have hcard : Nat.card A = 4 := le_antisymm ((card_le_of_le hAK).trans hK)
    (four_le_card_of_noncyclic A hn)
  have hAL : ¬ A ≤ solvableResidual G := by
    intro hle
    have hh := (card_le_of_le (le_inf hAK hle)).trans hKL
    omega
  obtain ⟨a, haA, haL⟩ := Set.not_subset.mp hAL
  have ha1 : a ≠ 1 := fun he => haL (he ▸ (solvableResidual G).one_mem)
  have ha : orderOf a = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian a haA) ha1
  have hd := fixedCodim_outer_involution ρ h d hfusion haL ha
  have hf := Submodule.finrank_mono
    (fixedSpace_antitone ρ (zpowers_le.mpr haA))
  have hda := fixedCodim_add_finrank ρ (zpowers a)
  have hdA := fixedCodim_add_finrank ρ A
  refine Or.inr ⟨?_, by omega⟩
  norm_num [rank, hcard]

include d in
omit [Finite G] in
/-- The linear deduction in H.11.1(4), conditional on an actual pair. -/
theorem dimensions_of_inner_outer_fixed_pair (hfusion : OuterInvolutionFusion)
    {A : Subgroup G} {t z : G}
    (htA : t ∈ A) (htL : t ∉ solvableResidual G) (ht : orderOf t = 2)
    (hzA : z ∈ A) (hzL : z ∈ solvableResidual G) (hz : orderOf z = 2)
    (hpair : Module.finrank (ZMod 2)
      (fixedSpace ρ (zpowers t) ⊓ fixedSpace ρ (zpowers z) : Submodule (ZMod 2) V) ≤ 3) :
    Module.finrank (ZMod 2) (fixedSpace ρ A) ≤ 3 ∧
      8 ≤ Module.finrank (ZMod 2) (fixedSpaceSpan ρ A) := by
  have htfix := fixedCodim_add_finrank ρ (zpowers t)
  rw [fixedCodim_outer_involution ρ h d hfusion htL ht, h.finrank_eq_ten ρ] at htfix
  have hzfix := finrank_fixedSpace_residual_involution ρ h hzL hz
  have hsub : fixedSpace ρ A ≤ fixedSpace ρ (zpowers t) ⊓ fixedSpace ρ (zpowers z) :=
    le_inf (fixedSpace_antitone ρ (zpowers_le.mpr htA))
      (fixedSpace_antitone ρ (zpowers_le.mpr hzA))
  refine ⟨(Submodule.finrank_mono hsub).trans hpair, ?_⟩
  have ht1 : t ≠ 1 := fun he => by simp [he] at ht
  have hz1 : z ≠ 1 := fun he => by simp [he] at hz
  have hsum := (fixedSpace ρ (zpowers t)).finrank_sup_add_finrank_inf_eq
    (fixedSpace ρ (zpowers z))
  have hle := Submodule.finrank_mono (sup_le
    (fixedSpace_le_fixedSpaceSpan ρ htA ht1) (fixedSpace_le_fixedSpaceSpan ρ hzA hz1))
  omega

end CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.LocalActors
