module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Models
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# The quadratic obstruction in K.3.4.2

A quadratic actor centralizes every displacement space of its elements.
The source root-fixer calculation therefore bounds its rank by s. The
involution fixed-space bound on a 16s-dimensional module gives codimension
at least 6s, contradicting ratio at most two.

The geometric premises below are deliberately explicit: outer-actor placement,
involution fixed dimensions, and the orders of the actual Sylow pointwise
fixers. Their construction for the descended tensor is still required.
This is a conditional reduction, not a proof of K.3.4.2 by itself.
Source: Aschbacher–Smith, printed p.457.
-/

public section
namespace CFSG.Quasithin.ChapterK.Symplectic
open Subgroup Representation Representation.BinaryOffender

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The root-fixer calculation rules out a particular quadratic actor. -/
theorem tensor_quadratic_actor_excluded {s : ℕ} (hs : 0 < s)
    (hdim : Module.finrank (ZMod 2) V = 16 * s)
    {A T : Subgroup G} (hAT : A ≤ T) (hq : IsQuadratic ρ A)
    (hr : fixedCodim ρ A ≤ 2 * rank A) {j : G} (hj : j ∈ A)
    (hfix : Module.finrank (ZMod 2) (fixedSpace ρ (zpowers j)) ≤ 10 * s)
    (hroot : rank (subspaceKernel ρ (LinearMap.range (displacement ρ j)) T) ≤ s) :
    False := by
  have hker : A ≤ subspaceKernel ρ (LinearMap.range (displacement ρ j)) T := by
    intro a ha
    refine ⟨hAT ha, ?_⟩
    rintro _ ⟨v, rfl⟩
    exact hq a ha j hj v
  have hrank := Nat.log_mono_right (b := 2) (Subgroup.card_le_of_le hker)
  change rank A ≤ rank (subspaceKernel ρ (LinearMap.range (displacement ρ j)) T) at hrank
  have hfixed : fixedSpace ρ A ≤ fixedSpace ρ (zpowers j) := by
    intro v hv
    exact (mem_fixedSpace_zpowers_iff ρ j v).mpr (hv ⟨j, hj⟩)
  have hfd := Submodule.finrank_mono hfixed
  have hsum := fixedCodim_add_finrank ρ A
  omega

/-- After field-automorphism exclusion, the literal Sylow root-fixer and
involution computations imply the strict quadratic bound. -/
theorem tensor_quadraticRatio_gt_two {s : ℕ} (hs : 0 < s)
    (hdim : Module.finrank (ZMod 2) V = 16 * s) (L : Subgroup G)
    (hplace : ∀ A, IsElementaryTwo A → fixedCodim ρ A ≤ 2 * rank A → A ≤ L)
    (hlocal : ∀ (T : Sylow 2 G) (j : G), j ∈ T → j ∈ L → orderOf j = 2 →
      Module.finrank (ZMod 2) (fixedSpace ρ (zpowers j)) ≤ 10 * s ∧
        rank (subspaceKernel ρ (LinearMap.range (displacement ρ j)) T) ≤ s) :
    2 < quadraticRatio ρ := by
  by_contra! hsmall
  obtain ⟨A, hA, hquad, hr⟩ := (quadraticRatio_le_two_iff ρ).mp hsmall
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨T, hAT⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨j, hj⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA.1
  have horder : orderOf (j : G) = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (j : G) j.property)
    (fun he => hj (Subtype.ext he))
  obtain ⟨hfix, hroot⟩ := hlocal T j (hAT j.property)
    (hplace A hA hr j.property) horder
  exact tensor_quadratic_actor_excluded ρ hs hdim hAT hquad hr j.property hfix hroot

/-- The actual scalar-extension identification supplies the dimension premise
of the source obstruction. Its remaining inputs are geometric computations. -/
theorem TensorIdentification.quadraticRatio_gt_two
    {F : Type*} [Field F] {L : Subgroup G}
    [IsIrreducible (ρ.comp L.subtype)]
    [Algebra (SchurField (ρ.comp L.subtype)) F]
    {s : ℕ} (hs : 0 < s) (h : TensorIdentification (ρ.comp L.subtype) F s)
    (hplace : ∀ A, IsElementaryTwo A → fixedCodim ρ A ≤ 2 * rank A → A ≤ L)
    (hlocal : ∀ (T : Sylow 2 G) (j : G), j ∈ T → j ∈ L → orderOf j = 2 →
      Module.finrank (ZMod 2) (fixedSpace ρ (zpowers j)) ≤ 10 * s ∧
        rank (subspaceKernel ρ (LinearMap.range (displacement ρ j)) T) ≤ s) :
    2 < quadraticRatio ρ :=
  tensor_quadraticRatio_gt_two ρ hs h.binary_finrank L hplace hlocal

end CFSG.Quasithin.ChapterK.Symplectic
