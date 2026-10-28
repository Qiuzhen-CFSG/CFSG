module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FixedSpaces
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FourSpaceOffenders.CenterGeometry

/-!
# Offenders on the four-space with a natural central quotient

The involution fixed planes and the elementary rank bound exclude strong
and cyclic offenders. A four-group is best precisely when its involutions
have the same fixed plane. For a central natural quotient these planes are
the actual preimages of the transvection centers, so the offenders are
exactly the full-center groups. An explicit line provides an offender,
and absence of strong offenders gives quadratic ratio one.

All actions, quotient maps and subgroup identifications are literal.
Source: Aschbacher–Smith, B.4.8(2), printed p.91, combined manuscript
of 1 March 2004.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.ChapterB.NaturalExtensions
open BinaryLinearThree FourSpaceOffenders
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) BinaryLinearThree.Group V)
  (p : ρ.IntertwiningMap W) (hp : Function.Surjective p)
  (hfixed : p.toLinearMap.ker ≤ Representation.OneCohomology.fixed ρ)
  (hind : ∀ A B : Submodule (ZMod 2) V,
      (∀ g v, v ∈ A → ρ g v ∈ A) →
      (∀ g v, v ∈ B → ρ g v ∈ B) → IsCompl A B → A = ⊥ ∨ B = ⊥)
  (hdim : Module.finrank (ZMod 2) V = 4)

include p hp hfixed hind hdim

theorem central_best_iff_fullCenter (A : Subgroup BinaryLinearThree.Group) :
    IsBestOffender ρ A ↔ IsFullCenterGroup BinaryField.two 3 A := by
  have hInv := central_quotient_involutions ρ p hp hfixed hind hdim
  have hpre := central_quotient_involution_fixed_preimage ρ p hp hfixed hind hdim
  rw [fullCenter_iff_common_range]
  constructor
  · intro hA
    have hAr := (best_iff ρ hdim (fun a ha => (hInv a ha).2) A).mp hA
    let _ : IsElementaryAbelian 2 A := hAr.1.2
    obtain ⟨a, ha, hne⟩ := A.bot_or_exists_ne_one.resolve_left hAr.1.1
    have hao : orderOf a = 2 := orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian a ha) hne
    refine ⟨hAr.1, hAr.2.1, LinearMap.range (W a - LinearMap.id),
      natural_involution_range_finrank a hao, ?_⟩
    intro b hb hbn
    have hbo : orderOf b = 2 := orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian b hb) hbn
    apply Submodule.comap_injective_of_surjective hp
    rw [← hpre a hao, ← hpre b hbo]
    exact (best_fixedSpace_eq_involution ρ hdim (fun a ha => (hInv a ha).2) hA hb hbn).symm.trans
      (best_fixedSpace_eq_involution ρ hdim (fun a ha => (hInv a ha).2) hA ha hne)
  · rintro ⟨hA, hr, P, hP, hRanges⟩
    let _ : IsElementaryAbelian 2 A := hA.2
    obtain ⟨a, ha, hne⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
    have hao : orderOf a = 2 := orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian a ha) hne
    have hf : fixedSpace ρ A = fixedSpace ρ (zpowers a) := by
      apply le_antisymm (fixedSpace_antitone ρ (zpowers_le.mpr ha))
      intro v hv b
      by_cases hbn : (b : BinaryLinearThree.Group) = 1
      · change ρ (b : BinaryLinearThree.Group) v = v
        simp [hbn]
      have hbo : orderOf (b : BinaryLinearThree.Group) = 2 := orderOf_eq_prime
        (elemPow_eq_one_of_isElementaryAbelian (b : BinaryLinearThree.Group) b.property) hbn
      have he : fixedSpace ρ (zpowers (b : BinaryLinearThree.Group)) =
          fixedSpace ρ (zpowers a) := by
        rw [hpre _ hbo, hpre a hao, hRanges a ha hne, hRanges b b.property hbn]
      exact (mem_fixedSpace_zpowers_iff ρ (b : BinaryLinearThree.Group) v).mp (he.symm ▸ hv)
    exact (best_iff ρ hdim (fun a ha => (hInv a ha).2) A).mpr
      ⟨hA, hr, hf ▸ (hInv a hao).2⟩

theorem central_quadraticRatio : quadraticRatio ρ = 1 := by
  have hInv := central_quotient_involutions ρ p hp hfixed hind hdim
  let P := Submodule.span (ZMod 2) {(![1,0,0] : BinaryLinearThree.Vector)}
  have hP : Module.finrank (ZMod 2) P = 1 := finrank_span_singleton (by decide)
  have hA := (central_best_iff_fullCenter ρ p hp hfixed hind hdim (centerGroup P)).mpr
    (centerGroup_full P hP)
  exact quadraticRatio_eq_one_of_no_strong ρ ⟨centerGroup P, hA.isOffender ρ⟩
    (no_strong ρ hdim (fun a ha => (hInv a ha).2))

theorem central_fullCenter_quadratic {A : Subgroup BinaryLinearThree.Group}
    (hA : IsFullCenterGroup BinaryField.two 3 A) : IsQuadratic ρ A :=
  best_quadratic ρ hdim (central_quotient_involutions ρ p hp hfixed hind hdim)
    ((central_best_iff_fullCenter ρ p hp hfixed hind hdim A).mpr hA)
end CFSG.Quasithin.ChapterB.NaturalExtensions
