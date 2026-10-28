module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ModelCases

/-!
# A literal even-field Borel placement

The output contract names a finite characteristic-two field, a multiplicative
isomorphism of the actual K with SL₂(F) × SL₂(F), its embedded upper-triangular
Borel, and the inclusion of the actual four-module in its root subgroup.
Constructing that placement from characteristic-normalizer control remains a
source obligation.

Once placed, the Borel is two-perfect by the matrix calculation. Its action
on the two source factors is trivial, so it normalizes their commutator
modules. Pulling the selected four-module back through the injective product
map permits the checked root-product bound, forcing the field order to be
at most four. No two-core is substituted for the two-residual.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
proof of 15.4.20, printed p.1164.
-/

@[expose] public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination
open BenderSuzuki.Converse Matrix.SpecialLinearGroup
variable {G : Type*} [Group G]

/-- A concrete Borel placement, including the actual product isomorphism
and the inclusion of the specified ambient module in the root subgroup. -/
def EvenBorelPlacement (K V M : Subgroup G) (q : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = q ∧
    ∃ e : K ≃* (SL(2,F) × SL(2,F)),
      ((Borel F).prod (Borel F)).map (K.subtype.comp e.symm.toMonoidHom) ≤ M ∧
      V ≤ ((upperUnipotent F).prod (upperUnipotent F)).map (K.subtype.comp e.symm.toMonoidHom)

/-- Transport the placed Borel and the actual commutator module to matrix
coordinates. Two-perfectness makes the Borel fix both source factors, so
its action normalizes the transported four-group. -/
theorem even_borel_placement_field_bound [Finite G]
    {K M V : Subgroup G} {L : Bool → Subgroup G}
    (a : TwoFactors.MixedLocal.FactorPairAction M L)
    (hMV : M ≤ normalizer (V : Set G)) (i : Bool)
    (hcard : Nat.card (⁅V,L i⁆ : Subgroup G) = 4)
    {q : ℕ} (hq : 4 ≤ q) (h : EvenBorelPlacement K ⁅V,L i⁆ M q) : q ≤ 4 := by
  obtain ⟨F,_,_,_,hF,e,hBM,hVR⟩ := h
  let f := K.subtype.comp e.symm.toMonoidHom
  let B₀ := (Borel F).prod (Borel F)
  let R₀ := (upperUnipotent F).prod (upperUnipotent F)
  let W := (⁅V,L i⁆ : Subgroup G).comap f
  have hf : Function.Injective f := K.subtype_injective.comp e.symm.injective
  have hB₀ : IsPPerfect 2 B₀ := linear_borel_pair_isPPerfect (by omega : 4 ≤ Nat.card F)
  have hB : IsPPerfect 2 (B₀.map f) := hB₀.of_surjective (f.subgroupMap B₀) (f.subgroupMap_surjective B₀)
  have hn : B₀.map f ≤ normalizer ((⁅V,L i⁆ : Subgroup G) : Set G) :=
    twoPerfect_normalizes_factor_modules a hBM hB hMV i
  have hWroot : W ≤ R₀ := by
    have hh := comap_mono (f := f) hVR
    rwa [comap_map_eq_self_of_injective hf] at hh
  have hWmap : W.map f = ⁅V,L i⁆ := map_comap_eq_self (hVR.trans (map_le_range f R₀))
  have hWcard : Nat.card W = 4 := by
    rw [← card_map_of_injective hf, hWmap]
    exact hcard
  have hBW : B₀ ≤ normalizer (W : Set (SL(2,F) × SL(2,F))) := by
    have hh : B₀ ≤ (normalizer ((⁅V,L i⁆ : Subgroup G) : Set G)).comap f := by
      intro b hb
      exact hn (mem_map_of_mem f hb)
    exact hh.trans ((⁅V,L i⁆ : Subgroup G).le_normalizer_comap f)
  rw [← hF]
  exact linear_root_pair_four_field_bound W hWroot hWcard hBW

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination
