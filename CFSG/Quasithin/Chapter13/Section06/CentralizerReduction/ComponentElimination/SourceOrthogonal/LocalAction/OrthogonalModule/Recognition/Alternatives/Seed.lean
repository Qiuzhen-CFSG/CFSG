module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition.Section
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Marking
public import Theory.Representation.BinarySylowFixedSpace

/-!
# The moving seed in the Sylow-fixed part of U_K

The original seed z is fixed by Tᵥ. Average it over the odd number of cosets
of the actual Sylow two-subgroup of K⁺. The average is K⁺-fixed and differs
from z by a vector of U_K = [W_K,K⁺]. That difference is still Sylow-fixed,
and an element of Lᵥ moving z moves it as well. Consequently the actual
source parabolic cannot fix the whole Sylow-fixed subspace of U_K.

This constructs the seed obstruction used to compare the natural-plus-dual
row. It does not assume that W_K is a split extension or that z belongs to
U_K. The Sylow is marked by the literal plus image of Tᵥ ∩ K.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), the paragraph
following 13.6.23, printed p.933/PDF p.950.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition.Alternatives
open ComponentSelection
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
variable {G : Type*} [Group G] [Finite G] (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]

/-- Movement of the original Sylow-fixed seed persists in the actual upper
space. Odd-index averaging retains arbitrary central extensions. -/
theorem exists_moving_upper_sylow_fixed
    (hLK : Lv L v ≤ K)
    (hmove : ¬ Lv L v ≤ centralizer ({z} : Set G))
    (s : MovedSection (representation K L T z v hL hz) (plusImage K L T z v hL hz K))
    (R : Sylow 2 (plusImage K L T z v hL hz K))
    (hR : (R : Subgroup (plusImage K L T z v hL hz K)).map
      (plusImage K L T z v hL hz K).subtype = plusImage K L T z v hL hz (Tv T v ⊓ K)) :
    ∃ u ∈ fixedSpace (s.space.toRepresentation.comp (plusImage K L T z v hL hz K).subtype)
        (R : Subgroup (plusImage K L T z v hL hz K)),
      ∃ g : plusImage K L T z v hL hz K,
        (g : Gplus K L T z v hL hz) ∈ plusImage K L T z v hL hz (Lv L v) ∧
          s.space.toRepresentation (g : Gplus K L T z v hL hz) u ≠ u := by
  classical
  let ρ := representation K L T z v hL hz
  let C := plusImage K L T z v hL hz K
  let τ := ρ.comp C.subtype
  let a : Additive (WK K L T z v) := Additive.ofMul (markedSeed K L T z v)
  have ha : a ∈ fixedSpace τ (R : Subgroup C) := by
    intro r
    have hr : (r.val : Gplus K L T z v hL hz) ∈ plusImage K L T z v hL hz (Tv T v ⊓ K) :=
      hR ▸ (show (r.val : Gplus K L T z v hL hz) ∈
        (R : Subgroup C).map C.subtype from ⟨r.val, r.property, rfl⟩)
    exact seed_fixed_by_Tv K L T z v hL hz _ (map_mono (comap_mono inf_le_left) hr)
  obtain ⟨w, hw, haw⟩ := BinarySylowFixedSpace.fixed_lift_mod_trivial_quotient τ R
    s.space.toSubmodule (fun g x => s.space_eq.symm ▸
      Submodule.subset_span ⟨g, g.property, x, Submodule.mem_top, rfl⟩) a ha
  let u : s.space.toSubmodule := ⟨a - w, haw⟩
  have hu : u ∈ fixedSpace (s.space.toRepresentation.comp C.subtype) (R : Subgroup C) := by
    intro r
    apply Subtype.ext
    change τ r.val (a - w) = a - w
    have har : τ r.val a = a := ha r
    rw [map_sub, har, hw]
  obtain ⟨k, hk, hkn⟩ : ∃ k ∈ Lv L v, k ∉ centralizer ({z} : Set G) := by
    simpa only [SetLike.le_def, not_forall, exists_prop] using hmove
  let k' : plusActor K L T v := ⟨k, K_le_plusActor K L T v (hLK hk)⟩
  let g : C := ⟨plusMk K L T z v hL hz k', ⟨k', hLK hk, rfl⟩⟩
  refine ⟨u, hu, g, ⟨k', hk, rfl⟩, ?_⟩
  intro he
  have hd := congrArg Subtype.val he
  change τ g (a - w) = a - w at hd
  rw [map_sub, hw] at hd
  have hfix : ρ g a = a := sub_left_inj.mp hd
  exact hkn ((mk_mem_seedStabilizer K L T z v hL hz k').mp hfix)

/-- The source minimal parabolic cannot fix the whole Sylow-fixed subspace
of U_K. This is the local obstruction consumed by the module comparisons. -/
theorem sourceParabolic_not_fix_upper_sylow
    (hLK : Lv L v ≤ K)
    (hmove : ¬ Lv L v ≤ centralizer ({z} : Set G))
    (s : MovedSection (representation K L T z v hL hz) (plusImage K L T z v hL hz K))
    (R : Sylow 2 (plusImage K L T z v hL hz K))
    (hR : (R : Subgroup (plusImage K L T z v hL hz K)).map
      (plusImage K L T z v hL hz K).subtype = plusImage K L T z v hL hz (Tv T v ⊓ K)) :
    ¬ ∀ u ∈ fixedSpace (s.space.toRepresentation.comp (plusImage K L T z v hL hz K).subtype)
        (R : Subgroup (plusImage K L T z v hL hz K)),
      ∀ g : plusImage K L T z v hL hz K,
        (g : Gplus K L T z v hL hz) ∈
          plusImage K L T z v hL hz (sourceParabolic K L T v) →
        s.space.toRepresentation (g : Gplus K L T z v hL hz) u = u := by
  obtain ⟨u, hu, g, hg, hn⟩ := exists_moving_upper_sylow_fixed K L T z v hL hz hLK hmove s R hR
  intro h
  exact hn (h u hu g (map_mono (comap_mono (show Lv L v ≤ sourceParabolic K L T v from
    le_sup_left)) hg))

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition.Alternatives
