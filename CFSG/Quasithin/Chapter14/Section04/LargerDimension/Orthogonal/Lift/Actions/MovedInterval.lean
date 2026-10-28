module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.Elementary
public import Theory.GroupAction.InvariantImageInterval

/-!
# From the actual moved quotient to the elementary lift

Irreducibility of the literal image of [U,i] in U/Z(U) implies that
⟨z⟩<A has no intermediate invariant subgroup. This discharges the
invariant-interval premise in the elementary lift construction. The
supplied action must satisfy the actual quotient-conjugation formula;
no abstractly isomorphic but unrelated action is used.

The comparison of this image action with the binary A₅ module remains
an input to the source assembly, which must establish its irreducibility.

Source: Aschbacher–Smith, Lemma 14.4.9, printed p.1010.
-/

public section
open Subgroup

namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal
variable {G : Type*} [Group G] [Finite G]

/-- The literal moved-image action supplies the interval premise used in the lift. -/
theorem liftBase_invariant_interval_of_moved_image
    (U K : Subgroup G) [IsExtraspecial 2 U] (z i : G)
    (hZ : (center U).map U.subtype = zpowers z)
    (hiU : i ∈ normalizer (U : Set G))
    (hKU : K ≤ normalizer (U : Set G))
    (hmoved : Nat.card (((⁅U,zpowers i⁆).subgroupOf U).map
      (QuotientGroup.mk' (center U))) = 16)
    (ρ : K →* MulAut (U ⧸ center U))
    (hρ : ∀ k : K, ∀ u : U, ρ k (QuotientGroup.mk' (center U) u) =
      QuotientGroup.mk' (center U) ⟨(k : G) * (u : G) * (k : G)⁻¹,
        (mem_normalizer_iff.mp (hKU k.property) u).mp u.property⟩)
    (hirr : ∀ F : Subgroup (U ⧸ center U),
      F ≤ ((⁅U,zpowers i⁆).subgroupOf U).map (QuotientGroup.mk' (center U)) →
      (∀ k : K, ∀ v ∈ F, ρ k v ∈ F) → F = ⊥ ∨
        F = ((⁅U,zpowers i⁆).subgroupOf U).map (QuotientGroup.mk' (center U))) :
    ∀ E : Subgroup G, zpowers z ≤ E → E ≤ liftBase U z i →
      K ≤ normalizer (E : Set G) → E = zpowers z ∨ E = liftBase U z i := by
  have hzU : zpowers z ≤ U := by rw [← hZ]; exact map_subtype_le _
  have hAU : liftBase U z i ≤ U := sup_le
    (le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr hiU)) hzU
  have hker : (QuotientGroup.mk' (center U)).ker = (zpowers z).subgroupOf U := by
    rw [QuotientGroup.ker_mk']
    apply map_injective U.subtype_injective
    rw [map_subgroupOf_eq_of_le hzU, hZ]
  have hAB := (liftBase_eq_commutator_and_card U z i hZ hiU hmoved).1
  apply invariant_interval_of_image_irreducible U (liftBase U z i) (zpowers z) K
    le_sup_right hAU hKU (QuotientGroup.mk' (center U)) hker ρ hρ
  simpa only [hAB] using hirr

/-- Applying the image-to-interval bridge constructs the elementary lift. -/
theorem centralizerLift_elementary_and_card_of_moved_image
    (U K : Subgroup G) [IsExtraspecial 2 U] (z i : G)
    (hz : orderOf z = 2) (hi : orderOf i = 2)
    (hZ : (center U).map U.subtype = zpowers z)
    (hiU : i ∈ normalizer (U : Set G)) (hiz : i ∈ centralizer ({z} : Set G))
    (hout : i ∉ U) (hKU : K ≤ normalizer (U : Set G))
    (hKi : K ≤ centralizer ({i} : Set G))
    (hmoved : Nat.card (((⁅U,zpowers i⁆).subgroupOf U).map
      (QuotientGroup.mk' (center U))) = 16)
    (ρ : K →* MulAut (U ⧸ center U))
    (hρ : ∀ k : K, ∀ u : U, ρ k (QuotientGroup.mk' (center U) u) =
      QuotientGroup.mk' (center U) ⟨(k : G) * (u : G) * (k : G)⁻¹,
        (mem_normalizer_iff.mp (hKU k.property) u).mp u.property⟩)
    (hirr : ∀ F : Subgroup (U ⧸ center U),
      F ≤ ((⁅U,zpowers i⁆).subgroupOf U).map (QuotientGroup.mk' (center U)) →
      (∀ k : K, ∀ v ∈ F, ρ k v ∈ F) → F = ⊥ ∨
        F = ((⁅U,zpowers i⁆).subgroupOf U).map (QuotientGroup.mk' (center U))) :
    IsElementaryAbelian 2 (centralizerLift U z i) ∧
      Nat.card (centralizerLift U z i) = 64 ∧
      IsElementaryAbelian 2 (liftBase U z i) ∧ Nat.card (liftBase U z i) = 32 :=
  centralizerLift_elementary_and_card U K z i hz hi hZ hiU hiz hout hKU hKi hmoved
    (liftBase_invariant_interval_of_moved_image U K z i hZ hiU hKU hmoved ρ hρ hirr)

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal
