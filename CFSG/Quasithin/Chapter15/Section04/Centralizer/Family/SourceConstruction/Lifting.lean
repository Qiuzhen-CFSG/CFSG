module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.Basic

/-!
# Constructing source members from quotient subgroups

The order-three case constructs a member of the lowercase Xi family, and
hence of Y, from a normalized quotient factor and its actual Thompson
commutator. The quotient isomorphism retains the original projection on
every element. The local H condition is explicit and must be supplied by
the source application; it is not inferred from an arbitrary solvable group.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Lemma 15.4.12, printed pp.1160–1161.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section04.FamilySource
open LocalSetup.TwoFactors.SourceFactors.Permutation
variable {G : Type*} [Group G] [Finite G]

/-- Normalizing an actual quotient subgroup normalizes its residual lift. -/
theorem lift_normalized (M U : Subgroup G) (hUM : U ≤ M)
    (A : Subgroup (CoreQuotient M))
    (hn : image M U ≤ normalizer (A : Set (CoreQuotient M))) :
    U ≤ normalizer (lift M A : Set G) := by
  have h := liftedFactors_normalized M (quotientMap M) (fun _ : Bool => A)
    (U.subgroupOf M) false hn
  rwa [map_subgroupOf_eq_of_le hUM] at h

/-- The residual lift has the specified quotient image. -/
theorem image_lift (M : Subgroup G) (A : Subgroup (CoreQuotient M))
    (hp : IsPPerfect 2 A) : image M (lift M A) = A := by
  change (((residualPreimage (quotientMap M) A).map M.subtype).subgroupOf M).map
    (quotientMap M) = A
  rw [← comap_subtype, comap_map_eq_self_of_injective M.subtype_injective]
  exact residualPreimage_image (quotientMap M) (QuotientGroup.mk'_surjective _) A hp

/-- Quotient commutator saturation lifts through the two-group kernel. -/
theorem lift_commutator (M J : Subgroup G) (hJM : J ≤ M)
    (A : Subgroup (CoreQuotient M)) (hp : IsPPerfect 2 A)
    (hn : image M J ≤ normalizer (A : Set (CoreQuotient M)))
    (hc : ⁅A, image M J⁆ = A) : ⁅lift M A, J⁆ = lift M A := by
  have hk : IsPGroup 2 (quotientMap M).ker := by
    rw [quotientMap, QuotientGroup.ker_mk']; exact pCore_isPGroup
  have he : ⁅residualPreimage (quotientMap M) A, J.subgroupOf M⁆ =
      residualPreimage (quotientMap M) A := by
    apply eq_of_perfect_of_map_eq (quotientMap M) hk
      (residualPreimage_perfect (quotientMap M) A)
      (le_normalizer_iff_commutator_le_left.mp
        (residualPreimage_normalized _ _ _ hn))
      (normalizer_commutator_ge_left _ _)
    rw [map_commutator, residualPreimage_image (quotientMap M) (QuotientGroup.mk'_surjective _) A hp]
    exact hc
  have h := congrArg (Subgroup.map M.subtype) he
  rwa [map_commutator, map_subgroupOf_eq_of_le hJM] at h

/-- The order-three quotient isomorphism respects the original quotient map. -/
theorem prime_lift_quotient (M : Subgroup G) (A : Subgroup (CoreQuotient M))
    (hA : Nat.card A = 3) :
    ∃ e : (lift M A ⧸ pCore 2 (lift M A)) ≃* A,
      ∀ x : lift M A,
        (e (QuotientGroup.mk' (pCore 2 (lift M A)) x) : CoreQuotient M) =
          quotientMap M ⟨(x : G), lift_le M A x.property⟩ := by
  have hk : IsPGroup 2 (quotientMap M).ker := by
    rw [quotientMap, QuotientGroup.ker_mk']; exact pCore_isPGroup
  exact liftedFactors_quotient_compatible M (quotientMap M)
    (QuotientGroup.mk'_surjective _) hk (fun _ : Bool => A) false hA

/-- Construct a genuine Y-member from an order-three factor. The remaining
H-overgroup premise is a source-domain condition, not family membership. -/
theorem prime_lift_mem_Y (T M : Subgroup G) (hTM : T ≤ M)
    (A : Subgroup (CoreQuotient M)) (hA : Nat.card A = 3)
    (hn : image M T ≤ normalizer (A : Set (CoreQuotient M)))
    (hc : ⁅A, image M (elementaryAbelianMaxJ T)⁆ = A)
    (hH : lift M A ⊔ T ∈ Chapter1.HOver G (T : Set G)) : lift M A ∈ Y T := by
  have hJT : elementaryAbelianMaxJ T ≤ T := sSup_le fun _ h => h.1
  have hJ : image M (elementaryAbelianMaxJ T) ≤ normalizer (A : Set (CoreQuotient M)) :=
    (map_mono (comap_mono hJT)).trans hn
  obtain ⟨e, _⟩ := prime_lift_quotient M A hA
  have hi : (pCore 2 (lift M A)).index = 3 := (Nat.card_congr e.toEquiv).trans hA
  refine ⟨Or.inr ⟨lift_normalized M T hTM A hn, lift_perfect M A, hH,
    hi ▸ Nat.prime_three, hi ▸ (by decide : Odd 3)⟩, ?_⟩
  exact (lift_commutator M _ (hJT.trans hTM) A (three_isPPerfect A hA) hJ hc).symm

end CFSG.Quasithin.Chapter15.Section04.FamilySource
