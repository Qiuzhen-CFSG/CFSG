module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.SolvableFactor

/-!
# Saturated lifts of star factors

For a subgroup B of H/O₂(H), lift B by taking its full inverse image inside
J. When B lies in J*, this lift has star image exactly B and contains
J ∩ O₂(H). Subnormality lifts relative to H. If J is normal in H, the
normalizer and conjugacy-orbit length of the lift agree with those of B
under the quotient map.

The final construction turns actual quotient-factor data into the candidate
used by SolvableFactor. It proves the containment, saturation and subnormality
fields, and transports the given S₃ equivalence and section-action data.
It does not assert that a quotient factor exists or lift component generation
through a solvable kernel.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.49(i), printed pp.1143–1144, with B.5.6 on printed pp.105–110.
-/

@[expose] public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ClassificationCases
variable {G : Type*} [Group G]

/-- The full inverse image of B inside J, embedded in the original ambient group. -/
def saturatedStarLift (H J : Subgroup G) (B : Subgroup (H ⧸ pCore 2 H)) : Subgroup G :=
  (J.subgroupOf H ⊓ B.comap (QuotientGroup.mk' (pCore 2 H))).map H.subtype

theorem saturatedStarLift_le (H J : Subgroup G) (B : Subgroup (H ⧸ pCore 2 H)) :
    saturatedStarLift H J B ≤ J := by
  rintro x ⟨y, hy, rfl⟩
  exact hy.1

theorem saturatedStarLift_le_overgroup (H J : Subgroup G)
    (B : Subgroup (H ⧸ pCore 2 H)) : saturatedStarLift H J B ≤ H :=
  map_subtype_le _

theorem saturatedStarLift_subgroupOf (H J : Subgroup G)
    (B : Subgroup (H ⧸ pCore 2 H)) :
    (saturatedStarLift H J B).subgroupOf H =
      J.subgroupOf H ⊓ B.comap (QuotientGroup.mk' (pCore 2 H)) :=
  comap_map_eq_self_of_injective H.subtype_injective _

theorem saturatedStarLift_kernel_le (H J : Subgroup G)
    (B : Subgroup (H ⧸ pCore 2 H)) :
    J ⊓ localTwoCore H ≤ saturatedStarLift H J B := by
  rintro x ⟨hxJ, y, hy, rfl⟩
  refine ⟨y, ⟨hxJ, ?_⟩, rfl⟩
  change QuotientGroup.mk' (pCore 2 H) y ∈ B
  have he : QuotientGroup.mk' (pCore 2 H) y = 1 :=
    (QuotientGroup.eq_one_iff y).mpr hy
  rw [he]
  exact B.one_mem

theorem saturatedStarLift_image (H J : Subgroup G)
    (B : Subgroup (H ⧸ pCore 2 H)) (hBJ : B ≤ starImage H J) :
    starImage H (saturatedStarLift H J B) = B := by
  change ((saturatedStarLift H J B).subgroupOf H).map _ = B
  rw [saturatedStarLift_subgroupOf]
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact hy.2
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hBJ hx
    exact ⟨y, ⟨hy, hx⟩, rfl⟩

theorem saturatedStarLift_subnormal (H J : Subgroup G)
    (B : Subgroup (H ⧸ pCore 2 H))
    (hJ : (J.subgroupOf H).IsSubnormal) (hBJ : B ≤ starImage H J)
    (hB : (B.subgroupOf (starImage H J)).IsSubnormal) :
    ((saturatedStarLift H J B).subgroupOf H).IsSubnormal := by
  rw [saturatedStarLift_subgroupOf]
  have hJstar : (starImage H J).IsSubnormal :=
    hJ.map (QuotientGroup.mk'_surjective _)
  exact hJ.inf ((hB.trans hBJ hJstar).comap _)

/-- Kernel saturation determines the lift uniquely from its star image. -/
theorem saturatedStarLift_unique (H J L : Subgroup G)
    (hLH : L ≤ H) (hLJ : L ≤ J) (hker : J ⊓ localTwoCore H ≤ L) :
    saturatedStarLift H J (starImage H L) = L := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    obtain ⟨l, hl, he⟩ := hy.2
    have hdiff : y * l⁻¹ ∈ pCore 2 H := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' (pCore 2 H) (y * l⁻¹) = 1
      rw [map_mul, map_inv, he]
      exact mul_inv_cancel _
    have hin : ((y * l⁻¹ : H) : G) ∈ L := hker
      ⟨J.mul_mem hy.1 (J.inv_mem (hLJ hl)), ⟨y * l⁻¹, hdiff, rfl⟩⟩
    have hh := L.mul_mem hin hl
    simpa only [subtype_apply, coe_mul, coe_inv, inv_mul_cancel_right] using hh
  · intro x hx
    refine ⟨⟨x, hLH hx⟩, ⟨hLJ hx, ?_⟩, rfl⟩
    exact ⟨⟨x, hLH hx⟩, hx, rfl⟩


/-- Normalizers correspond inside H; ambient normality of H is not required. -/
theorem saturatedStarLift_normalizer (H J : Subgroup G)
    (B : Subgroup (H ⧸ pCore 2 H)) (hJ : (J.subgroupOf H).Normal)
    (hBJ : B ≤ starImage H J) :
    normalizer ((saturatedStarLift H J B).subgroupOf H : Set H) =
      (normalizer (B : Set (H ⧸ pCore 2 H))).comap
        (QuotientGroup.mk' (pCore 2 H)) := by
  apply le_antisymm
  · apply map_le_iff_le_comap.mp
    have hh := ((saturatedStarLift H J B).subgroupOf H).le_normalizer_map
      (QuotientGroup.mk' (pCore 2 H))
    change _ ≤ normalizer (starImage H (saturatedStarLift H J B) :
      Set (H ⧸ pCore 2 H)) at hh
    rwa [saturatedStarLift_image H J B hBJ] at hh
  · rw [saturatedStarLift_subgroupOf]
    apply le_normalizer_iff.mpr
    intro h hh j hj
    exact ⟨hJ.conj_mem j hj.1 h,
      le_normalizer_iff.mp (B.le_normalizer_comap _) h hh j hj.2⟩

theorem saturatedStarLift_conjugacy_card (H J : Subgroup G)
    (B : Subgroup (H ⧸ pCore 2 H)) (hJ : (J.subgroupOf H).Normal)
    (hBJ : B ≤ starImage H J) :
    (Set.range fun h : H => ((saturatedStarLift H J B).subgroupOf H).map
      (MulAut.conj h).toMonoidHom).ncard =
      (Set.range fun h : H ⧸ pCore 2 H => B.map (MulAut.conj h).toMonoidHom).ncard := by
  rw [ncard_conjugates_eq_index_normalizer, ncard_conjugates_eq_index_normalizer,
    saturatedStarLift_normalizer H J B hJ hBJ,
    index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)]

/-- Lift a specified quotient factor, deriving the ambient candidate fields.
The model, module rank, cubic identity and quotient orbit bound remain explicit. -/
noncomputable def solvableStarFactorOfImage
    (H ZS Z A : Subgroup G) [IsElementaryAbelian 2 (localSpan ZS H)]
    (action : SectionAction H (localSpan ZS H) Z) (hAH : A ≤ H)
    (B : Subgroup (H ⧸ pCore 2 H))
    (hBJ : B ≤ starImage H (localSpan A H))
    (hB : (B.subgroupOf (starImage H (localSpan A H))).IsSubnormal)
    (model : B ≃* Equiv.Perm (Fin 3))
    (hthree : (pCore 3 B).map B.subtype =
      ⁅(pCore 3 B).map B.subtype, starImage H A⁆)
    (hrank : Module.finrank (ZMod 2)
      (Representation.Coinvariants.ker (action.representation.comp B.subtype)) = 2)
    (horbit : (Set.range fun h : H ⧸ pCore 2 H =>
      B.map (MulAut.conj h).toMonoidHom).ncard ≤ 2) :
    SolvableStarFactor H ZS Z A action where
  carrier := saturatedStarLift H (localSpan A H) B
  le_span := saturatedStarLift_le H (localSpan A H) B
  kernel_le := saturatedStarLift_kernel_le H (localSpan A H) B
  subnormal := saturatedStarLift_subnormal H (localSpan A H) B
    (localSpan_normal A H hAH).isSubnormal hBJ hB
  model := (MulEquiv.subgroupCongr
    (saturatedStarLift_image H (localSpan A H) B hBJ)).trans model
  three_generation := by
    dsimp only [threeCoreImage]
    rw [saturatedStarLift_image H (localSpan A H) B hBJ]
    exact hthree
  commutator_rank := by
    rw [saturatedStarLift_image H (localSpan A H) B hBJ]
    exact hrank
  conjugacy_bound := by
    simpa only [saturatedStarLift_image H (localSpan A H) B hBJ] using horbit

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ClassificationCases
