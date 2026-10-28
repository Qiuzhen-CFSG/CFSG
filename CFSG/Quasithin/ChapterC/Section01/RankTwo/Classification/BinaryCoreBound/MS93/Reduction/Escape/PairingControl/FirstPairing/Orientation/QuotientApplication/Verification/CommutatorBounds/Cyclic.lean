module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Verification.Basic

/-!
# The cyclic commutator and its parabolic closure

The selected cyclic image lies in the actual moving-neighbor Z-image.
Consequently its pairing with Q has order at most four. The full natural
section places that pairing in B, but this is not yet containment in Z.

We prove the exact closure transfer: if the parabolic normalizes the cyclic
pairing, taking the relative normal closure does not enlarge it. Normality
is proved inside the parabolic, not imposed on the ambient quotient. It
suffices to prove normalization by the untilded residual: its projection
is the full model parabolic, and Q already normalizes the cyclic pairing.
Neither the missing residual normalization nor containment in Z is assumed
implicitly in these results.

Source: Meierfrankenfeld--Stellmacher (1993), printed p.883, the cyclic
commutator estimates before the first application of (1.7)(i), pp.847--848.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication
open RankOnePairing

private theorem localGenerated_commutator_eq_of_normalizes {G : Type*} [Group G]
    (P A W : Subgroup G) [W.Normal]
    (hAP : A ≤ P) (hWP : W ≤ P)
    (hn : P ≤ normalizer (⁅A, W⁆ : Subgroup G)) :
    ⁅localGenerated P A, W⁆ = ⁅A, W⁆ := by
  let K := ⁅A, W⁆
  let : (K.subgroupOf P).Normal := normal_subgroupOf_of_le_normalizer hn
  have hKP : K ≤ P := (Subgroup.commutator_le_sup _ _).trans (sup_le hAP hWP)
  have hnative : ⁅W.subgroupOf P, A.subgroupOf P⁆ ≤ K.subgroupOf P := by
    rw [commutator_comm, ← commutator_subgroupOf P A W hAP hWP]
  have hbound := commutator_normalClosure_le_of_normal
    (W.subgroupOf P) (A.subgroupOf P) (K.subgroupOf P) hnative
  have hm := map_mono (f := P.subtype) hbound
  rw [map_commutator, map_subgroupOf_eq_of_le hWP,
    map_subgroupOf_eq_of_le hKP, commutator_comm] at hm
  exact le_antisymm hm (commutator_mono (le_localGenerated P A hAP) le_rfl)

variable {M : Type*} [Group M] {L R : Subgroup M}
  {geometry : Geometry R} {a : Vertex R} {f : FrameAt a}

namespace SelectedSeed
variable (s : SelectedSeed geometry a f)

/-- The original selected element gives a literal subgroup containment in the neighbor image. -/
theorem cyclic_le_neighbor_image :
    zpowers (quotientMap a s.element) ≤ quotientImage a (Z R s.neighbor) :=
  zpowers_le.mpr (mem_map_of_mem _ s.element_mem)

/-- The right factor normalizes the cyclic commutator before any parabolic extension. -/
theorem cyclic_commutator_normalized_Q :
    quotientImage a (Q R a) ≤ normalizer
      (⁅zpowers (quotientMap a s.element), quotientImage a (Q R a)⁆ :
        Subgroup (LocalQuotient a)) :=
  normalizer_commutator_ge_right _ _

/-- The section's triple bound puts the cyclic pairing in the original fixed preimage B. -/
theorem cyclic_commutator_le_B :
    ⁅zpowers (quotientMap a s.element), quotientImage a (Q R a)⁆ ≤
      quotientImage a (B R a (geometry.Z_normal a)) := by
  let := f.natural_section.normal_group
  let := geometry.Z_normal a
  have hnative : ⁅(V R a).subgroupOf (stabilizer R a),
      (Q R a).subgroupOf (stabilizer R a)⁆ ≤
      (B R a (geometry.Z_normal a)).subgroupOf (stabilizer R a) := by
    intro x hx
    change (x : FreeAmalgam R) ∈ B R a (geometry.Z_normal a)
    apply mem_map_of_mem (stabilizer R a).subtype
    apply mem_centralizerModulo_iff.mpr
    refine ⟨commutator_le_left _ _ hx, ?_⟩
    intro l hl
    apply f.natural_section.triple_le
    rw [commutator_comm]
    exact commutator_mem_commutator hl hx
  have hm := map_mono (f := quotientMap a) hnative
  rw [map_commutator] at hm
  change ⁅quotientImage a (V R a), quotientImage a (Q R a)⁆ ≤
    quotientImage a (B R a (geometry.Z_normal a)) at hm
  have hseed : zpowers (quotientMap a s.element) ≤ quotientImage a (V R a) :=
    zpowers_le.mpr (mem_map_of_mem _ (moving_Z_le_V s.moving s.element_mem))
  exact (commutator_mono hseed le_rfl).trans hm

variable [Finite M]

/-- The neighbor estimate bounds the cyclic pairing itself in the literal quotient. -/
theorem cyclic_commutator_card_le_four (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (ha : color R a = false) :
    Nat.card (⁅zpowers (quotientMap a s.element), quotientImage a (Q R a)⁆ :
      Subgroup (LocalQuotient a)) ≤ 4 := by
  have hle := commutator_mono s.cyclic_le_neighbor_image (le_refl (quotientImage a (Q R a)))
  exact (Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective _)).trans
    (quotient_moving_commutator_card_le_four source hb modules ha s.moving)

/-- The actual residual image and Q together generate the parabolic. -/
theorem parabolic_le_normalizer_cyclic_of_residual (source : LocalSource L R)
    (ha : color R a = false)
    (hn : localResidual (parabolic (projection f) s.flag s.side) ≤ normalizer
      (⁅zpowers (quotientMap a s.element), quotientImage a (Q R a)⁆ :
        Subgroup (LocalQuotient a))) :
    parabolic (projection f) s.flag s.side ≤ normalizer
      (⁅zpowers (quotientMap a s.element), quotientImage a (Q R a)⁆ :
        Subgroup (LocalQuotient a)) := by
  have hm := localResidual_map (s.extension source ha) s.side
  rw [s.localParabolic_extension source ha, s.extension_projection source ha,
    s.extension_flag source ha] at hm
  have hcover : parabolic (projection f) s.flag s.side =
      localResidual (parabolic (projection f) s.flag s.side) ⊔ quotientImage a (Q R a) := by
    calc
      _ = ((localResidual (parabolic (projection f) s.flag s.side)).map
          (projection f)).comap (projection f) := by rw [hm]; rfl
      _ = _ := by rw [comap_map_eq, projection, quotientProjection_kernel]
  exact hcover.le.trans (sup_le hn s.cyclic_commutator_normalized_Q)

/-- Relative invariance, when supplied, justifies passing the estimate through the closure. -/
theorem X_commutator_Q_eq_cyclic_of_normalized
    (hb : 2 < geometry.b R) (ha : color R a = false)
    (hn : parabolic (projection f) s.flag s.side ≤ normalizer
      (⁅zpowers (quotientMap a s.element), quotientImage a (Q R a)⁆ :
        Subgroup (LocalQuotient a))) :
    ⁅s.X, quotientImage a (Q R a)⁆ =
      ⁅zpowers (quotientMap a s.element), quotientImage a (Q R a)⁆ := by
  let := quotientImage_normal a (Q R a) (Q_normalized R a)
  rw [s.X_commutator_Q ha]
  apply localGenerated_commutator_eq_of_normalizes _ _ _ _ (s.Q_le_parabolic s.side) hn
  exact (s.cyclic_le_X hb ha).trans (s.X_le_parabolic hb ha s.side)

end SelectedSeed
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication
