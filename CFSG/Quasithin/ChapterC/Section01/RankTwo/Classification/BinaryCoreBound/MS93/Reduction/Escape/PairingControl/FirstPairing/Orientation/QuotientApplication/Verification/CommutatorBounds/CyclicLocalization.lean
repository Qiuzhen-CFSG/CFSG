module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Verification.CommutatorBounds.CyclicLocalization.Transport

/-!
# Localization of the selected cyclic pairing

In the literal quotient G_alpha/D_alpha, adjoin the natural Z-image to the
cyclic commutator K. The earlier section places K in B, so KZ is normal and
has trivial component action modulo Z. Its order-four bound forces Q to
centralize KZ. The faithful fixed-core quotient and the actual natural
coordinates therefore give a natural-by-trivial binary module with zero
fixed space. Residual normalization extends to the marked parabolic, whose
four-group and the checked cocycle calculation force K into Z.

Only the residual normalization remains an explicit premise. In particular,
this does not use the later pairing bounds or assume coordinates on K.

Source: Meierfrankenfeld--Stellmacher (1993), printed p.883, the containment
before the first application of (1.7)(i), pp.847--848.
-/
public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication
open RankOnePairing CyclicLocalization
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {geometry : Geometry R} {a : Vertex R} {f : FrameAt a}
namespace SelectedSeed

/-- The conditional cyclic localization needed for the first application of
MS93 (1.7). Normalization is relative to the actual untilded residual. -/
theorem cyclic_commutator_le_Z_of_residual_normalized
    (s : SelectedSeed geometry a f) (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (ha : color R a = false)
    (hn : localResidual (parabolic (projection f) s.flag s.side) ≤ normalizer
      (⁅zpowers (quotientMap a s.element), quotientImage a (Q R a)⁆ :
        Subgroup (LocalQuotient a))) :
    ⁅zpowers (quotientMap a s.element), quotientImage a (Q R a)⁆ ≤
      quotientImage a (Z R a) := by
  let := quotientImage_normal a (Z R a) (Z_normalized R a)
  let := s.cyclicLayer_normal source ha
  let := s.cyclicLayer_elementary hb modules ha
  have hπ : Function.Surjective (projection f) :=
    quotientProjection_surjective a _ f.natural_section.projection_surjective _
  have hZQ : quotientImage a (Z R a) ≤ quotientImage a (Q R a) :=
    (show quotientImage a (Z R a) ≤ s.cyclicLayer from le_sup_left).trans
      (s.cyclicLayer_le_Q hb ha)
  have hcomm : ⁅s.cyclicLayer, component (projection f) s.flag⁆ ≤ quotientImage a (Z R a) := by
    have hpre : s.cyclicLayer ≤ commutatorPreimage (quotientImage a (Q R a))
        (component (projection f) s.flag) (quotientImage a (Z R a)) :=
      sup_le (le_commutatorPreimage hZQ (commutator_le_left _ _))
        (le_commutatorPreimage s.cyclicPairing_le_Q (s.cyclicPairing_component source ha))
    exact (commutator_mono hpre le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ le_normalizer_of_normal)
  exact small_layer_le_natural (projection f) hπ (quotientImage a (Q R a))
    (component (projection f) s.flag) (quotientImage a (Z R a)) s.cyclicLayer s.cyclicPairing
    (quotientProjection_kernel a _ _) (component_map _ hπ _) (naturalZ modules a ha f)
    le_sup_left le_sup_right (s.cyclicLayer_le_Q hb ha)
    (s.cyclicLayer_centralizes_Q source hb modules ha) hcomm
    (quotient_Q_fixed_eq_bot source ha f s.flag) s.flag s.side
    (s.cyclic_commutator_card_le_four source hb modules ha)
    (s.parabolic_le_normalizer_cyclic_of_residual source ha hn)

end SelectedSeed
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication
