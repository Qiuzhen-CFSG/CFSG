module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.QuasisimpleDoubleCenters
public import Theory.GroupTheory.PerfectCentralCoverCompatibleComparison
public import Theory.SpecificGroups.J2HSMultipliers.HSDoubleCover
public import Theory.SpecificGroups.Rudvalis.Multiplier.DoubleCover

/-!
# The literal HS and Ru double covers at the nonsingular point

The covering center has already been proved to be the original local fixed
line. Its order is two, so the genuine universal-kernel bound identifies K_v
with the constructed perfect double cover. Both identifications commute with
the original central projection followed by the supplied simple-model map.
They therefore retain the original L_v and V_v images without a new choice
of action or quotient convention.

The final consumer constructs the preferred escaping point and attaches these
actual comparisons to the remaining HS/Ru/J4 catalogue. The local exclusions,
blocks, splitting and fixed-space elimination are still required; neither
12.6.2 nor 12.6.23 is asserted. Earlier invariance and TI retain producer
qt-d-1222-source and final discharge owner qt-d-12634-source.

Source: Aschbacher--Smith, proof of 12.6.12, pp.825--826; I.1.1--3, p.407.
-/

public section
open Subgroup Theory.GroupTheory PerfectCentralCovering
namespace CFSG.Quasithin.Chapter12.Section06

/-- The remaining models with actual maps from the covering group. The two
double-cover alternatives retain their commuting central-quotient triangles. -/
@[expose] def NonsingularRemainingCoverModels (C : Type*) [Group C] : Prop :=
  (∃ hp : Group.IsPerfect Sporadic.LeechRelated.HS.Carrier,
    letI := hp
    ∃ (e : (C ⧸ center C) ≃* Sporadic.LeechRelated.HS.Carrier)
      (f : C ≃* Theory.SpecificGroups.J2HSMultipliers.HS.DoubleCover),
      ∀ x, Theory.SpecificGroups.J2HSMultipliers.HS.projection (f x) =
        e (QuotientGroup.mk' (center C) x)) ∨
  (∃ (e : (C ⧸ center C) ≃* Rudvalis.Model)
      (f : C ≃* Rudvalis.Multiplier.DoubleCover.Carrier),
      ∀ x, Rudvalis.Multiplier.DoubleCover.covering.toMonoidHom (f x) =
        e (QuotientGroup.mk' (center C) x)) ∨
  Nonempty ((C ⧸ center C) ≃* Janko4.Model)

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The original HS residual is the concrete perfect double cover, with its
literal central projection preserved. -/
theorem SourceHypothesis.nonsingular_hs_doubleCover
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.LeechRelated.HS.Carrier) :
    letI : IsQuasisimple (Kv (v : G)) := hK
    letI : Group.IsPerfect Sporadic.LeechRelated.HS.Carrier :=
      Group.IsPerfect.ofSurjective
        (f := e.toMonoidHom.comp (QuotientGroup.mk' (center (Kv (v : G)))))
        (e.surjective.comp (QuotientGroup.mk'_surjective _))
    ∃ f : Kv (v : G) ≃* Theory.SpecificGroups.J2HSMultipliers.HS.DoubleCover,
      ∀ x, Theory.SpecificGroups.J2HSMultipliers.HS.projection (f x) =
        e (QuotientGroup.mk' (center (Kv (v : G))) x) := by
  let := hK
  let c := centralQuotientCover e
  let : Group.IsPerfect Sporadic.LeechRelated.HS.Carrier :=
    Group.IsPerfect.ofSurjective (f := c.toMonoidHom) c.surjective
  let u := universalCover Sporadic.LeechRelated.HS.Carrier
  have hp := Theory.SpecificGroups.J2HSMultipliers.HS.kernel_isPGroup
    u.toMonoidHom u.surjective u.ker_le_center
  have hn := Theory.SpecificGroups.J2HSMultipliers.HS.TwoPrimary.not_four_dvd_card_kernel
    u.toMonoidHom u.surjective u.ker_le_center hp
  have hb := Theory.SpecificGroups.J2HSMultipliers.HS.card_kernel_le_two_of_not_four_dvd
    u.toMonoidHom u.surjective u.ker_le_center hn
  simp only [u,universalCover] at hb
  have hc : Nat.card c.toMonoidHom.ker = 2 := by
    rw [centralQuotientCover_ker]
    exact H.nonsingular_hs_ru_center_card D v hv hK (.inl ⟨e⟩)
  exact c.exists_mulEquiv_over_of_kernel_bound Theory.SpecificGroups.J2HSMultipliers.HS.cover
    (by simpa only [hc] using hb)
    (by simpa only [Theory.SpecificGroups.J2HSMultipliers.HS.cover,
      Theory.SpecificGroups.J2HSMultipliers.HS.kernel_card] using hb)

/-- The original Ru residual is the concrete perfect double cover, with its
literal central projection preserved in every ambient universe. -/
theorem SourceHypothesis.nonsingular_ru_doubleCover
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Rudvalis.Model) :
    ∃ f : Kv (v : G) ≃* Rudvalis.Multiplier.DoubleCover.Carrier,
      ∀ x, Rudvalis.Multiplier.DoubleCover.covering.toMonoidHom (f x) =
        e (QuotientGroup.mk' (center (Kv (v : G))) x) := by
  let := hK
  let c := centralQuotientCover e
  have hb := Rudvalis.Multiplier.kernel_card_le_two (universalCover Rudvalis.Model)
  simp only [universalCover] at hb
  have hc : Nat.card c.toMonoidHom.ker = 2 := by
    rw [centralQuotientCover_ker]
    exact H.nonsingular_hs_ru_center_card D v hv hK (.inr ⟨e⟩)
  exact c.exists_mulEquiv_over_of_kernel_bound Rudvalis.Multiplier.DoubleCover.covering
    (by simpa only [hc] using hb)
    (by simpa only [Rudvalis.Multiplier.DoubleCover.kernel_card_two] using hb)

/-- The actual model catalogue now identifies both covering groups and their
projections. This does not exclude any of its three remaining alternatives. -/
theorem SourceHypothesis.nonsingular_quasisimple_marked_cover_models
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G))) :
    NonsingularRemainingCoverModels (Kv (v : G)) := by
  let := hK
  obtain ⟨name,hn,⟨e⟩⟩ := H.nonsingular_quasisimple_models_after_held D v hv hK
  rcases hn with rfl | rfl | rfl
  · let hp : Group.IsPerfect Sporadic.LeechRelated.HS.Carrier :=
      Group.IsPerfect.ofSurjective
        (f := e.toMonoidHom.comp (QuotientGroup.mk' (center (Kv (v : G)))))
        (e.surjective.comp (QuotientGroup.mk'_surjective _))
    obtain ⟨f,hf⟩ := H.nonsingular_hs_doubleCover D v hv hK e
    exact .inl ⟨hp,e,f,hf⟩
  · obtain ⟨f,hf⟩ := H.nonsingular_ru_doubleCover D v hv hK e
    exact .inr (.inl ⟨e,f,hf⟩)
  · exact .inr (.inr ⟨e⟩)

/-- Apply the marked covering catalogue at the literal preferred escaping
point, together with its original component and Sylow conclusions. Earlier
invariance and TI retain producer qt-d-1222-source and final discharge owner
qt-d-12634-source. -/
theorem SourceHypothesis.exists_preferred_nonsingular_marked_cover_models
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ∃ w : V, D.Nonsingular w ∧ ¬ Gv (w : G) ≤ M L ∧
      Chapter1.IsSylowIn 2 (Tv T (w : G)) (Mv L (w : G)) ∧
      (Tv T (w : G)).relIndex (T : Subgroup G) = 4 ∧
      Lv L (w : G) < Kv (w : G) ∧ ¬ Kv (w : G) ≤ M L ∧
      ((Kv (w : G)).subgroupOf (Gv (w : G))).IsCComponent ∧
      IsQuasisimple (Star (Kv (w : G))) ∧ IsSimpleGroup (Star (Kv (w : G))) ∧
      (IsQuasisimple (Kv (w : G)) →
        NonsingularRemainingCoverModels (Kv (w : G)) ∧
        (Stellmacher.elementaryAbelianMaxJ (Tv T (w : G)) ≤ Q T L →
          Nonempty (((Kv (w : G)) ⧸ center (Kv (w : G))) ≃* Janko4.Model))) := by
  obtain ⟨w,hw,he,hs,hi,hlt,hnot,hc,hq,hsimple⟩ :=
    H.exists_preferred_nonsingular_component_escape D hTV hTI v hv he
  exact ⟨w,hw,he,hs,hi,hlt,hnot,hc,hq,hsimple,fun hK =>
    ⟨H.nonsingular_quasisimple_marked_cover_models D w hw hK,
      fun hJ => H.nonsingular_quasisimple_small_thompson_jankoFour D w hw hTV hs hJ hK⟩⟩

end CFSG.Quasithin.Chapter12.Section06
