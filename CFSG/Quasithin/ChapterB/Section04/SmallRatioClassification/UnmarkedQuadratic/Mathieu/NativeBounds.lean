module

public import CFSG.Quasithin.ChapterB.Section04.SmallRatioClassification.UnmarkedQuadratic
public import CFSG.Quasithin.ChapterK.Section01To04.Mathieu.CocodePreliminary
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.SourceFF.MathieuTwentyThree
public import Theory.Representation.MathieuCodeRestriction.QuadraticActors.StrictCode

/-!
# Strict quadratic bounds for the large Mathieu actions

The native code calculation and the cocode fixed-space calculation exclude
quadratic ratio at most two. For the cocode, the checked quadratic-actor bound
gives rank at most two, whereas K.4.1 forces a small actor to have larger rank.
Equivariant transport retains the whole ambient action.

The proved cubic source recognition discharges both degree and module marking
for M23, including arbitrary central covers at the input. The M24 estimates
below concern the actual marked code and cocode; they do not assert completeness
of the source M24 module list.

Source: Aschbacher--Smith B.4.5 and K.4.1--3, printed pp.87,458--459.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Sporadic.Mathieu MathieuCode
namespace CFSG.Quasithin.ChapterB.SmallRatioClassification.UnmarkedQuadratic.Mathieu

/-- The native M24 cocode has no quadratic actor of ratio at most two. -/
theorem cocode_quadraticRatio_gt_two : 2 < quadraticRatio cocodeRepresentation := by
  by_contra! hle
  obtain ⟨A, hA, hq, hsmall⟩ :=
    (quadraticRatio_le_iff cocodeRepresentation (by simp)).mp hle
  let : IsElementaryAbelian 2 A := hA.2
  have hcard := QuadraticActors.m24_cocode_card_le_four A hq
  have hr : rank A ≤ 2 :=
    (Nat.log_mono_right hcard : Nat.log 2 (Nat.card A) ≤ Nat.log 2 4)
  have hlarge := ChapterK.Mathieu.m24_cocode_small_actor_rank A hA
    ((actionRatio_le_nat_iff cocodeRepresentation hA 2).mp hsmall)
  omega

/-- The native point-stabilizer restriction preserves the strict cocode bound. -/
theorem m23Cocode_quadraticRatio_gt_two : 2 < quadraticRatio m23CocodeRepresentation :=
  cocode_quadraticRatio_gt_two.trans_le
    (quadraticRatio_le_of_injective_equivariant m23CocodeRepresentation cocodeRepresentation
      pointEmbedding pointEmbedding_injective (LinearEquiv.refl _ _) (fun _ _ => rfl))

universe u v
variable {G : Type u} [Group G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

/-- Transport the native code estimate through the literal M23 marking. -/
theorem quadraticRatio_gt_two_of_m23Code (h : IsM23Code ρ) : 2 < quadraticRatio ρ := by
  obtain ⟨e, E, hE⟩ := h
  exact QuadraticActors.StrictCode.m23Code_quadraticRatio_gt_two.trans_le
    (quadraticRatio_le_of_injective_equivariant ρ m23CodeRepresentation
      e.toMonoidHom e.injective E hE)

/-- Transport the native cocode estimate through the literal M23 marking. -/
theorem quadraticRatio_gt_two_of_m23Cocode (h : IsM23Cocode ρ) : 2 < quadraticRatio ρ := by
  obtain ⟨e, E, hE⟩ := h
  exact m23Cocode_quadraticRatio_gt_two.trans_le
    (quadraticRatio_le_of_injective_equivariant ρ m23CocodeRepresentation
      e.toMonoidHom e.injective E hE)

/-- Both genuine native M24 module markings have strict quadratic ratio. -/
theorem quadraticRatio_gt_two_of_m24ToddOrDual (h : MathieuSmall.IsM24ToddOrDual ρ) :
    2 < quadraticRatio ρ := by
  rcases h with ⟨e, hc | hd⟩
  · obtain ⟨E⟩ := hc
    exact cocode_quadraticRatio_gt_two.trans_le
      (quadraticRatio_le_of_injective_equivariant ρ cocodeRepresentation
        e.toMonoidHom e.injective E.toLinearEquiv
        (fun g v => LinearMap.congr_fun (E.isIntertwining' g) v))
  · obtain ⟨E⟩ := hd
    exact QuadraticActors.StrictCode.code_quadraticRatio_gt_two.trans_le
      (quadraticRatio_le_of_injective_equivariant ρ codeRepresentation
        e.toMonoidHom e.injective E.toLinearEquiv
        (fun g v => LinearMap.congr_fun (E.isIntertwining' g) v))

variable [Finite G] [FiniteDimensional (ZMod 2) V] {L : Subgroup G}

open ComponentRecognition.KnownFFTypes.Sporadic.LargeMathieu in
/-- The original cubic source hypotheses recognize M23 without any additional
degree, small-displacement, FF, or module-marking assumption. -/
theorem m23_quadraticRatio_gt_two (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (he : Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.m23.Carrier)) :
    2 < quadraticRatio ρ := by
  rcases h.fitting with rfl
  obtain ⟨e⟩ := he
  have hs : SourceHypotheses ρ :=
    ⟨h.sqtk, h.quasisimple, h.faithful, h.irreducible, h.smallCubic⟩
  obtain ⟨_, _, hc | hd⟩ := source_m23_of_degree_and_small_recognition
    ChapterK.SporadicCatalogue.SourceFF.m23_degree_eleven m23SmallRecognition ρ hs e
  · exact quadraticRatio_gt_two_of_m23Code hc
  · exact quadraticRatio_gt_two_of_m23Cocode hd

/-- Exclude the actual M23 central quotient from the small-quadratic source. -/
theorem no_m23 (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (hq : quadraticRatio ρ ≤ 2)
    (he : Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.m23.Carrier)) : False :=
  (not_lt_of_ge hq) (m23_quadraticRatio_gt_two h he)

open Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases in
/-- The M23 constructor of the remaining-model sieve is impossible under the
literal B.4 hypotheses and the quadratic bound. -/
theorem b4_no_m23 [Finite V] (h : B4Hypotheses KnownSimple.IsKnownSimple ρ)
    (hq : quadraticRatio ρ ≤ 2)
    (he : Nonempty (generalizedFitting G ⧸ center (generalizedFitting G) ≃*
      KnownSimple.SporadicName.m23.Carrier)) : False :=
  no_m23 ⟨h.sqtk, rfl, h.quasisimple, h.faithful, h.irreducible,
    (Representation.BinaryOffender.cubicRatio_le_quadraticRatio ρ).trans hq⟩ hq he

end CFSG.Quasithin.ChapterB.SmallRatioClassification.UnmarkedQuadratic.Mathieu
