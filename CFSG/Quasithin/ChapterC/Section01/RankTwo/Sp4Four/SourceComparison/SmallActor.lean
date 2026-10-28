module
public import Theory.SpecificGroups.SymplecticFour.ReciprocalSmallActors
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.TopLayerBound
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Factorization.Offenders
/-!
# Reciprocal critical seed images of order four

The exact centralizer kernels turn opposite natural image orders into the
original seed indices. Surjective natural quotients of the moving layers
bound those indices below by natural fixed quotients. Critical noncommutation
and the reciprocal comparison then force order four and displacement lines
once one inner image has order less than sixteen.

This is the small-inner-actor step of MS93 (3.3), printed p.867. The two inner
maps remain explicit; the ambient field-twist case is discharged separately.
-/

public section
noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
variable {M : Type*} [Group M] {R : Subgroup M}
  {geometry : Geometry R} {a e : Vertex R}

theorem critical_reverse_actor_normalizes_moving (path : CriticalPath R geometry a e) :
    Z R e ≤ normalizer (U R a : Set (FreeAmalgam R)) := by
  apply (Z_le_stabilizer_of_dist_le e (geometry.exists_critical e path.end_color) ?_).trans
    (U_normalized a)
  rw [SimpleGraph.dist_comm,path.critical.1,geometry.distance_constant a path.start_color,
    geometry.distance_constant e path.end_color]

variable [Finite M] {F : Type*} [Field F] [Finite F]

theorem critical_small_inner_actor_card_four_of_fields
    {K : Type*} [Field K] [Finite K]
    (path : CriticalPath R geometry a e) (hb : 0 < geometry.b R)
    (hC : EdgeCentralizerCondition R) (hF : Nat.card F=4) (hK : Nat.card K=4)
    (πe : U R e →* Multiplicative (Vector F)) (hpe : Function.Surjective πe)
    (πa : U R a →* Multiplicative (Vector K)) (hpa : Function.Surjective πa)
    (α : Z R a →* Sp F) (β : Z R e →* Sp K)
    (hαker : α.ker = (centralizer (Z R e : Set (FreeAmalgam R))).subgroupOf (Z R a))
    (hβker : β.ker = (centralizer (Z R a : Set (FreeAmalgam R))).subgroupOf (Z R e))
    (hα : ∀ (z : Z R a) (u : U R e),
      πe ⟨z.val*u.val*z.val⁻¹,
        (mem_normalizer_iff.mp (critical_actor_normalizes_moving path z.property) u.val).mp u.property⟩ =
          Multiplicative.ofAdd (α z • (πe u).toAdd))
    (hβ : ∀ (z : Z R e) (u : U R a),
      πa ⟨z.val*u.val*z.val⁻¹,
        (mem_normalizer_iff.mp (critical_reverse_actor_normalizes_moving path z.property) u.val).mp u.property⟩ =
          Multiplicative.ofAdd (β z • (πa u).toAdd))
    (hsmall : Nat.card α.range < 16) :
    Nat.card α.range=4 ∧ Nat.card β.range=4 ∧
      Module.finrank F (displacementSpace α.range)=1 ∧
      Module.finrank K (displacementSpace β.range)=1 := by
  let := finite_Z R a
  let := finite_Z R e
  let : Finite (U R e) := Finite.of_injective (inclusion (U_le_Z e)) (inclusion_injective _)
  let : Finite (U R a) := Finite.of_injective (inclusion (U_le_Z a)) (inclusion_injective _)
  have hia : (centralizer (Z R e : Set (FreeAmalgam R))).relIndex (Z R a) =
      Nat.card α.range := by
    change ((centralizer (Z R e : Set (FreeAmalgam R))).subgroupOf (Z R a)).index = _
    rw [←hαker,index_ker]
  have hie : (centralizer (Z R a : Set (FreeAmalgam R))).relIndex (Z R e) =
      Nat.card β.range := by
    change ((centralizer (Z R a : Set (FreeAmalgam R))).subgroupOf (Z R e)).index = _
    rw [←hβker,index_ker]
  have hB : 1 < Nat.card β.range := by
    have hp : 0 < Nat.card β.range := Nat.card_pos
    have hn : Nat.card β.range ≠ 1 := by
      intro he
      have hz := relIndex_eq_one.mp (hie.trans he)
      have hc := commutator_eq_bot_iff_le_centralizer.mpr hz
      rw [commutator_comm] at hc
      exact critical_noncommutation R geometry hC a path.start_color
        (by rwa [geometry.distance_constant a path.start_color]) path.critical hc
    omega
  have hAB : Nat.card (Vector F ⧸ TwoLocalCover.fixedSpace α.range) ≤ Nat.card β.range := by
    have h := fixed_quotient_card_le_centralizer_index (U R e) (Z R a)
      (critical_actor_normalizes_moving path) πe hpe α hα
    apply h.trans
    rw [←hie]
    exact relIndex_le_of_le_right (U_le_Z e) index_ne_zero_of_finite
  have hBA : Nat.card (Vector K ⧸ TwoLocalCover.fixedSpace β.range) ≤ Nat.card α.range := by
    have h := fixed_quotient_card_le_centralizer_index (U R a) (Z R e)
      (critical_reverse_actor_normalizes_moving path) πa hpa β hβ
    apply h.trans
    rw [←hia]
    exact relIndex_le_of_le_right (U_le_Z a) index_ne_zero_of_finite
  exact reciprocal_small_actor_card_four_of_fields hF hK α.range β.range hB hAB hBA hsmall

theorem critical_small_inner_actor_card_four
    (path : CriticalPath R geometry a e) (hb : 0 < geometry.b R)
    (hC : EdgeCentralizerCondition R) (hF : Nat.card F=4)
    (πe : U R e →* Multiplicative (Vector F)) (hpe : Function.Surjective πe)
    (πa : U R a →* Multiplicative (Vector F)) (hpa : Function.Surjective πa)
    (α : Z R a →* Sp F) (β : Z R e →* Sp F)
    (hαker : α.ker = (centralizer (Z R e : Set (FreeAmalgam R))).subgroupOf (Z R a))
    (hβker : β.ker = (centralizer (Z R a : Set (FreeAmalgam R))).subgroupOf (Z R e))
    (hα : ∀ (z : Z R a) (u : U R e),
      πe ⟨z.val*u.val*z.val⁻¹,
        (mem_normalizer_iff.mp (critical_actor_normalizes_moving path z.property) u.val).mp u.property⟩ =
          Multiplicative.ofAdd (α z • (πe u).toAdd))
    (hβ : ∀ (z : Z R e) (u : U R a),
      πa ⟨z.val*u.val*z.val⁻¹,
        (mem_normalizer_iff.mp (critical_reverse_actor_normalizes_moving path z.property) u.val).mp u.property⟩ =
          Multiplicative.ofAdd (β z • (πa u).toAdd))
    (hsmall : Nat.card α.range < 16) :
    Nat.card α.range=4 ∧ Nat.card β.range=4 ∧
      Module.finrank F (displacementSpace α.range)=1 ∧
      Module.finrank F (displacementSpace β.range)=1 :=
  critical_small_inner_actor_card_four_of_fields path hb hC hF hF
    πe hpe πa hpa α β hαker hβker hα hβ hsmall
end CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
