module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction.Configuration
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.ExtensionControl.Dimension

/-!
# The backward radius image in the actual local quotient

Form Gₐ/Qₐ using relative normality inside the stabilizer, and map Vδ
through the quotient map. The constructed path makes this image nontrivial
and elementary abelian. The transported source projection identifies the
quotient with SL₃(2); its proved elementary-rank bound restricts the image
to order two or four. The remaining R₁ calculation must exclude four.

All cardinalities refer to this literal image, equivalently to
[Vδ : Vδ intersect Qₐ]. No order-two index or module marking is assumed.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.2), printed p.893, the R₁ index calculation.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}

/-- Qₐ considered inside Gₐ, where it is normal. -/
def localKernel (a : Vertex R) : Subgroup (stabilizer R a) :=
  (Q R a).subgroupOf (stabilizer R a)
instance localKernel_normal (a : Vertex R) : (localKernel a).Normal := Q_normal R a
/-- The actual quotient Gₐ/Qₐ. -/
abbrev LocalQuotient (a : Vertex R) := stabilizer R a ⧸ localKernel a
def quotientMap (a : Vertex R) : stabilizer R a →* LocalQuotient a :=
  QuotientGroup.mk' (localKernel a)
/-- The image of a local subgroup under the literal quotient map. -/
noncomputable def quotientImage (a : Vertex R) (E : Subgroup (FreeAmalgam R)) :
    Subgroup (LocalQuotient a) := (E.subgroupOf (stabilizer R a)).map (quotientMap a)

/-- Image order is the relative index [E : E intersect Qₐ]. -/
theorem quotientImage_card (a : Vertex R) (E : Subgroup (FreeAmalgam R))
    (hE : E ≤ stabilizer R a) : Nat.card (quotientImage a E) = (Q R a).relIndex E := by
  rw [quotientImage, ← relIndex_ker, quotientMap, QuotientGroup.ker_mk', localKernel,
    subgroupOf, relIndex_comap, map_subgroupOf_eq_of_le hE]

theorem quotientImage_eq_bot_iff (a : Vertex R) (E : Subgroup (FreeAmalgam R))
    (hE : E ≤ stabilizer R a) : quotientImage a E = ⊥ ↔ E ≤ Q R a := by
  rw [quotientImage, Subgroup.map_eq_bot_iff, quotientMap, QuotientGroup.ker_mk']
  constructor
  · intro h x hx
    exact h (show (⟨x, hE hx⟩ : stabilizer R a) ∈ E.subgroupOf _ from hx)
  · intro h x hx
    exact h hx

theorem quotientImage_elementary (a : Vertex R) (E : Subgroup (FreeAmalgam R))
    (hE : E ≤ stabilizer R a) [IsElementaryAbelian 2 E] :
    IsElementaryAbelian 2 (quotientImage a E) := by
  let := IsElementaryAbelian.subgroupOf (p := 2) hE
  exact IsElementaryAbelian.map (quotientMap a)

/-- Transport the source projection, then use its exact kernel for the quotient isomorphism. -/
theorem exists_quotient_equiv [Finite M] (source : LocalSource L R)
    (a : Vertex R) (ha : color R a = false) : Nonempty (LocalQuotient a ≃* SL) := by
  obtain ⟨π, hπ, hk⟩ := Escape.Initial.Natural.exists_localProjection source a ha
  change π.ker = localKernel a at hk
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective π hπ)⟩

theorem quotientImage_card_le_four [Finite M] (source : LocalSource L R)
    (a : Vertex R) (ha : color R a = false) (E : Subgroup (FreeAmalgam R))
    (hE : E ≤ stabilizer R a) [IsElementaryAbelian 2 E] :
    Nat.card (quotientImage a E) ≤ 4 := by
  obtain ⟨e⟩ := exists_quotient_equiv source a ha
  let := quotientImage_elementary a E hE
  let A := (quotientImage a E).map e.toMonoidHom
  have hA : IsElementaryAbelian 2 A := IsElementaryAbelian.map e.toMonoidHom
  have hc : Nat.card (quotientImage a E) = Nat.card A :=
    Nat.card_congr ((quotientImage a E).equivMapOfInjective e.toMonoidHom e.injective).toEquiv
  rw [hc]
  by_cases hn : A = ⊥
  · simp [hn]
  have htwo : Representation.BinaryOffender.IsElementaryTwo A := ⟨hn, hA⟩
  rw [htwo.card_eq_two_pow_rank]
  exact Nat.pow_le_pow_right (by decide : 0 < 2)
    (AbelianCore.QuotientRecognition.ExtensionControl.elementary_rank_le_two A hA)

namespace Configuration
variable {a a' : Vertex R} {p : CriticalPath R geometry a a'}
  (s : Configuration p) (hb : 4 < geometry.b R)

include hb

theorem backward_image_ne_bot {source : LocalSource L R}
    (common : CommonFacts R source geometry) : quotientImage a (V R s.delta) ≠ ⊥ := by
  rw [ne_eq, quotientImage_eq_bot_iff _ _ (s.radius_le_start_stabilizer hb)]
  exact s.radius_not_le_start_kernel hb common

theorem backward_image_card : Nat.card (quotientImage a (V R s.delta)) =
    (Q R a).relIndex (V R s.delta) :=
  quotientImage_card _ _ (s.radius_le_start_stabilizer hb)

theorem backward_image_elementary : IsElementaryAbelian 2 (quotientImage a (V R s.delta)) := by
  let := s.radius_elementary hb
  exact quotientImage_elementary _ _ (s.radius_le_start_stabilizer hb)

theorem one_lt_backward_index [Finite M] {source : LocalSource L R}
    (common : CommonFacts R source geometry) : 1 < (Q R a).relIndex (V R s.delta) := by
  let := finite_stabilizer R a
  let : Finite (V R s.delta) := Finite.of_injective
    (inclusion (s.radius_le_start_stabilizer hb)) (inclusion_injective _)
  have hzero : (Q R a).relIndex (V R s.delta) ≠ 0 :=
    ((Q R a).subgroupOf (V R s.delta)).index_ne_zero_of_finite
  have hone : (Q R a).relIndex (V R s.delta) ≠ 1 := by
    rw [ne_eq, relIndex_eq_one]
    exact s.radius_not_le_start_kernel hb common
  omega

/-- The only two possible image orders before the R₁ argument excludes four. -/
theorem backward_index_two_or_four [Finite M] {source : LocalSource L R}
    (common : CommonFacts R source geometry) :
    (Q R a).relIndex (V R s.delta) = 2 ∨ (Q R a).relIndex (V R s.delta) = 4 := by
  let := s.radius_elementary hb
  let := s.backward_image_elementary hb
  have hsmall := quotientImage_card_le_four source a p.start_color (V R s.delta)
    (s.radius_le_start_stabilizer hb)
  have hdiv := (IsElementaryAbelian.isPGroup 2 (quotientImage a (V R s.delta))).card_eq_or_dvd
  rw [s.backward_image_card hb] at hsmall hdiv
  have hpos := s.one_lt_backward_index hb common
  omega

end Configuration
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction
