module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.Recognition.Source
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.Overgroups

/-!
# The three-local quotient in the vertex-overgroup calculation

The perfect subgroup C_G(X) has index two in N_G(X), so its relative
copy is the full commutator subgroup. Consequently every comparison of
the literal quotient N_G(X)/X with PGL₂(9) carries C_G(X) onto the
canonical PSL₂(9). This proves the compatibility required by the actual
vertex-overgroup consumer; no choice of projective coordinates is assumed
to preserve that subgroup without proof.

The final application discharges the perfectness, quotient and image
premises of the proper-overgroup calculation from the exact earlier
47.1–47.2 conclusions. The edge-frame application retains its actual
embedded A₅ fixer, supplied by the separate 47.5 construction.

Source: Aschbacher, *Sporadic Groups* (1994), 47.3 and 47.10,
printed pp.261–262 and 266.
-/

public section

open Subgroup Theory.GroupTheory.GraphUniquenessSystem
open Atlas.Comparisons.Exceptional GorensteinWalter
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal
variable {G : Type*} [Group G] [Finite G] {D : Seed G}

namespace CentralizerCalculation

/-- Perfectness and the cyclic quotient identify the intrinsic commutator. -/
theorem normalizer_commutator (H : CentralizerCalculation D) :
    commutator (M D) = CM D := by
  let : Group.IsPerfect (C D) := H.perfect
  let : Group.IsPerfect (CM D) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (C_le_M D)).symm.toMonoidHom)
    (subgroupOfEquivOfLe (C_le_M D)).symm.surjective
  let : IsCyclic (M D ⧸ CM D) := isCyclic_of_prime_card H.centralizer_index
  apply le_antisymm
  · exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  · rw [← (CM D).commutator_eq_self]
    exact Subgroup.commutator_mono le_top le_top

/-- Compatibility with PSL₂ holds for any coordinates on the literal quotient. -/
theorem projective_centralizer_image (H : CentralizerCalculation D)
    (e : (M D ⧸ XM D) ≃* PGL2 Nine.F) :
    (CM D).map (Overgroups.vertexModelMap D e) =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := Nine.F)).range := by
  have hf : Function.Surjective (Overgroups.vertexModelMap D e) :=
    e.surjective.comp (QuotientGroup.mk'_surjective (XM D))
  rw [← H.normalizer_commutator, map_commutator_eq, MonoidHom.range_eq_top.mpr hf]
  exact pgl2_commutator_eq_psl2_range_of_card_gt_three Nine.F
    (by rw [Nine.card]; exact ⟨3, 2, by decide, by decide, by decide, by decide⟩)
    (by rw [Nine.card]; decide)

/-- Apply the projective overgroup theorem through the original quotient map. -/
theorem proper_overgroup_le_centralizer (H : CentralizerCalculation D)
    (F U : Subgroup G) (he : Nonempty (F ≃* alternatingGroup (Fin 5)))
    (hFM : F ≤ M D) (hFU : F ≤ U) (hUM : U ≤ M D) (hU : U ≠ M D) :
    U ≤ C D :=
  Overgroups.proper_overgroup_le_centralizer D H.perfect H.normalizerQuotientEquiv
    (H.projective_centralizer_image H.normalizerQuotientEquiv) F U he hFM hFU hUM hU

end CentralizerCalculation

variable [IsSimpleGroup G]

/-- The three-local source theorem discharges all local-model premises in the
proper-overgroup consumer. The A₅ and overgroup inclusions are literal. -/
theorem EarlierConclusions.proper_overgroup_le_centralizer (E : EarlierConclusions D)
    (F U : Subgroup G) (he : Nonempty (F ≃* alternatingGroup (Fin 5)))
    (hFM : F ≤ M D) (hFU : F ≤ U) (hUM : U ≤ M D) (hU : U ≠ M D) :
    U ≤ C D := by
  obtain ⟨H⟩ := E.centralizerCalculation
  exact H.proper_overgroup_le_centralizer F U he hFM hFU hUM hU

/-- The precise `hovergroups` premise of `SourceLocal.localDataOfCalculations`,
with the three-local premises discharged. The frame and its A₅ fixer come
from the separate source suborbit construction. -/
theorem EarlierConclusions.edgeFrame_proper_overgroups (E : EarlierConclusions D)
    (frame : EdgeFrame D)
    (he : Nonempty (edgeFixer G D.base frame.y ≃* alternatingGroup (Fin 5))) :
    ∀ U : Subgroup G, edgeFixer G D.base frame.y ≤ U →
      U ≤ M D → U ≠ M D → U ≤ C D := by
  obtain ⟨H⟩ := E.centralizerCalculation
  exact Overgroups.edgeFrame_proper_overgroups frame he H.perfect H.normalizerQuotientEquiv
    (H.projective_centralizer_image H.normalizerQuotientEquiv)

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal
