module

public import CFSG.Quasithin.Chapter13.Section07.TranspositionImage
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FiveSeed.BarMarking.Pair
public import Theory.GroupTheory.InvolutionCentralizerControl
public import Theory.Alternating.OddCentralCovers
public import Theory.GroupTheory.PerfectCentralCoverCyclicOddSylow

/-!
# The ordinary and triple-cover alternatives in the actual natural setup

Perfectness of the original L follows from its C-component property. The
marked quotient by O₂,Z(L) is exactly the central quotient of L/O₂(L),
so that quotient is quasisimple. Its center is odd because its two-core is
trivial; the established alternating-cover theorem leaves A₆ or the actual
hexacode triple cover. The quotient coordinate retains the original projection.

The source point-centralizer residual and common Sylow also put the entire
preimage of that center inside H. These conclusions are derived directly
from the original natural setup, without a component-model premise.
Source: Aschbacher–Smith, 13.7.3(8) and13.7.9(2), pp.936,940–941;
the local alternatives are the A₆ specialization of13.3.2.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion
open Section08.TransvectionRecognition.Component.ModelExtension
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

noncomputable def source_central_quotient :
    ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) ≃* alternatingGroup (Fin 6) := by
  let q := QuotientGroup.mk' (pCore 2 L)
  let f := (QuotientGroup.mk' (center (L ⧸ pCore 2 L))).comp q
  have hf : Function.Surjective f := (QuotientGroup.mk'_surjective _).comp
    (QuotientGroup.mk'_surjective _)
  have hk : f.ker = centralCore L := by
    change ((QuotientGroup.mk' (center (L ⧸ pCore 2 L))).comp q).ker = _
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  let e : (L ⧸ centralCore L) ≃* ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  exact e.symm.trans d.local_quotient

theorem source_central_quotient_apply (l : L) :
    source_central_quotient d
      (QuotientGroup.mk' (center (L ⧸ pCore 2 L)) (QuotientGroup.mk' (pCore 2 L) l)) =
        d.local_quotient (QuotientGroup.mk' (centralCore L) l) := by
  unfold source_central_quotient
  change d.local_quotient _ = d.local_quotient _
  congr 1
  apply (Equiv.symm_apply_eq _).mpr
  rfl

theorem source_core_quotient_quasisimple : IsQuasisimple (L ⧸ pCore 2 L) := by
  let : Group.IsPerfect (L.subgroupOf (L ⊔ (T : Subgroup G))) :=
    d.counterexample.local_component.1.1.perfect
  let e : (L.subgroupOf (L ⊔ (T : Subgroup G))) ≃* L := subgroupOfEquivOfLe le_sup_left
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let : Group.IsPerfect (L ⧸ pCore 2 L) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (pCore 2 L))
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  exact { toIsPerfect := inferInstance, simple := (source_central_quotient d).isSimpleGroup }

theorem source_odd_center_alternatives :
    Nat.card (center (L ⧸ pCore 2 L)) = 1 ∨ Nat.card (center (L ⧸ pCore 2 L)) = 3 := by
  let := source_core_quotient_quasisimple d
  have hn : ¬ 2 ∣ Nat.card (center (L ⧸ pCore 2 L)) :=
    PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot
      (pCore_quotient_pCore_eq_bot 2) (center (L ⧸ pCore 2 L)) le_rfl
  have ho : Odd (Nat.card (center (L ⧸ pCore 2 L))) := by
    exact Nat.not_even_iff_odd.mp (fun he => hn (even_iff_two_dvd.mp he))
  rcases GLS3.Chapter5.OddCentralCovers.odd_center_alternatives 6 (by decide)
    (source_central_quotient d) ho with hc | ⟨_,hc⟩
  · exact Or.inl hc
  · exact Or.inr hc

theorem source_core_quotient_alternatives :
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) := by
  let := source_core_quotient_quasisimple d
  rcases source_odd_center_alternatives d with hc | hc
  · exact Or.inl ⟨GLS3.Chapter5.OddCentralCovers.alternatingEquivOfCenterCardOne 6
      (source_central_quotient d) hc⟩
  · exact Or.inr (GLS3.Chapter5.OddCentralCovers.triple_six_equiv_hexacode
      (source_central_quotient d) hc)

/-- The original local point centralizer lies in H by its actual two-residual. -/
theorem local_point_centralizer_le {H : Subgroup G}
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis) :
    L ⊓ centralizer (V₁ : Set G) ≤ H := by
  have he : normalizer (V₁ : Set G) = centralizer (V₁ : Set G) :=
    le_antisymm (normalizer_le_centralizer_of_card_two V₁ d.line_card)
      (Subgroup.centralizer_le_normalizer _)
  have hr := Section08.TransvectionQuotients.FiveSeed.BarMarking.normalizer_residual_eq
    L V₁ (T : Subgroup G) T.isPGroup' d.normalizes_L
  have hn := Section08.TransvectionQuotients.FiveSeed.BarMarking.residual_normalizer_sup_sylow
    (L ⊔ (T : Subgroup G)) V₁ T le_sup_right d.line_stable
  rw [hr, he] at hn
  have hm : (L ⊔ (T : Subgroup G)) ⊓ centralizer (V₁ : Set G) ≤ H :=
    hn.symm.trans_le h.local_le
  exact (inf_le_inf_right _ le_sup_left).trans hm

/-- The entire preimage of the component center is in the original local H. -/
theorem central_core_le_local {H : Subgroup G}
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis) :
    (centralCore L).map L.subtype ≤ H := by
  apply le_trans ?_ (local_point_centralizer_le d h)
  refine le_inf (map_subtype_le _) ?_
  rintro _ ⟨l,hl,rfl⟩
  have he : NaturalAction.permutation d (inclusion le_sup_left l) = 1 := by
    rw [NaturalAction.permutation_L,
      show QuotientGroup.mk' (centralCore L) l = 1 from (QuotientGroup.eq_one_iff l).mpr hl,
      map_one]
    rfl
  exact (centralizer_le (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)))
    ((permutation_eq_one_iff d (inclusion le_sup_left l)).mp he)

end CFSG.Quasithin.Chapter13.Section07
