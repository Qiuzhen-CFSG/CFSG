module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeChiefActions
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodeActorRank
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeParabolicInputs

/-!
# The original sharp actor on M22-code chief factors

Under the temporary containment of the original source orbit in the
two-core, the chosen M22-code marking forces every noncentral chief action
of the original conjugate span to see the same minimum quadratic actor with
rank at least two modulo the two-core.  Its faithful image on each chief
factor is consequently an FF offender with the source rank and
fixed-codimension equalities.  The containment remains an explicit input;
this result does not assert the exceptional parabolic classification.

Source: Aschbacher–Smith, original 3.1.9(2)–(4) and 8.2.2(1), printed
pp.577 and 715 (PDF pp.594 and 732).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource MathieuCode
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open ChapterD ChapterD.UniqueFactor NoncentralChiefRefinement
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

theorem sourceOrbit_m22_code_inside_core_large_chief_actor
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hcore : D.sourceOrbit ≤ H.pCoreIn 2) :
    let U := (conjugateSpan H D.sourceOrbit).subgroupOf H
    ∃ hU : IsElementaryAbelian 2 U,
      let := hU
      ∃ A ∈ elementaryAbelianMaxSubgroups ((T.subtype hH.1.1.2) : Subgroup H),
        ¬ A ≤ pCore 2 H ∧ IsQuadratic (normalRepresentation U) A ∧
        2 ≤ Nat.log 2 ((pCore 2 H).relIndex A) ∧
        (∀ B ∈ elementaryAbelianMaxSubgroups ((T.subtype hH.1.1.2) : Subgroup H),
          ¬ B ≤ pCore 2 H → (pCore 2 H).relIndex A ≤ (pCore 2 H).relIndex B) ∧
        ∀ (s : SeriesOn U) (i : Fin s.series.length), ¬ s.Central i →
          IsOffender (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i))
            (actionSubgroup (s.factorRepresentation i) A) ∧
          rank (actionSubgroup (s.factorRepresentation i) A) =
            fixedCodim (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i))
              (actionSubgroup (s.factorRepresentation i) A) ∧
          rank (actionSubgroup (s.factorRepresentation i) A) =
            Nat.log 2 ((pCore 2 H).relIndex A) := by
  obtain ⟨c,_,hq,hd⟩ := D.sourceOrbit_m22_code_inside_core_inputs h hmany hV hnon d hH hcore
  obtain ⟨hM,hu⟩ := D.original_uniqueness h
  let q := c.toQRCConfiguration (c.no_common_normal hu)
  let := source_elementary_span_of_notFF q hcore (source_notFF_of_ratio_two q hq)
  let U := (conjugateSpan H D.sourceOrbit).subgroupOf H
  let hU : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    ((span_le_right_core q hcore).trans (twoCore_le H))
  let := hU
  let S := T.subtype hH.1.1.2
  have hS : (S : Subgroup H).map H.subtype = T := map_subgroupOf_eq_of_le hH.1.1.2
  have hp := source_intrinsic_minimalParabolic_of_notFF q
    D.sourceOrbit_weakClosure_setup.nontrivial (source_notFF_of_ratio_two q hq) S hS
  obtain ⟨A,hA,hAR,hquad,hmin,heq⟩ := c.sqtk_minimal_actor_equalities
    h.simpleQTKE hM hu (D.sourceOrbit_thompson_centralizes h.toHypothesis1221 hnon)
    D.sourceOrbit_weakClosure_setup.nontrivial hcore hd hq
  let : IsElementaryAbelian 2 A := hA.2.1
  have hnc : ¬ A ≤ centralizer (U : Set H) := by
    intro ha
    exact hAR ((le_inf hA.1 ha).trans
      (source_span_centralizer_sylow_le_core q D.sourceOrbit_weakClosure_setup.nontrivial
        hcore (source_notFF_of_ratio_two q hq) S hS))
  obtain ⟨a,ha,hE,_⟩ := D.sourceOrbit_m22_code_full_automizer h.toHypothesis1221 d
  let j : internalActionImage (L ⊔ (T : Subgroup G)) D.sourceOrbit c.module_normalized →*
      Automizer D.sourceOrbit :=
    inclusion (by rintro _ ⟨x,rfl⟩; exact ⟨inclusion c.module_normalized x,rfl⟩)
  obtain ⟨s⟩ := SeriesOn.exists_series U
  have hr := Chapter8.MathieuShadowRows.code_sharp_actor_rank_lower q hcore (a.comp j)
    (D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv)
    (fun x v => hE (j x) v) A hnc (heq s).2.1 (heq s).2.2.2.1
  refine ⟨hU,A,hA,hAR,hquad,hr,hmin,?_⟩
  intro s i hi
  have hk := MultipleFactors.source_chief_sylow_kernel U S hp s i hi A hA.1
  have hn : ¬ A ≤ (s.factorRepresentation i).ker := by
    intro hn
    apply hAR
    have he : A ⊓ (s.factorRepresentation i).ker = A := inf_eq_left.mpr hn
    rw [he] at hk
    exact hk.le.trans inf_le_right
  have hidx : (s.factorRepresentation i).ker.relIndex A = (pCore 2 H).relIndex A := by
    rw [←inf_relIndex_left,hk,inf_relIndex_left]
  have hrank : rank (actionSubgroup (s.factorRepresentation i) A) =
      Nat.log 2 ((pCore 2 H).relIndex A) := by
    rw [rank_actionSubgroup_eq_log_relIndex,hidx]
  have he : rank (actionSubgroup (s.factorRepresentation i) A) =
      fixedCodim (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i))
        (actionSubgroup (s.factorRepresentation i) A) := by
    rw [hrank,fixedCodim_actionSubgroup]
    exact (heq s).2.2.2.2.1 i hi
  exact ⟨⟨elementary_actionSubgroup _ hn,he.ge⟩,he,hrank⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
