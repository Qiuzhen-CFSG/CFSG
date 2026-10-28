module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Inspection.Normality
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.AlternatingCubics
public import Theory.Alternating.Theorem523Reduction
public import Theory.GroupTheory.CoveringKernelCard

/-!
# Alternating exclusions in the original plane inspection

The component J is normal in N_G(A), so quotienting this normalizer by
the embedded O₂(J) gives an actual ordinary component isomorphic to
J/O₂(J). The second cubic survives outside the image of C_G(A), whereas
the proved alternating cases of A.3.18 put every cubic in that component.

The literal C.2.7 comparison identifies the central quotients of J/O₂(J)
and J*. Its possible center of order three is retained in the A₆ and A₇
arguments; the actual triple-cover cubic theorem excludes both. For A₈,
Schur's order-two universal kernel first rules out a central three-cover.
Consequently the original star catalogue retains only A₅ among its
alternating rows and has no triple-six row. The remaining Lie-family
inspection, field reductions and chief-factor argument are not asserted here.

Source: Aschbacher--Smith 13.3.12, printed pp.889--890, using A.3.18,
pp.51--53, and C.2.7, pp.145--147; GLS3, Theorem 5.2.3 for A₈.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open ChapterE Atlas.G2.Natural.BinaryNondegeneratePlane
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  [IsElementaryAbelian 2 V]

/-- An outside plane cubic contradicts cubic capture in the literal component quotient. -/
theorem Context.no_cubic_capture (s : Context T L V) (d : MarkedPlane V)
    (J : Subgroup G) (j : LocalData T L d J)
    (capture : ∀ (B : Type u) [Group B] [Finite B], IsSQTK KnownSimple.IsKnownSimple B →
      ∀ (D : Subgroup B), IsComponent B D → (J ⧸ pCore 2 J) ≃* D →
      ∀ x : B, orderOf x = 3 → x ∈ D) : False := by
  let N := normalizer (d.A : Set G)
  let H := centralizer (d.A : Set G)
  let D := J.subgroupOf N
  have hJN : J ≤ N := j.input.component.1.trans (Subgroup.centralizer_le_normalizer _)
  let : D.Normal := normal_subgroupOf_of_le_normalizer (s.local_component_normalizer d J j)
  let R := D.pCoreIn 2
  have hRnormal : R.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    have hn := normalizer_le_normalizer_characteristic_image D (pCore 2 D)
    rw [normalizer_eq_top (H := D)] at hn
    exact hn
  let := hRnormal
  let B := N ⧸ R
  let q := QuotientGroup.mk' R
  let Dbar := D.map q
  let f := q.subgroupMap D
  have hk : f.ker = pCore 2 D := by
    rw [ker_subgroupMap, QuotientGroup.ker_mk']
    exact comap_map_eq_self_of_injective D.subtype_injective (pCore 2 D)
  let e : (D ⧸ pCore 2 D) ≃* Dbar :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f (q.subgroupMap_surjective D))
  let eJ := subgroupOfEquivOfLe hJN
  let eQ : (J ⧸ pCore 2 J) ≃* Dbar :=
    (QuotientGroup.congr _ _ eJ (pCore_map_iso 2 eJ)).symm.trans e
  let := j.input.quasisimple
  let : IsQuasisimple Dbar := IsQuasisimple.of_mulEquiv eQ
  have hDbar : IsComponent B Dbar :=
    ⟨(inferInstance : D.Normal).isSubnormal.map (QuotientGroup.mk'_surjective R), inferInstance⟩
  have hNsq : IsSQTK KnownSimple.IsKnownSimple N :=
    s.hypothesis.qtke.twoLocal_sqtk
      ⟨d.A,d.ne_bot,IsPGroup.of_card (n := 2) d.card,rfl⟩
  have hBsq : IsSQTK KnownSimple.IsKnownSimple B := by
    refine ⟨?_,hNsq.isKGroup.quotient R⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho R (isPGroup_pCoreIn 2 D)).trans
      (hNsq.stronglyQuasithin p hp ho)
  obtain ⟨x,hx,_,hout⟩ := s.plane_cubic_escape d
  have hxbar : orderOf (q x) = 3 := by
    rw [q.orderOf_map_eq_of_coprime_of_isPGroup_ker
      (show IsPGroup 2 q.ker from (QuotientGroup.ker_mk' R).symm ▸ isPGroup_pCoreIn 2 D)
      x (by rw [hx]; decide),hx]
  obtain ⟨y,hy,he⟩ := capture B hBsq Dbar hDbar eQ (q x) hxbar
  have hxy : x * y⁻¹ ∈ R := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (x * y⁻¹) = 1
    rw [map_mul,map_inv,he,mul_inv_cancel]
  have hxyH : ((x * y⁻¹ : N) : G) ∈ H := j.input.component.1 (pCoreIn_le 2 D hxy)
  have hyH : (y : G) ∈ H := j.input.component.1 hy
  apply hout
  simpa only [Subgroup.coe_mul,Subgroup.coe_inv,mul_assoc,inv_mul_cancel,mul_one] using H.mul_mem hxyH hyH

/-- An actual alternating quotient of degree at least six cannot occur in the original plane component. -/
theorem Context.not_alternating_core (s : Context T L V) (d : MarkedPlane V)
    (J : Subgroup G) (j : LocalData T L d J) {n : ℕ} (hn : 6 ≤ n)
    (e : (J ⧸ pCore 2 J) ≃* alternatingGroup (Fin n)) : False := by
  apply s.no_cubic_capture d J j
  intro B _ _ hB D hD eD x hx
  exact ChapterA.Section03.OddPrime.SourceModels.AlternatingCubics.cubic_mem_of_alternating_component
    hD hn ⟨eD.symm.trans e⟩ (hB.stronglyQuasithin 3 (by decide) (by decide)) hx

/-- The two exceptional triple alternating quotients are excluded with their cubic centers retained. -/
theorem Context.not_alternating_cover_core (s : Context T L V) (d : MarkedPlane V)
    (J : Subgroup G) (j : LocalData T L d J)
    (hm : Chapter1.Section02.LocalModels.IsAlternatingCover (J ⧸ pCore 2 J) 6 ∨
      Chapter1.Section02.LocalModels.IsAlternatingCover (J ⧸ pCore 2 J) 7) : False := by
  apply s.no_cubic_capture d J j
  intro B _ _ hB D hD eD x hx
  exact ChapterA.Section03.OddPrime.SourceModels.AlternatingCubics.cubic_mem_of_alternating_cover_component
    hD eD.symm hm (hB.stronglyQuasithin 3 (by decide) (by decide)) hx

/-- The central quotient alternatives A₆ and A₇ are excluded even when the
original two-core quotient has its allowed central three-cover. -/
theorem Context.not_alternating_central_quotient (s : Context T L V) (d : MarkedPlane V)
    (J : Subgroup G) (j : LocalData T L d J) {n : ℕ} (hn : n = 6 ∨ n = 7)
    (e : ((J ⧸ pCore 2 J) ⧸ center (J ⧸ pCore 2 J)) ≃*
      alternatingGroup (Fin n)) : False := by
  let := j.input.quasisimple
  rcases ChapterC.C27Source.coreQuotient_center_card_from_source j.input with hc | hc
  · have hz : center (J ⧸ pCore 2 J) = ⊥ := (eq_bot_iff_card _).mpr hc
    let eq : (J ⧸ pCore 2 J) ≃* alternatingGroup (Fin n) :=
      QuotientGroup.quotientBot.symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hz.symm).trans e)
    exact s.not_alternating_core d J j (by omega) eq
  · have hm : Chapter1.Section02.LocalModels.IsAlternatingCover (J ⧸ pCore 2 J) n :=
      ⟨inferInstance,⟨mulEquivOfPrimeCardEq hc (by simp)⟩,⟨e⟩⟩
    apply s.not_alternating_cover_core d J j
    rcases hn with rfl | rfl
    · exact Or.inl hm
    · exact Or.inr hm

/-- The actual star-image central quotient comparison excludes the same
alternating alternatives in C.2.7, without identifying star and core quotients. -/
theorem Context.not_alternating_star_central_quotient
    (s : Context T L V) (d : MarkedPlane V) (J : Subgroup G)
    (j : LocalData T L d J) {n : ℕ} (hn : n = 6 ∨ n = 7)
    (e : (Chapter1.RadicalExclusions.ModelReduction.starImage
        J ((L ⊔ T).pCoreIn 2) J ⧸
      center (Chapter1.RadicalExclusions.ModelReduction.starImage J ((L ⊔ T).pCoreIn 2) J)) ≃*
        alternatingGroup (Fin n)) : False := by
  apply s.not_alternating_central_quotient d J j hn
  exact (Chapter1.RadicalExclusions.ModelReduction.coreStarCenterEquiv j.input.normalizes
    j.input.quasisimple
    (Chapter1.RadicalExclusions.ModelReduction.FullSieve.starImage_ne_bot_of_bound
      j.input.normalizes j.input.quasisimple
      (ChapterC.C27Source.kernel_offender_from_source j.input).1.upper)).trans e


private noncomputable def quotientCenterCongr {B C : Type*} [Group B] [Group C]
    (e : B ≃* C) : (B ⧸ center B) ≃* (C ⧸ center C) := by
  apply QuotientGroup.congr _ _ e
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact (centerCongr e ⟨y,hy⟩).property
  · intro hx
    exact ⟨e.symm x,(centerCongr e.symm ⟨x,hx⟩).property,e.apply_symm_apply x⟩

/-- The literal A₆ and A₇ star rows of the proved B.5/C.2.7 group catalogue
are impossible in this plane normalizer. -/
theorem Context.not_alternating_star (s : Context T L V) (d : MarkedPlane V)
    (J : Subgroup G) (j : LocalData T L d J) {n : ℕ} (hn : n = 6 ∨ n = 7)
    (e : Chapter1.RadicalExclusions.ModelReduction.starImage
      J ((L ⊔ T).pCoreIn 2) J ≃* alternatingGroup (Fin n)) : False := by
  apply s.not_alternating_star_central_quotient d J j hn
  exact (quotientCenterCongr e).trans
    ((QuotientGroup.quotientMulEquivOfEq (alternatingGroup.center_eq_bot (by simp; omega))).trans
      QuotientGroup.quotientBot)

/-- The triple-six star row is excluded through its actual central quotient;
its central cubic is never discarded. -/
theorem Context.not_tripleSix_star (s : Context T L V) (d : MarkedPlane V)
    (J : Subgroup G) (j : LocalData T L d J)
    (e : (Chapter1.RadicalExclusions.ModelReduction.starImage
        J ((L ⊔ T).pCoreIn 2) J ⧸
      center (Chapter1.RadicalExclusions.ModelReduction.starImage J ((L ⊔ T).pCoreIn 2) J)) ≃*
        alternatingGroup (Fin 6)) : False :=
  s.not_alternating_star_central_quotient d J j (Or.inl rfl) e

/-- The A₈ central quotient has no residual central cubic: its universal
Schur cover has kernel of order two. -/
theorem Context.not_alternatingEight_central_quotient
    (s : Context T L V) (d : MarkedPlane V) (J : Subgroup G)
    (j : LocalData T L d J)
    (e : ((J ⧸ pCore 2 J) ⧸ center (J ⧸ pCore 2 J)) ≃*
      alternatingGroup (Fin 8)) : False := by
  let := j.input.quasisimple
  let c : Covering (J ⧸ pCore 2 J) (alternatingGroup (Fin 8)) := {
    toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (center (J ⧸ pCore 2 J)))
    surjective := e.surjective.comp (QuotientGroup.mk'_surjective _) }
  have hk : c.toMonoidHom.ker = center (J ⧸ pCore 2 J) := by
    change (e.toMonoidHom.comp (QuotientGroup.mk' _)).ker = _
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let a := GLS3.Chapter5.SchurPresentation.schurAlternatingCovering 3
  have ha := GLS3.Chapter5.SchurPresentation.theorem_5_2_3_b_universality
    3 (by decide) (by decide)
  have hd := kernel_card_dvd_of_surjective_factor a.toMonoidHom c.toMonoidHom
    (ha.lift c).toMonoidHom (ha.lift c).surjective
    (congrArg Covering.toMonoidHom (ha.lift_fac c))
  rw [hk,GLS3.Chapter5.SchurPresentation.natCard_ker_schurAlternatingCovering 3] at hd
  have hc : Nat.card (center (J ⧸ pCore 2 J)) = 1 := by
    rcases ChapterC.C27Source.coreQuotient_center_card_from_source j.input with hc | hc
    · exact hc
    · rw [hc] at hd
      norm_num at hd
  have hz : center (J ⧸ pCore 2 J) = ⊥ := (eq_bot_iff_card _).mpr hc
  exact s.not_alternating_core d J j (by decide)
    (QuotientGroup.quotientBot.symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hz.symm).trans e))

/-- Eliminate the actual A₈ star row using the original central comparison. -/
theorem Context.not_alternatingEight_star
    (s : Context T L V) (d : MarkedPlane V) (J : Subgroup G)
    (j : LocalData T L d J)
    (e : Chapter1.RadicalExclusions.ModelReduction.starImage
      J ((L ⊔ T).pCoreIn 2) J ≃* alternatingGroup (Fin 8)) : False := by
  apply s.not_alternatingEight_central_quotient d J j
  exact (Chapter1.RadicalExclusions.ModelReduction.coreStarCenterEquiv j.input.normalizes
    j.input.quasisimple
    (Chapter1.RadicalExclusions.ModelReduction.FullSieve.starImage_ne_bot_of_bound
      j.input.normalizes j.input.quasisimple
      (ChapterC.C27Source.kernel_offender_from_source j.input).1.upper)).trans
    ((quotientCenterCongr e).trans
      ((QuotientGroup.quotientMulEquivOfEq (alternatingGroup.center_eq_bot (by simp))).trans
        QuotientGroup.quotientBot))

open scoped MatrixGroups
open ChapterB.QuasisimpleSource ChapterB.SourceInduction.ProjectiveLine

/-- The actual star-group catalogue after the alternating and triple-six
cubic obstructions. The remaining rows retain their literal group equivalences. -/
inductive InspectedStarModel (B : Type*) [Group B] : Prop
  | linearTwo (F : BinaryField) (equiv : B ≃* SL(2,F.Carrier))
  | linearThree (F : BinaryField) (equiv : B ≃* SL(3,F.Carrier))
  | symplectic (F : BinaryField) (large : 1 < F.degree)
      (equiv : B ≃* Matrix.symplecticGroup (Fin 2) F.Carrier)
  | g2 (F : BinaryField) (large : 1 < F.degree) (equiv : B ≃* Atlas.G2.Model F.Carrier)
  | g2DerivedTwo (equiv : B ≃* commutator (Atlas.G2.Model (ZMod 2)))
  | alternatingFive (equiv : B ≃* alternatingGroup (Fin 5))
  | linearFiveTwo (equiv : B ≃* SL(5,ZMod 2))

/-- Apply all the proved cubic exclusions to the original B.5/C.2.7
catalogue on the actual component-radical star image. -/
theorem Context.inspected_star_model (s : Context T L V) (d : MarkedPlane V)
    (J : Subgroup G) (j : LocalData T L d J) :
    InspectedStarModel (Chapter1.RadicalExclusions.ModelReduction.starImage
      J ((L ⊔ T).pCoreIn 2) J) := by
  cases ChapterC.C27Source.star_model_from_source j.input with
  | linearTwo F e => exact .linearTwo F e
  | linearThree F e => exact .linearThree F e
  | symplectic F hF e => exact .symplectic F hF e
  | g2 F hF e => exact .g2 F hF e
  | g2DerivedTwo e => exact .g2DerivedTwo e
  | linearFiveTwo e => exact .linearFiveTwo e
  | alternating n hn e =>
    rcases hn with rfl | rfl | rfl | rfl
    · exact .alternatingFive e
    · exact (s.not_alternating_star d J j (Or.inl rfl) e).elim
    · exact (s.not_alternating_star d J j (Or.inr rfl) e).elim
    · exact (s.not_alternatingEight_star d J j e).elim
  | tripleSix _ e => exact (s.not_tripleSix_star d J j e).elim

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
