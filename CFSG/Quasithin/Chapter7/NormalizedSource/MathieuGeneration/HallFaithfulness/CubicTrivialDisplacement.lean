module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.CoreDisplacement
public import Theory.GroupAction.ElementaryNineLargeFixed
public import Theory.GroupTheory.CComponent.ThreeCore

/-!
# A large cubic fixed subgroup forces trivial Mathieu displacement

The original intersection residual has cubic rank at least two: otherwise
its cyclic Sylow subgroup would give cubic rank at most one in the actual
Mathieu central quotient. Coprime fixed-point generation on an elementary
nine-subgroup selects a cubic whose fixed subgroup in V has more than two
elements. This uses only the already proved size of the original module.

Cubic fusion in the full J₄ cover moves the previously resolved cubic to
this new cyclic subgroup. Conjugation transports the full residual, its
ordinary-component normality, and its commutator centralization, retaining
the original ambient inclusions and covering kernel. The small fixed-space
bound therefore excludes nonzero displacement: the defined displacement
domain lies in the original core and its commutator image is trivial.

The literal Hall application retains its complete witnesses and supplies
these conclusions. Finishing pushing up still requires the source local-join
factorization and a suitable involution giving the full relative-normalizer
domain. The separate M₂₄ fixed-line and odd-actor comparisons also remain.
Source: Aschbacher--Smith 4.2.13, printed p.612, and 4.4.14, pp.624--625.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- The actual intersection residual contains a cubic with more than two fixed points on V. -/
theorem sourceOrbit_pushingUp_large_fixed_cubic
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : V = D.sourceOrbit) (hm : HasMathieuCentralQuotient D.orbitComponent)
    {A J H W : Subgroup G} (hw : Witness L V A J H W) :
    ∃ x ∈ (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype,
      orderOf x = 3 ∧ 2 < Nat.card (V ⊓ centralizer ({x} : Set G) : Subgroup G) := by
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  obtain ⟨e,_⟩ := hw.2.2.2.2.2.2.2.2.2.2.2.1
  let z := (centerQuotientCongr e).trans (D.orbitCentralQuotientEquiv h)
  let q := z.toMonoidHom.comp ((QuotientGroup.mk' (center (F ⧸ pCore 2 F))).comp
    (QuotientGroup.mk' (pCore 2 F)))
  have hq : Function.Surjective q := z.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  have hr : 2 ≤ primeRank 3 F := by
    by_contra hn
    let P : Sylow 3 F := default
    have hh := P.primeRank_le_one_of_surjective
      (P.isCyclic_of_odd_of_primeRank_le_one (by decide) (by omega)) q hq
    have := mathieu_centralQuotient_threeRank hm
    omega
  obtain ⟨E,hE,hcard⟩ := exists_elementary_nine_of_three_rank hr
  let := hE
  let Eg := E.map F.subtype
  let : IsElementaryAbelian 3 Eg := IsElementaryAbelian.map_subtype
  have hEg : Nat.card Eg = 9 := (card_map_of_injective F.subtype_injective).trans hcard
  have hEF : Eg ≤ F := map_subtype_le _
  have hEV : Eg ≤ normalizer (V : Set G) :=
    hEF.trans ((map_subtype_le _).trans (inf_le_left.trans D.normalizes))
  let := D.elementary
  obtain ⟨x,hx,ho,hbig⟩ := exists_cubic_large_centralizer_of_elementary_nine Eg V hEg hEV
    (IsElementaryAbelian.isPGroup 2 V) (lt_trans (by decide) (D.sourceOrbit_mathieu_card_gt_eight hV hm))
  exact ⟨x,hEF hx,ho,hbig⟩

/-- Move a prescribed cubic cyclic subgroup to such a cubic in the original residual, inside the same full cover. -/
theorem sourceOrbit_pushingUp_cubic_large_fixed_conjugate
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : V = D.sourceOrbit) (hm : HasMathieuCentralQuotient D.orbitComponent)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) [K.Normal]
    (hFK : ((solvableResidual (L ⊓ H : Subgroup G)).map
      (L ⊓ H).subtype).subgroupOf H ≤ K)
    (e : (K ⧸ center K) ≃* Janko4.Model) (x : K) (hx : orderOf x = 3) :
    ∃ g : K, ((g*x*g⁻¹ : K) : H) ∈
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype).subgroupOf H ∧
      2 < Nat.card (V ⊓ centralizer ({(((g*x*g⁻¹ : K) : H) : G)} : Set G) : Subgroup G) := by
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  have hFH : F ≤ H := (map_subtype_le _).trans inf_le_right
  obtain ⟨z,hz,hz3,hbig⟩ := D.sourceOrbit_pushingUp_large_fixed_cubic h hV hm hw
  let zK : K := ⟨⟨z,hFH hz⟩,hFK hz⟩
  have hzK : orderOf zK = 3 := (orderOf_coe zK).symm.trans
    ((orderOf_coe (zK : H)).symm.trans hz3)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hk : q.ker = center K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  obtain ⟨g,hg⟩ := Janko4.LocalStructure.cubic_cyclic_fusion q
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
    (hk.symm ▸ pushingUp_component_center_three_coprime hw K) x zK hx hzK
  have hy : g*x*g⁻¹ ∈ zpowers zK := hg ▸ mem_map_of_mem (MulAut.conj g).toMonoidHom (mem_zpowers x)
  have hyF : ((g*x*g⁻¹ : K) : H) ∈ F.subgroupOf H := by
    let f := H.subtype.comp K.subtype
    have hzF : zpowers zK ≤ F.comap f := zpowers_le.mpr hz
    exact hzF hy
  have hcent : centralizer ({(((g*x*g⁻¹ : K) : H) : G)} : Set G) = centralizer ({z} : Set G) := by
    have hh := congrArg (map (H.subtype.comp K.subtype)) hg
    rw [MonoidHom.map_zpowers] at hh
    rw [MonoidHom.map_zpowers,MonoidHom.map_zpowers] at hh
    change zpowers (((g*x*g⁻¹ : K) : H) : G) = zpowers z at hh
    rw [←centralizer_closure,←zpowers_eq_closure,hh,zpowers_eq_closure,centralizer_closure]
  exact ⟨g,hyF,by rwa [hcent]⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
private theorem centralizer_singleton_map_equiv {U : Type*} [Group U]
    (a : U ≃* U) (x : U) :
    (centralizer ({x} : Set U)).map a.toMonoidHom = centralizer ({a x} : Set U) := by
  rw [←centralizer_closure,←zpowers_eq_closure,map_centralizer_equiv]
  change centralizer ((zpowers x).map a.toMonoidHom : Set U) = _
  rw [MonoidHom.map_zpowers,zpowers_eq_closure,centralizer_closure]
  rfl

/-- Conjugation transports the full residual through the unchanged ambient inclusion. -/
theorem cubicResidualImage_conjugate {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (K : Subgroup H) (x g : K) :
    (cubicResidualImage H K x).map (MulAut.conj ((g : H) : G)).toMonoidHom =
      cubicResidualImage H K (g*x*g⁻¹) := by
  let a := MulAut.conj g
  let C := centralizer ({x} : Set K)
  let D := centralizer ({g*x*g⁻¹} : Set K)
  have hC : C.map a.toMonoidHom = D := centralizer_singleton_map_equiv a x
  let c : C ≃* D := (a.subgroupMap C).trans (MulEquiv.subgroupCongr hC)
  have hR : (solvableResidual D).map D.subtype =
      ((solvableResidual C).map C.subtype).map a.toMonoidHom := by
    rw [←map_solvableResidual_eq c.toMonoidHom c.surjective,map_map,map_map]
    rfl
  change (((solvableResidual C).map C.subtype).map (H.subtype.comp K.subtype)).map
    (MulAut.conj ((g : H) : G)).toMonoidHom =
    ((solvableResidual D).map D.subtype).map (H.subtype.comp K.subtype)
  rw [hR]
  simp only [map_map]
  rfl

/-- The full ordinary-component resolution survives conjugation within the original cover centralizing r. -/
theorem cubic_full_resolution_conjugate {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (K : Subgroup H) (x g : K) (r : G)
    (hfull : CubicPumpupFullResolution H K x r)
    (hKr : K.map H.subtype ≤ centralizer ({r} : Set G)) :
    CubicPumpupFullResolution H K (g*x*g⁻¹) r := by
  let a := MulAut.conj ((g : H) : G)
  let C := centralizer ({((x : H) : G)} : Set G)
  let D := centralizer ({(((g*x*g⁻¹ : K) : H) : G)} : Set G)
  let S := cubicResidualImage H K x
  let U := cubicResidualImage H K (g*x*g⁻¹)
  have hC : C.map a.toMonoidHom = D := centralizer_singleton_map_equiv a _
  have hS : S.map a.toMonoidHom = U := cubicResidualImage_conjugate H K x g
  have hcomp : IsComponentIn U D := by
    have hh := hfull.2.1.map a
    rwa [hC,hS] at hh
  have hn : D ≤ normalizer (U : Set G) := by
    have hh := map_mono (f := a.toMonoidHom)
      ((normal_subgroupOf_iff_le_normalizer hfull.2.1.1).mp hfull.2.2.1)
    rw [hC,map_normalizer_eq_of_bijective _ a.bijective,hS] at hh
    exact hh
  let hnU := normal_subgroupOf_of_le_normalizer hn
  have har : a r = r := by
    apply mul_inv_eq_iff_eq_mul.mpr
    exact (mem_centralizer_singleton_iff.mp
      (hKr (mem_map_of_mem H.subtype g.property)))
  have hZ : (zpowers r).map a.toMonoidHom = zpowers r := by
    rw [MonoidHom.map_zpowers]
    change zpowers (a r) = _
    rw [har]
  have hcomm : ⁅zpowers r,D⁆ ≤ centralizer (U : Set G) := by
    have hh := map_mono (f := a.toMonoidHom) hfull.2.2.2
    rw [map_commutator,hZ,hC,map_centralizer_equiv] at hh
    change ⁅zpowers r,D⁆ ≤ centralizer (S.map a.toMonoidHom : Set G) at hh
    rwa [hS] at hh
  refine ⟨?_,hcomp,hnU,hcomm⟩
  apply le_antisymm (le_componentOrbit _ _)
  change (⨆ a : oddELayer D, (U.subgroupOf D).map (MulAut.conj (a : D)).toMonoidHom) ≤ _
  refine iSup_le fun a => ?_
  exact (mem_normalizer_iff_map_conj_eq.mp
    (show (a : D) ∈ normalizer (U.subgroupOf D : Set D) from by
      rw [normalizer_eq_top]; trivial)).le
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- A large cubic fixed subgroup excludes the nontrivial displacement alternative on the actual source Sylow. -/
theorem sourceOrbit_pushingUp_displacement_le_core
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : V = D.sourceOrbit) (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hfix : V ⊓ centralizer (L : Set G) = ⊥)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) [K.Normal]
    (hFK : ((solvableResidual (L ⊓ H : Subgroup G)).map
      (L ⊓ H).subtype).subgroupOf H ≤ K)
    (e : (K ⧸ center K) ≃* Janko4.Model)
    (r : G) (hrR : r ∈ J.pCoreIn 2)
    (hKr : K.map H.subtype ≤ centralizer ({r} : Set G))
    (x : K) (hx : orderOf x = 3) (hfull : CubicPumpupFullResolution H K x r)
    (P : Sylow 2 (sectionCentralizerIn (normalizer (L : Set G)) L))
    (hRP : J.pCoreIn 2 ≤ (P : Subgroup _).map
      (sectionCentralizerIn (normalizer (L : Set G)) L).subtype)
    (hcent : (P : Subgroup _).map (sectionCentralizerIn (normalizer (L : Set G)) L).subtype ⊓
      centralizer ({r} : Set G) = J.pCoreIn 2) :
    pushingDisplacementDomain ((P : Subgroup _).map
      (sectionCentralizerIn (normalizer (L : Set G)) L).subtype) (J.pCoreIn 2) V r ≤ J.pCoreIn 2 := by
  obtain ⟨g,hg,hbig⟩ := D.sourceOrbit_pushingUp_cubic_large_fixed_conjugate h hV hm hw K hFK e x hx
  let y := g*x*g⁻¹
  have hy : orderOf y = 3 := ((MulAut.conj g).orderOf_eq x).trans hx
  have hfullY := cubic_full_resolution_conjugate H K x g r hfull hKr
  have hM := h.sylow_normalized_maximal_unique D.sylow_normalizes_component
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have hjoin : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)) :=
    ⟨hM.1,sup_le L.le_normalizer D.sylow_normalizes_component,hM.2⟩
  have hyp := source_hypothesis411 h hjoin
  let Pg := (P : Subgroup _).map (sectionCentralizerIn (normalizer (L : Set G)) L).subtype
  have hFP : (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype ≤
      normalizer (Pg : Set G) := ((map_subtype_le _).trans inf_le_left).trans
    (Chapter4.Section02.Unitary.sectionSylow_normalized
      hyp.plus_le hyp.plus_normal hyp.plus_perfect P)
  obtain ⟨_,_,_,_,hc⟩ := D.sourceOrbit_cubic_displacement hfix hw K hFK r hrR hKr
    y hy hg hfullY Pg (P.isPGroup'.map _) hRP hFP
  have hsmall := D.sourceOrbit_cubic_fixed_card_le_two hfix hw K hFK e y hy
  have hc' := hc.resolve_right (fun hh => (not_le_of_gt hbig) (hsmall hh))
  exact (le_inf ((commutatorPreimage_le _ _ _).trans (inf_le_left.trans inf_le_left)) hc').trans hcent.le
end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter4
/-- The large fixed cubic and zero displacement, on the same full covering component and original core. -/
@[expose] def CubicTrivialDisplacementConclusion {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (L V J H : Subgroup G) (K : Subgroup H) (x : K) (r : G) : Prop :=
  CubicCoreDisplacementConclusion T L V J H K x r ∧
    (∃ g : K, ((g*x*g⁻¹ : K) : H) ∈
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype).subgroupOf H ∧
      2 < Nat.card (V ⊓ centralizer ({(((g*x*g⁻¹ : K) : H) : G)} : Set G) : Subgroup G) ∧
      CubicPumpupFullResolution H K (g*x*g⁻¹) r) ∧
    ∀ P : Sylow 2 (sectionCentralizerIn (normalizer (L : Set G)) L),
      let Pg := (P : Subgroup _).map (sectionCentralizerIn (normalizer (L : Set G)) L).subtype
      J.pCoreIn 2 ≤ Pg → Pg ⊓ centralizer ({r} : Set G) = J.pCoreIn 2 →
      let Q := pushingDisplacementDomain Pg (J.pCoreIn 2) V r
      Q ≤ J.pCoreIn 2 ∧ ⁅zpowers r,Q⁆ = ⊥ ∧
        ((T : Subgroup G) ≤ L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 →
          Q ≠ Pg ⊓ normalizer (J.pCoreIn 2 : Set G))
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- Keep the original kernel data and prove that every corresponding displacement image is trivial. -/
theorem sourceOrbit_pushingUp_trivial_displacement
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : V = D.sourceOrbit) (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hfix : V ⊓ centralizer (L : Set G) = ⊥)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) [K.Normal]
    (hFK : ((solvableResidual (L ⊓ H : Subgroup G)).map
      (L ⊓ H).subtype).subgroupOf H ≤ K)
    (e : (K ⧸ center K) ≃* Janko4.Model)
    (r : G) (hrR : r ∈ J.pCoreIn 2)
    (hKr : K.map H.subtype ≤ centralizer ({r} : Set G))
    (x : K) (hx : orderOf x = 3) (hfull : CubicPumpupFullResolution H K x r)
    (hd : CubicCoreDisplacementConclusion T L V J H K x r) :
    CubicTrivialDisplacementConclusion T L V J H K x r := by
  refine ⟨hd,?_,?_⟩
  · obtain ⟨g,hg,hbig⟩ := D.sourceOrbit_pushingUp_cubic_large_fixed_conjugate h hV hm hw K hFK e x hx
    exact ⟨g,hg,hbig,cubic_full_resolution_conjugate H K x g r hfull hKr⟩
  · intro P Pg hRP hc
    let Q := pushingDisplacementDomain Pg (J.pCoreIn 2) V r
    have hQR := D.sourceOrbit_pushingUp_displacement_le_core h hV hm hfix hw K hFK e r hrR hKr
      x hx hfull P hRP hc
    have hQc : Q ≤ centralizer ({r} : Set G) := hQR.trans (hc.ge.trans inf_le_right)
    have hz : ⁅zpowers r,Q⁆ = ⊥ := by
      rw [commutator_comm,commutator_eq_bot_iff_le_centralizer,zpowers_eq_closure,centralizer_closure]
      exact hQc
    refine ⟨hQR,hz,?_⟩
    intro hjoin hdom
    have hlt := D.sourceOrbit_pushingUp_core_lt_of_localJoin h hw hjoin P hRP
    have hh := cubic_core_displacement_full_domain (x := ((x : H) : G)) (P.isPGroup'.map _) hlt hc hdom
      (Or.inl hz) (Or.inl hQR)
    exact D.ne_bot (hh.1.symm.trans hz)
end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open Sporadic.Mathieu Janko4.InvolutionCentralizers
/-- The original full source configuration with a genuinely large cubic fixed subgroup
and vanishing displacement on every containing Sylow with the original kernel. -/
@[expose] def MathieuPushingUpTrivialDisplacementCase {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (L V A : Subgroup G) : Prop :=
  ∃ J H W : Subgroup G, Witness L V A J H W ∧
    ((T : Subgroup G) ≤ L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 →
      ∀ P : Sylow 2 (sectionCentralizerIn (normalizer (L : Set G)) L),
        J.pCoreIn 2 ≤ (P : Subgroup _).map
          (sectionCentralizerIn (normalizer (L : Set G)) L).subtype →
        J.pCoreIn 2 < (P : Subgroup _).map
          (sectionCentralizerIn (normalizer (L : Set G)) L).subtype) ∧
    ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ (normalizer (L : Set G)).subgroupOf H ∧
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
      ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧
      F.subgroupOf H ≤ K ∧ W.subgroupOf H ≤ K ∧
      H = K.map H.subtype ⊔ (H ⊓ centralizer (K.map H.subtype : Set G)) ∧
      ∃ (r : H.pCoreIn 2) (H₁ : Subgroup G), orderOf r = 2 ∧
        centralizer ({(r : G)} : Set G) ≤ H₁ ∧
        IsComponentIn (K.map H.subtype) H₁ ∧
        ((K.map H.subtype).subgroupOf H₁).Normal ∧
        IsComponentIn (K.map H.subtype) (centralizer ({(r : G)} : Set G)) ∧
      ∃ e : (K ⧸ center K) ≃* Janko4.Model,
        let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
        let R := First.centralizer.comap q
        ∃ x : R, orderOf x = 3 ∧ orderOf (q (x : K)) = 3 ∧
          (⟨x,mem_centralizer_singleton_iff.mpr rfl⟩ : Subgroup.centralizer ({x} : Set R)) ∈
            solvableResidual (Subgroup.centralizer ({x} : Set R)) ∧
          solvableResidual (Subgroup.centralizer ({(x : K)} : Set K)) =
            (solvableResidual (Subgroup.centralizer ({x} : Set R))).map
              (R.subtype.elementCentralizerMap x) ∧
          IsQuasisimple (solvableResidual (Subgroup.centralizer ({(x : K)} : Set K))) ∧
          Nonempty (((solvableResidual (Subgroup.centralizer ({(x : K)} : Set K))) ⧸
            center (solvableResidual (Subgroup.centralizer ({(x : K)} : Set K)))) ≃* M22) ∧
          (∃ g : K, ((g * (x : K) * g⁻¹ : K) : H) ∈ F.subgroupOf H ∧
            let y := g * (x : K) * g⁻¹
            IsQuasisimple (solvableResidual (centralizer ({y} : Set K))) ∧
              Nonempty ((solvableResidual (centralizer ({y} : Set K)) ⧸
                center (solvableResidual (centralizer ({y} : Set K)))) ≃* M22) ∧
              CubicAmbientData H K y ∧
              (let C := centralizer ({((y : H) : G)} : Set G) ⊓ centralizer ({(r : G)} : Set G)
               IsComponentIn (cubicResidualImage H K y) C ∧
                 ((cubicResidualImage H K y).subgroupOf C).Normal) ∧
              CubicPumpupData H K y (r : G) ∧
              CubicPumpupQuotientAction H K y (r : G) ∧
              CubicPumpupFullResolution H K y (r : G) ∧
              CubicTrivialDisplacementConclusion T L V J H K y (r : G) ∧
              ∀ Q : Subgroup (centralizer ({y} : Set K)), Q.IsCComponent →
                Q = solvableResidual (centralizer ({y} : Set K))) ∧
          ∀ Q : Subgroup (Subgroup.centralizer ({(x : K)} : Set K)), Q.IsCComponent →
            Q = solvableResidual (Subgroup.centralizer ({(x : K)} : Set K))


end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- Reselect the cubic within the same full covering component to exclude the small
fixed-space alternative. The original involution and quotient maps are retained. -/
theorem pushingUp_trivial_displacement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {A : Subgroup G} (hc : MathieuPushingUpCoreDisplacementCase T L V A) :
    MathieuPushingUpTrivialDisplacementCase T L V A := by
  obtain ⟨J,H,W,hw,hstrict,hesc,K,hK,hn,hout,hFK,hWK,hprod,r,H₁,hr,hCH,hrel,hn₁,hKr,
    e,x,hx,hqx,hmem,he,hquasi,heq,⟨g,hg,hqy,hey,hdata,hs,hp,hact,hfull,hdisp,huy⟩,hux⟩ := hc
  let y := g * (x : K) * g⁻¹
  have hy : orderOf y = 3 :=
    ((MulAut.conj g).orderOf_eq (x : K)).trans ((orderOf_coe x).trans hx)
  let := hn
  have hnew := D.sourceOrbit_pushingUp_trivial_displacement h.toHypothesis1221 hV hm
    (D.sourceOrbit_fixed_and_thompson_of_many h hmany hnon).1 hw K hFK e (r : G)
    (hw.2.2.2.2.2.2.1.ambient_core_le_radical r.property) hKr.1 y hy hfull hdisp
  exact ⟨J,H,W,hw,hstrict,hesc,K,hK,hn,hout,hFK,hWK,hprod,r,H₁,hr,hCH,hrel,hn₁,hKr,
    e,x,hx,hqx,hmem,he,hquasi,heq,⟨g,hg,hqy,hey,hdata,hs,hp,hact,hfull,hnew,huy⟩,hux⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
open Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
universe u
variable {G : Type u} [instG : Group G] [finG : Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The literal Hall obstruction excludes every nonzero displacement on the selected domain.
The full cover, original quotient maps and all Hall hypotheses are retained. -/
theorem sourceOrbit_mathieu_hall_trivial_displacement_obstruction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G))) (hlarge : 1 < ChapterE.generationParameter H)
    (B : Subgroup H) (hBN : B ≤ (normalizer (L : Set G)).subgroupOf H)
    (hHall : IsHallSubgroup oddPrimes
      (B.subgroupOf ((normalizer (L : Set G)).subgroupOf H)))
    (hker : B.map H.subtype ⊓ sectionCentralizer L ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧ A ≤ H ∧ A ≤ sectionCentralizer L ∧
      A ≤ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      (let X := conjugateSpanBy A (T : Subgroup G)
       IsPPerfect 2 X ∧ X.pCoreIn 2 ≠ ⊥ ∧
         L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
         normalizer (X : Set G) ≤ normalizer (L : Set G)) ∧
      (∀ Q : Subgroup G, (T : Subgroup G) ≤ normalizer (Q : Set G) →
        A ≤ sectionCentralizer Q → Q ≤ normalizer (L : Set G)) ∧
      (MathieuPushingUpTrivialDisplacementCase T L V A ∨
        (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
          MathieuJankoSeedResidualCase (T : Subgroup G) L V A
            (D.orbitComponent ⧸ center D.orbitComponent))) := by
  have hsource :=
    @sourceOrbit_mathieu_hall_core_displacement_obstruction G instG finG T L V D
      h hmany hV hm hnon H hH hlarge B hBN hHall hker
  refine hsource.imp fun p hp => hp.imp fun A => ?_
  iterate 11 apply And.imp_right
  exact Or.imp (D.pushingUp_trivial_displacement h hmany hV hm hnon) id

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
