module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ActorPlacement
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.NaturalNormalizer
public import Theory.Representation.BinaryConjugationSection.QuadraticPair
/-!
# Actual critical escape from the five-point natural section

A displacement subgroup of order at most two forces an H actor into O₂(H):
its image on the given natural SL₂(4) quotient would otherwise be a binary
transvection. The core of H fixes its neighborhood, so actual criticality
makes U/(U∩Qα) nontrivial. If Uα were contained in O₂(H), the original
point-commutator identity would bound the reciprocal displacement by a line.
The natural-section detector would then put U in Qα, a contradiction.
All subgroups and conjugators are the original source objects.
Source: Aschbacher–Smith 14.5.18(1,4), 14.5.21(2), and Notation14.7.1,
printed pp.1018–1019,1043, in the actual14.7.63 S₅ case.
-/
public section
open Subgroup Representation
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Data
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
variable (d : Data T L V F W)

include d in
theorem actor_in_core_of_small_commutator
    (A C : Subgroup G) (hcomm : ⁅A,F.U⁆ ≤ C) (hcard : Nat.card C ≤ 2)
    (x : F.H) (hx : (x:G) ∈ A) : (x:G) ∈ F.H.pCoreIn 2 := by
  let : Finite W := Finite.of_surjective
    (fun v : F.U => (d.conjugationSection.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp d.conjugationSection.onto)
  let D := d.conjugationSection.imageSpace C
  have hDcard : Nat.card D ≤ 2 := by
    change Nat.card ((C.subgroupOf F.U).map d.conjugationSection.coordinates) ≤ 2
    have hmap := Nat.card_le_card_of_surjective (d.conjugationSection.coordinates.subgroupMap
      (C.subgroupOf F.U)) (d.conjugationSection.coordinates.subgroupMap_surjective _)
    have hsub : Nat.card (C.subgroupOf F.U) ≤ Nat.card C :=
      Nat.card_le_card_of_injective (fun y => (⟨y.val,y.property⟩ : C))
        (by
          intro a b h
          apply Subtype.ext
          apply Subtype.ext
          exact congrArg (fun z : C => (z:G)) h)
    exact hmap.trans (hsub.trans hcard)
  have hdim : Module.finrank (ZMod 2) D ≤ 1 := by
    rw [Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_zmod] at hDcard
    by_contra hn
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ 2)
      (show 2 ≤ Module.finrank (ZMod 2) D by omega)
    omega
  let δ := d.naturalQuotient.action (d.qH x) - LinearMap.id
  have hδ : LinearMap.range δ ≤ D.map d.projection.toLinearMap := by
    rintro y ⟨v,rfl⟩
    obtain ⟨w,rfl⟩ := d.projection_onto v
    refine ⟨(d.action x - 1) w,
      d.conjugationSection.displacement_range_le_imageSpace_of_commutator_le
        A C hcomm x hx ⟨w,rfl⟩,?_⟩
    change d.projection (d.action x w - w) =
      d.naturalQuotient.action (d.qH x) (d.projection w) - d.projection w
    rw [map_sub]
    exact congrArg (fun y => y-d.projection w)
      (LinearMap.congr_fun (d.projection.isIntertwining' x) w)
  have hr : Module.finrank (ZMod 2) (LinearMap.range δ) ≤ 1 :=
    (Submodule.finrank_mono hδ).trans ((Submodule.finrank_map_le _ _).trans hdim)
  have hn := d.naturalQuotient.no_rank_one (d.qH x)
  have hz : δ=0 := LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp (by
    change Module.finrank (ZMod 2) (LinearMap.range δ) ≠ 1 at hn
    omega))
  have he : d.qH x = 1 := d.naturalQuotient.injective (by
    simpa only [map_one,Module.End.one_eq_id] using (sub_eq_zero.mp hz))
  have hk : x ∈ d.qH.ker := he
  rw [d.qH_ker] at hk
  exact hk
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Data

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Subgroup Chapter12.Section08 Subgroup.CosetGeometry.RankTwo
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

omit [Finite G] in
theorem core_le_H_neighborhood :
    F.H.pCoreIn 2 ≤ (ballKernel (geometryFamily (L:=L) F)
      (base (geometryFamily (L:=L) F) true) 1).map (GeometryGroup T L F).subtype := by
  let X := GeometryGroup T L F
  let Ω := geometryFamily (L:=L) F
  have hQT : F.H.pCoreIn 2 ≤ (T:Subgroup G) :=
    (pCoreIn_le_sylow F.H (T.subtype (F.invariant 1))).trans_eq
      (map_subgroupOf_eq_of_le (F.invariant 1))
  have hn : F.H ≤ normalizer (F.H.pCoreIn 2 : Set G) :=
    F.H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image F.H (pCore 2 F.H))
  intro q hq
  let q' : X := ⟨q,mem_sup_right (pCoreIn_le 2 F.H hq)⟩
  refine ⟨q',?_,rfl⟩
  intro w hw
  rcases (mem_ball_one Ω (base Ω true) w).mp hw with hw | rfl
  · obtain ⟨h,hh,rfl⟩ := locally_transitive Ω
      (show (graph Ω).Adj (base Ω true) (base Ω false) from
        ⟨by change true≠false; decide,CosetGeometry.incident_base Ω true false⟩) hw
    have hhH : (h:G) ∈ F.H := by
      have hh' : h ∈ Ω true := by
        simpa only [stabilizer,base,CosetGeometry.stabilizer_base] using hh
      exact hh'
    have hc : (h:G)⁻¹*q*(h:G) ∈ F.H.pCoreIn 2 := by
      simpa only [inv_inv] using
        (mem_normalizer_iff.mp (hn (F.H.inv_mem hhH)) q).mp hq
    have hm : h⁻¹*q'*h ∈ Ω false := mem_sup_right (hQT hc)
    have hf : (h⁻¹*q'*h) • base Ω false=base Ω false := by
      apply MulAction.mem_stabilizer_iff.mp
      simpa only [CosetGeometry.stabilizer_base] using hm
    calc
      q' • (h • base Ω false) = h • ((h⁻¹*q'*h) • base Ω false) := by
        simp only [mul_smul,smul_inv_smul]
      _ = h • base Ω false := congrArg (h • ·) hf
  · apply MulAction.mem_stabilizer_iff.mp
    simpa only [CosetGeometry.stabilizer_base] using
      (show q' ∈ Ω true from pCoreIn_le 2 F.H hq)

include d in
theorem critical_span_not_le_reciprocal_core (c : CriticalPath (L:=L) F) :
    ¬ F.U ≤ c.Qα := by
  intro hU
  let X := GeometryGroup T L F
  let Ω := geometryFamily (L:=L) F
  apply c.critical
  intro v hv
  have hvU : (v:G) ∈ F.U := V_le_U F hv
  have hvh : (c.rechoice:G)⁻¹*(v:G)*(c.rechoice:G) ∈ F.U := by
    simpa only [inv_inv] using (mem_normalizer_iff.mp
      (d.conjugationSection.normalized (F.H.inv_mem c.rechoice.property)) (v:G)).mp hvU
  have hq := hU hvh
  change (c.rechoice:G)⁻¹*(v:G)*(c.rechoice:G) ∈
    (conjugate F.H c.conjugator).pCoreIn 2 at hq
  unfold conjugate at hq
  rw [← map_pCoreIn_of_injective 2 F.H (MulAut.conj c.conjugator⁻¹).toMonoidHom
    (MulAut.conj c.conjugator⁻¹).injective] at hq
  obtain ⟨q,hq,he⟩ := hq
  have heq : (c.gammaConjugator:G)*(v:G)*(c.gammaConjugator:G)⁻¹=q := by
    simp only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv] at he
    have he' := congrArg (fun x:G => c.conjugator*x*c.conjugator⁻¹) he
    simp only [CriticalPath.conjugator,mul_inv_rev] at he'
    group at he'
    simpa only [zpow_neg_one] using he'.symm
  have hq' := (core_le_H_neighborhood (L:=L) (F:=F)) hq
  obtain ⟨q',hq',he'⟩ := hq'
  have hval : c.gammaConjugator*v*c.gammaConjugator⁻¹=q' :=
    Subtype.ext (heq.trans he'.symm)
  apply (conj_mem_ballKernel_iff Ω c.gammaConjugator v
    (c.gammaConjugator⁻¹ • base Ω true) 1).mp
  rw [smul_inv_smul,hval]
  exact hq'

include d in
theorem critical_index_positive (c : CriticalPath (L:=L) F) :
    0 < Nat.log 2 ((F.U ⊓ c.Qα).relIndex F.U) := by
  have hn : (F.U ⊓ c.Qα).relIndex F.U ≠ 1 := by
    intro he
    exact d.critical_span_not_le_reciprocal_core c ((relIndex_eq_one.mp he).trans inf_le_right)
  have hp : 0 < (F.U ⊓ c.Qα).relIndex F.U := Nat.pos_of_ne_zero (by
    intro he
    have hh := relIndex_dvd_card (F.U ⊓ c.Qα) F.U
    rw [he,zero_dvd_iff] at hh
    exact Nat.card_pos.ne' hh)
  exact Nat.log_pos (by decide) (by omega)
end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Data
open Subgroup Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
variable (d : Data T L V F W)

include d in
theorem critical_star_nontrivial
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hUQ : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (c : CriticalPath (L:=L) F) : star F c.Uα ≠ ⊥ := by
  intro hz
  have hAH : c.Uα ≤ F.H := (d.source_critical_le_Q structural c).trans (Q_le_H F)
  have hαQ : c.Uα ≤ F.H.pCoreIn 2 := by
    have hk : c.Uα.subgroupOf F.H ≤ pCore 2 F.H := by
      simpa only [star,Subgroup.map_eq_bot_iff,starMap,QuotientGroup.ker_mk'] using hz
    intro x hx
    exact mem_map.mpr ⟨⟨x,hAH hx⟩,hk hx,rfl⟩
  let f := (MulAut.conj c.conjugator).toMonoidHom
  let A := F.U.map f
  let C := (F.Vi 1).map f
  have hmap : c.Uα.map f=F.U := by
    change (F.U.conjBy c.conjugator⁻¹).conjBy c.conjugator=F.U
    exact conjBy_inv' _ _
  have hA : A ≤ F.H := by
    have h := map_mono (f:=f) (d.source_reciprocal_placement c)
    change A ≤ (F.H.conjBy c.conjugator⁻¹).conjBy c.conjugator at h
    rwa [conjBy_inv'] at h
  have hc : ⁅A,F.U⁆ ≤ C := by
    have h := map_mono (f:=f) ((commutator_mono le_rfl hαQ).trans_eq hUQ)
    rwa [map_commutator,hmap] at h
  have hcard : Nat.card C ≤ 2 := by
    rw [show Nat.card C=Nat.card (F.Vi 1) from card_map_of_injective
      (MulAut.conj c.conjugator).injective]
    exact (show Nat.card (F.Vi 1)=2 by simpa using F.card 1 (by decide)).le
  have hAQ : A ≤ F.H.pCoreIn 2 := by
    intro x hx
    exact d.actor_in_core_of_small_commutator A C hc hcard ⟨x,hA hx⟩ hx
  apply d.critical_span_not_le_reciprocal_core c
  intro x hx
  change x ∈ (conjugate F.H c.conjugator).pCoreIn 2
  unfold conjugate
  rw [← map_pCoreIn_of_injective 2 F.H (MulAut.conj c.conjugator⁻¹).toMonoidHom
    (MulAut.conj c.conjugator⁻¹).injective]
  refine ⟨f x,hAQ (mem_map_of_mem f hx),?_⟩
  simp [f,MulAut.conj_apply,mul_assoc]
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Data
