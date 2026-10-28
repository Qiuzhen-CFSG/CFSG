module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CriticalActors
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.Alternating.DeletedExclusion
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.Geometry
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CriticalGeometry
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.DeletedExclusion
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.NaturalQuotient
public import Theory.SpecificGroups.SymmetricFourResidualCore

/-!
# Critical actors in the local alternating branch

The point-core image is the even four-group. A faithful alternating involution cannot have displacement in one line. Transporting the terminal edge of the actual critical path therefore proves its starred actor nontrivial.

Only Structural1222At at the original G,T is used. Independent model and
section lemmas are reused from LocalReduction; its universal APIs are preserved.
Source: Aschbacher–Smith, final paragraph of 14.7.40, printed p.1063,
and 14.7.52–63, printed pp.1065–1069. Earlier structural source discharge
and the unconditional classification remain with their existing owners.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
local notation "S5" => ChapterJ.S5
local notation "A5" => alternatingGroup (Fin 5)

private def pointEquiv (i : Fin 5) :
    MulAction.stabilizer S5 i ≃* Equiv.Perm (Fin 4) := by
  let p := fun a : Fin 5 => a ≠ i
  let f : Equiv.Perm {a : Fin 5 // p a} →* MulAction.stabilizer S5 i :=
    (Equiv.Perm.ofSubtype : Equiv.Perm {a : Fin 5 // p a} →* S5).codRestrict _
      (fun g => Equiv.Perm.ofSubtype_apply_of_not_mem g (by simp [p]))
  have hf : Function.Bijective f := by
    refine ⟨fun a b h => Equiv.Perm.ofSubtype_injective (congrArg Subtype.val h), ?_⟩
    intro g
    have hg : g.val i = i := g.property
    have hpred (a : Fin 5) : p (g.val a) ↔ p a := by
      change g.val a ≠ i ↔ a ≠ i
      exact ⟨fun hn he => hn (he ▸ hg), fun hn he => hn (g.val.injective (he.trans hg.symm))⟩
    refine ⟨g.val.subtypePerm hpred, ?_⟩
    apply Subtype.ext
    apply Equiv.Perm.ofSubtype_subtypePerm
    intro a ha hai
    exact ha (hai.symm ▸ hg)
  exact (MulEquiv.ofBijective f hf).symm.trans
    (Equiv.permCongrHom (finSuccAboveEquiv i).symm)

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}
local notation "B" => (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G)

omit [Finite G] in
private theorem point_le_H : B ≤ F.H :=
  sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)

private theorem point_core_image
    (e : HStar F.H ≃* S5) :
    ((F.Ri L 1).subgroupOf F.H).map (quotientMarking e) =
      (((B).subgroupOf F.H).map (quotientMarking e)).pCoreIn 2 := by
  let q := quotientMarking e
  let f : B →* S5 := q.comp (inclusion point_le_H)
  have hk : IsPGroup 2 f.ker := by
    change IsPGroup 2 (q.ker.comap (inclusion point_le_H))
    have hq : q.ker = pCore 2 F.H := by
      dsimp only [q]
      rw [quotientMarking, MonoidHom.ker_comp_of_injective _ _ e.injective]
      exact QuotientGroup.ker_mk' _
    rw [hq]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)
  have hm := f.rangeRestrict.comap_pCore_of_ker_isPGroup f.rangeRestrict_surjective
    (show IsPGroup 2 f.rangeRestrict.ker by rwa [MonoidHom.ker_rangeRestrict])
  have hmap : (pCore 2 B).map f = f.range.pCoreIn 2 := by
    have hm' : (pCore 2 B).map f.rangeRestrict = pCore 2 f.range := by
      rw [←hm,map_comap_eq_self_of_surjective f.rangeRestrict_surjective]
    have hm'' := congrArg (Subgroup.map f.range.subtype) hm'
    rw [map_map] at hm''
    exact hm''
  have hr : f.range = ((B).subgroupOf F.H).map q := by
    ext x
    constructor
    · rintro ⟨b,rfl⟩
      exact ⟨inclusion point_le_H b,b.property,rfl⟩
    · rintro ⟨b,hb,rfl⟩
      exact ⟨⟨b.val,hb⟩,rfl⟩
  rw [← hr, ← hmap]
  ext x
  constructor
  · rintro ⟨b,⟨a,ha,he⟩,rfl⟩
    exact ⟨a,ha,congrArg q (Subtype.ext he)⟩
  · rintro ⟨a,ha,rfl⟩
    exact ⟨inclusion point_le_H a,⟨a,ha,rfl⟩,rfl⟩

/-- The image of the original R₁ in every S₅ marking has order four. -/
theorem point_core_image_card_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (e : HStar F.H ≃* S5) :
    Nat.card (((F.Ri L 1).subgroupOf F.H).map (quotientMarking e)) = 4 := by
  let q := quotientMarking e
  let f : B →* S5 := q.comp (inclusion point_le_H)
  have hk : IsPGroup 2 f.ker := by
    change IsPGroup 2 ((quotientMarking e).ker.comap (inclusion point_le_H))
    rw [quotientMarking, MonoidHom.ker_comp_of_injective _ _ e.injective,
      starMap, QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)
  have hr : f.range = ((B).subgroupOf F.H).map q := by
    ext x
    constructor
    · rintro ⟨b,rfl⟩; exact ⟨inclusion point_le_H b,b.property,rfl⟩
    · rintro ⟨b,hb,rfl⟩; exact ⟨⟨b.val,hb⟩,rfl⟩
  have hc := point_image_ratio_at h structural f hk
  obtain ⟨i,hi⟩ := point_image_stabilizer_at h structural e
  have hI : Nat.card f.range = 24 := by
    rw [hr,hi,Nat.card_congr (pointEquiv i).toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  rw [point_core_image, ← hr]
  change Nat.card ((pCore 2 f.range).map f.range.subtype) = 4
  rw [card_map_of_injective f.range.subtype_injective]
  omega

/-- The same four-group lies in the actual alternating residual image. -/
theorem point_core_image_le_alternating_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (e : HStar F.H ≃* S5) :
    ((F.Ri L 1).subgroupOf F.H).map (quotientMarking e) ≤ A5 := by
  obtain ⟨i,hi⟩ := point_image_stabilizer_at h structural e
  rw [point_core_image,hi]
  have hcore := Theory.SpecificGroups.SymmetricFour.twoCore_le_twoResidual_of_equiv
    (pointEquiv i)
  have hm := (map_mono (f := (MulAction.stabilizer S5 i).subtype) hcore).trans
    (map_pResidual_le 2 (MulAction.stabilizer S5 i).subtype)
  exact hm.trans_eq (Equiv.Perm.twoResidual_eq_alternating (Fin 5))

/-- A point-core actor with displacement in one ambient line lies in O₂(H).
The detector uses only the faithful original action and the even four-group. -/
theorem point_actor_in_core_of_line_commutator_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (e : HStar F.H ≃* S5)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (A C : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : A ≤ F.Ri L 1) (hc : ⁅A,F.U⁆ ≤ C) (hC : Nat.card C ≤ 2) :
    A ≤ F.H.pCoreIn 2 := by
  let : Finite W := Finite.of_surjective (fun v : F.U => (s.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  obtain ⟨σ,hσ,hinj⟩ := exists_faithful_symmetric_representation h e s
  let D := s.imageSpace C
  have hDcard : Nat.card D ≤ 2 := by
    change Nat.card ((C.subgroupOf F.U).map s.coordinates) ≤ 2
    have hm := Nat.card_le_card_of_surjective (s.coordinates.subgroupMap
      (C.subgroupOf F.U)) (s.coordinates.subgroupMap_surjective _)
    have hs : Nat.card (C.subgroupOf F.U) ≤ Nat.card C :=
      Nat.card_le_card_of_injective (fun y => (⟨y.val,y.property⟩ : C))
        (by
          intro a b he
          apply Subtype.ext
          apply Subtype.ext
          exact congrArg (fun z : C => (z:G)) he)
    exact hm.trans (hs.trans hC)
  have hdim : Module.finrank (ZMod 2) D ≤ 1 := by
    rw [Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_zmod] at hDcard
    by_contra hn
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2)
      (show 2 ≤ Module.finrank (ZMod 2) D by omega)
    omega
  intro x hx
  have hxH : x ∈ F.H := point_le_H (pCoreIn_le 2 B (hA hx))
  let xH : F.H := ⟨x,hxH⟩
  have hxa : quotientMarking e xH ∈ A5 :=
    point_core_image_le_alternating_at h structural e (mem_map_of_mem _ (hA hx))
  let a : A5 := ⟨quotientMarking e xH,hxa⟩
  have ha2 : a ^ 2 = 1 := by
    apply Subtype.ext
    change quotientMarking e xH ^ 2 = 1
    rw [←map_pow]
    have he : xH ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian x hx)
    rw [he,map_one]
  have hr : Module.finrank (ZMod 2) (ρ xH - LinearMap.id).range ≤ 1 :=
    (Submodule.finrank_mono (s.displacement_range_le_imageSpace_of_commutator_le
      A C hc xH hx)).trans hdim
  have ha : a = 1 := by
    by_contra hn
    have hlo := AlternatingFiveInvolutionDisplacement.displacement_lower
      (σ.comp (A5).subtype) (hinj.comp (A5).subtype_injective) a
      (orderOf_eq_prime ha2 hn)
    have he : (σ.comp (A5).subtype) a = ρ xH :=
      congrArg (fun τ : Representation (ZMod 2) F.H W => τ xH) hσ
    rw [he] at hlo
    omega
  have he : quotientMarking e xH = 1 := congrArg Subtype.val ha
  have hker : (quotientMarking e).ker = pCore 2 F.H := by
    rw [quotientMarking,MonoidHom.ker_comp_of_injective _ _ e.injective]
    exact QuotientGroup.ker_mk' _
  exact mem_map_of_mem F.H.subtype (hker ▸ (show xH ∈ (quotientMarking e).ker from he))

open Subgroup.CosetGeometry.RankTwo

/-- Normalize the last edge, retaining the original span and central point.
The transported reciprocal actor lies in the original R₁. -/
theorem exists_terminal_edge_transport_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (c : CriticalPath (L := L) F) :
    ∃ g : G, (conjugate F.U c.conjugator).map (MulAut.conj g).toMonoidHom = F.U ∧
      (conjugate F.H c.conjugator).map (MulAut.conj g).toMonoidHom = F.H ∧
      F.U.map (MulAut.conj g).toMonoidHom ≤ F.Ri L 1 := by
  let X := GeometryGroup T L F
  let Ω := geometryFamily (L := L) F
  let r : X := inclusion (le_sup_right : F.H ≤ X) c.rechoice
  let k : X := c.gammaConjugator*r
  let w := r⁻¹ • c.path.getVert (c.b-1)
  let α := k⁻¹ • base Ω true
  have hadj : (graph Ω).Adj w α := by
    have he := c.path.adj_getVert_succ (i := c.b-1) (by rw [c.length]; have := c.three_le; omega)
    have hlast : c.path.getVert (c.b-1+1) = c.gammaConjugator⁻¹ • base Ω true := by
      rw [Nat.sub_add_cancel (by have := c.three_le; omega), ←c.length]
      exact c.path.getVert_length
    rw [hlast] at he
    have ht := (Subgroup.CosetGeometry.translationGraphIso Ω r⁻¹).toHom.map_adj he
    change (graph Ω).Adj (r⁻¹ • c.path.getVert (c.b-1))
      (r⁻¹ • (c.gammaConjugator⁻¹ • base Ω true)) at ht
    simpa only [α,k,mul_inv_rev,mul_smul] using ht
  have hka : k • α = base Ω true := smul_inv_smul _ _
  have hadj' : (graph Ω).Adj (base Ω true) (k • w) := by
    have ht := (Subgroup.CosetGeometry.translationGraphIso Ω k).toHom.map_adj hadj.symm
    change (graph Ω).Adj (k • α) (k • w) at ht
    simpa only [hka] using ht
  obtain ⟨t,ht,hte⟩ := locally_transitive Ω
    (show (graph Ω).Adj (base Ω true) (base Ω false) from
      ⟨by change true ≠ false; decide,Subgroup.CosetGeometry.incident_base Ω true false⟩) hadj'
  have htH : (t:G) ∈ F.H := by
    have ht' : t ∈ Ω true := by simpa only [stabilizer,Subgroup.CosetGeometry.stabilizer_base] using ht
    exact ht'
  let g : X := t⁻¹*k
  have hgw : g • w = base Ω false := by
    dsimp only [g]
    rw [mul_smul,←hte,inv_smul_smul]
  have hgα : g • α = base Ω true := by
    dsimp only [g]
    rw [mul_smul,hka]
    have he : t • base Ω true = base Ω true := ht
    exact (congrArg (t⁻¹ • ·) he).symm.trans (inv_smul_smul t _)
  have hrH : r⁻¹ • base Ω true = base Ω true := by
    have he : r • base Ω true = base Ω true := by
      apply MulAction.mem_stabilizer_iff.mp
      simpa only [Subgroup.CosetGeometry.stabilizer_base] using
        (show r ∈ Ω true from c.rechoice.property)
    exact (congrArg (r⁻¹ • ·) he).symm.trans (inv_smul_smul r _)
  have hd : (graph Ω).dist (base Ω true) w ≤ c.b-2 := by
    have hp := SimpleGraph.dist_le ((c.path.take (c.b-1)).drop 1)
    rw [SimpleGraph.Walk.drop_length,SimpleGraph.Walk.take_length,c.length,
      Nat.min_eq_left (Nat.sub_le _ _),SimpleGraph.Walk.take_getVert, Nat.min_eq_right (by have := c.three_le; omega : 1 ≤ c.b-1),c.first] at hp
    have he : c.b-1-1=c.b-2 := by omega
    rw [he] at hp
    have hd' := Subgroup.CosetGeometry.RankTwo.dist_smul Ω r⁻¹
      (base Ω true) (c.path.getVert (c.b-1))
    rw [hrH] at hd'
    exact hd'.trans_le hp
  have hdg : (graph Ω).dist (g • base Ω true) (base Ω false) ≤ c.b-2 := by
    rw [←hgw,Subgroup.CosetGeometry.RankTwo.dist_smul]
    exact hd
  have hAQ : F.U.map (MulAut.conj (g:G)).toMonoidHom ≤ Q T L := by
    rintro x ⟨u,hu,rfl⟩
    obtain ⟨u',hu',he⟩ := span_ballKernel h c hu
    have hm : g*u'*g⁻¹ ∈ ballKernel Ω (g • base Ω true) (c.b-1) :=
      (conj_mem_ballKernel_iff Ω g u' (base Ω true) (c.b-1)).mpr hu'
    have hb := ChapterF.Section07.Track.ballKernel_le_of_dist_add_le Ω
      (ChapterF.Section07.Geometry.family_generates _ _) (m:=1) (n:=c.b-1)
      (show (graph Ω).dist (g • base Ω true) (base Ω false)+1 ≤ c.b-1 by
        have := c.three_le; omega) hm
    have hq := base_kernel_le_Q_at h structural (mem_map_of_mem X.subtype hb)
    change (g:G)*(u':G)*(g:G)⁻¹ ∈ Q T L at hq
    change (u':G)=u at he
    rw [he] at hq
    exact hq
  refine ⟨g,?_,?_,?_⟩
  · change (F.U.conjBy c.conjugator⁻¹).conjBy (g:G) = F.U
    rw [←conjBy_mul]
    have he : (g:G)*c.conjugator⁻¹=(t:G)⁻¹ := by
      change ((t:G)⁻¹*(k:G))*(k:G)⁻¹=(t:G)⁻¹
      group
    rw [he]
    exact mem_normalizer_iff_map_conj_eq.mp
      (le_normalizer_conjugateSpanBy V F.H (F.H.inv_mem htH))
  · change (F.H.conjBy c.conjugator⁻¹).conjBy (g:G) = F.H
    rw [←conjBy_mul]
    have he : (g:G)*c.conjugator⁻¹=(t:G)⁻¹ := by
      change ((t:G)⁻¹*(k:G))*(k:G)⁻¹=(t:G)⁻¹
      group
    rw [he]
    exact mem_normalizer_iff_map_conj_eq.mp (F.H.le_normalizer (F.H.inv_mem htH))
  · have hQT : Q T L ≤ (T:Subgroup G) :=
      (pCoreIn_le_sylow (L ⊔ (T:Subgroup G)) (T.subtype le_sup_right)).trans_eq
        (map_subgroupOf_eq_of_le le_sup_right)
    have hle : B ≤ L ⊔ (T:Subgroup G) :=
      sup_le_sup ((F.Li_le L 1).trans inf_le_left) le_rfl
    exact hAQ.trans ((le_inf (hQT.trans le_sup_right) le_rfl).trans (inf_pCoreIn_le_of_le 2 hle))

/-- Critical escape in the alternating branch, using the terminal-edge
transport and the original section before natural recognition. -/
theorem critical_star_nontrivial_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (e : HStar F.H ≃* S5) (c : CriticalPath (L := L) F) :
    star F c.Uα ≠ ⊥ := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  intro hz
  have hAH : c.Uα ≤ F.H := (critical_le_Ri_at h structural c).trans ((pCoreIn_le 2 B).trans point_le_H)
  have hαQ : c.Uα ≤ F.H.pCoreIn 2 := by
    have hk : c.Uα.subgroupOf F.H ≤ pCore 2 F.H := by
      simpa only [CriticalFusion.Source.star,Subgroup.map_eq_bot_iff,starMap,QuotientGroup.ker_mk'] using hz
    intro x hx
    exact mem_map.mpr ⟨⟨x,hAH hx⟩,hk hx,rfl⟩
  have hcomm : ⁅F.U,c.Uα⁆ ≤ F.Vi 1 := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro a ha u hu
    have haH : a ∈ F.H := hAH ha
    have hqa : (⟨a,haH⟩ : F.H) ∈ pCore 2 F.H := by
      have hh := hαQ ha
      obtain ⟨a',ha',he⟩ := hh
      exact (show a' = ⟨a,haH⟩ from Subtype.ext he) ▸ ha'
    exact (s.action_mem_ker_iff ⟨a,haH⟩).mp (core_le_action_kernel h s hqa) u hu
  obtain ⟨g,hUg,hHg,hAR⟩ := exists_terminal_edge_transport_at h structural c
  let f := (MulAut.conj g).toMonoidHom
  let A := F.U.map f
  let C := (F.Vi 1).map f
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hc : ⁅A,F.U⁆ ≤ C := by
    have hm := map_mono (f:=f) hcomm
    change c.Uα.map f = F.U at hUg
    rw [map_commutator,hUg] at hm
    exact hm
  have hC : Nat.card C ≤ 2 := by
    rw [card_map_of_injective (MulAut.conj g).injective]
    exact (show Nat.card (F.Vi 1)=2 by simpa using F.card 1 (by decide)).le
  have hAQ := point_actor_in_core_of_line_commutator_at h structural e s A C hAR hc hC
  have hQmap : c.Qα.map f = F.H.pCoreIn 2 := by
    change ((conjugate F.H c.conjugator).pCoreIn 2).map f = _
    rw [map_pCoreIn_of_injective 2 _ f (MulAut.conj g).injective,hHg]
  apply critical_span_not_le_reciprocal_core c
  exact (map_le_map_iff_of_injective (f:=f) (MulAut.conj g).injective).mp
    (hAQ.trans_eq hQmap.symm)


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
