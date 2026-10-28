module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.G2Reconstruction.DistanceTwo.DistanceFour.NonfixedSeed
public import Theory.GroupAction.SymmetricSixChiefBudget.Quotient
public import Theory.GroupTheory.Commutator.AbelianEdgeCentrality
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.SectionFive.RadiusCentrality

/-!
# Centrality of the G₂ radius under its whole vertex kernel

The projected G₂ small-displacement theorem forces a nonfixed normal
section to have fixed index greater than four. The product inequality for
fixed indices therefore prevents both a normal section and its quotient
from moving under the residual when the total index is at most eight.
This yields the source residual dichotomy without assuming that the radius
or its quotient by the seed is elementary abelian.

Apply the dichotomy to [V,Q] modulo Z, using the actual critical endpoint,
its original actor map, and the proved radius-index bound. An abelian
incident edge radius normally generates V. In the fixed branch this makes
[V,Q] central in V; the covering branch follows by nilpotent commutator
saturation. The three-subgroup lemma now gives V' ≤ Ω₁Z(Q).

The actual critical commutator, and its commutator with the first edge
kernel, consequently lie in the midpoint elementary center. The triple
also lies in the starting moving seed. These conclusions supply the
kernel-centrality step on MS93 (3.8), printed p.878. They do not identify
the midpoint elementary center with its residual-fixed core. The remaining
moving-seed and auxiliary-subgroup argument on p.879 belongs to
qt-e-ms-small-g2-reconstruction, including final reconstruction assembly.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.8), printed pp.878--879. The fixed-index and abelian-edge lemmas
are reused from the source-neutral theory behind the analogous (5.2) proof.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped commutatorElement
open CFSG.Quasithin
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.G2Reconstruction.DistanceTwo.DistanceFour
open NoncentralChiefRefinement

private theorem section_fixed_index {S : Type*} [Group S] (A U X : Subgroup S)
    [U.Normal] [X.Normal] :
    SymmetricSixBudget.sectionIndex A ⟨X,inferInstanceAs X.Normal⟩ ⟨U,inferInstanceAs U.Normal⟩ =
      (centralizerModulo U A X).relIndex U := by
  let μ : MulDistribMulAction S (Section (⟨X,inferInstanceAs X.Normal⟩ : NormalNode S) ⟨U,inferInstanceAs U.Normal⟩) :=
    MulDistribMulAction.compHom _
      (sectionAction (⟨X,inferInstanceAs X.Normal⟩ : NormalNode S) ⟨U,inferInstanceAs U.Normal⟩)
  let := μ
  let N := X.subgroupOf U
  let π := QuotientGroup.mk' N
  let F := FixedPoints.subgroup A (U ⧸ N)
  have he : F.comap π = (centralizerModulo U A X).subgroupOf U := by
    ext x
    change (∀ a : A, π (MulAut.conjNormal (a : S) x) = π x) ↔ _
    rw [mem_subgroupOf,mem_centralizerModulo_iff,and_iff_right x.property]
    constructor
    · intro hx a ha
      have hh := (QuotientGroup.eq_iff_div_mem).mp (hx ⟨a,ha⟩)
      simpa only [N,mem_subgroupOf,div_eq_mul_inv,coe_mul,coe_inv,MulAut.conjNormal_apply,
        commutatorElement_def] using hh
    · intro hx a
      apply (QuotientGroup.eq_iff_div_mem).mpr
      simpa only [N,mem_subgroupOf,div_eq_mul_inv,coe_mul,coe_inv,MulAut.conjNormal_apply,
        commutatorElement_def] using hx a a.property
  change F.index = _
  rw [←F.index_comap_of_surjective (QuotientGroup.mk'_surjective N),he]
  rfl

section Projected
variable {S D : Type*} [Group S] [Finite S] [Group D] [Finite D]
  (q : S →* D) (hq : Function.Surjective q) (hp : IsPGroup 2 q.ker)
  (C : Subgroup D) [C.Normal] [IsSimpleGroup C] [IsQuasisimple C]
  (hres : (pResidual 2 S).map q = C)
  (hc : Nat.card C = 6048) (hC : centralizer (C : Set D) = ⊥)
  (hsq : IsSQTK KnownSimple.IsKnownSimple C)

include hq hp hres hc hC hsq

/-- A fixed index at most eight allows residual movement on only one of
an arbitrary normal two-section and its quotient. -/
theorem projected_g2_residual_dichotomy
    (U X : Subgroup S) [U.Normal] [X.Normal] (hU : IsPGroup 2 U) (hXU : X ≤ U)
    (A : Subgroup S) (hA : IsElementaryAbelian 2 A) (hcard : Nat.card (A.map q) = 8)
    (hindex : (centralizer (A : Set S)).relIndex U ≤ 8) :
    ⁅X,pResidual 2 S⁆ = ⊥ ∨ ⁅U,pResidual 2 S⁆ ≤ X := by
  have hbudget := SymmetricSixBudget.sectionIndex_mul_lower_le A
    (⟨X,inferInstanceAs X.Normal⟩ : NormalNode S) ⟨U,inferInstanceAs U.Normal⟩ hXU
  rw [section_fixed_index A U X] at hbudget
  change (centralizerModulo U A X).relIndex U *
    (centralizer (A : Set S)).relIndex X ≤ (centralizer (A : Set S)).relIndex U at hbudget
  by_cases hsmall : (centralizer (A : Set S)).relIndex X ≤ 4
  · left
    apply bot_unique
    apply projected_g2_commutator_le_of_small_index q hq hp C hres hc hC hsq
      X ⊥ (hU.to_le hXU) A hA hcard (centralizer (A : Set S)) _ hsmall
    exact (commutator_eq_bot_iff_le_centralizer.mpr inf_le_right).le
  · right
    have hsmall' : (centralizerModulo U A X).relIndex U ≤ 4 := by
      by_contra hn
      have hm : 25 ≤ (centralizerModulo U A X).relIndex U *
          (centralizer (A : Set S)).relIndex X := Nat.mul_le_mul
            (show 5 ≤ (centralizerModulo U A X).relIndex U by omega)
            (show 5 ≤ (centralizer (A : Set S)).relIndex X by omega)
      omega
    apply projected_g2_commutator_le_of_small_index q hq hp C hres hc hC hsq
      U X hU A hA hcard (centralizerModulo U A X) _ hsmall'
    rw [commutator_comm]
    apply commutator_le.mpr
    intro a ha x hx
    exact (mem_centralizerModulo_iff.mp hx.2).2 a ha

/-- The same residual dichotomy on the actual quotient by a specified normal
subgroup, with the original projection retained. -/
theorem projected_g2_residual_dichotomy_modulo
    (V Z : Subgroup S) [V.Normal] [Z.Normal] (hZV : Z ≤ V) (hV : V ≤ q.ker)
    (A : Subgroup S) (hA : IsElementaryAbelian 2 A) (hcard : Nat.card (A.map q) = 8)
    (hindex : (centralizerModulo V A Z).relIndex V ≤ 8)
    (X : Subgroup S) [X.Normal] (hXV : X ≤ V) :
    ⁅X,pResidual 2 S⁆ ≤ Z ∨ ⁅V,pResidual 2 S⁆ ≤ X ⊔ Z := by
  let π := QuotientGroup.mk' Z
  let qbar := QuotientGroup.lift Z q (hZV.trans hV)
  have hqbar : Function.Surjective qbar :=
    QuotientGroup.lift_surjective_of_surjective Z q hq _
  have hker : qbar.ker = q.ker.map π := QuotientGroup.ker_lift Z q _
  have hpbar : IsPGroup 2 qbar.ker := by rw [hker]; exact hp.map π
  let : (V.map π).Normal := Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective Z)
  let : (X.map π).Normal := Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective Z)
  have hVbar : V.map π ≤ qbar.ker := by rw [hker]; exact map_mono hV
  have hAbar : (A.map π).map qbar = A.map q := by rw [map_map]; rfl
  have hresbar : (pResidual 2 (S ⧸ Z)).map qbar = C := by
    rw [←map_pResidual_quotient 2 Z,map_map]
    exact hres
  have hidxbar : (centralizer (A.map π : Set (S ⧸ Z))).relIndex (V.map π) ≤ 8 := by
    rwa [SymmetricSixBudget.centralizerModulo_relIndex_eq] at hindex
  have hAb : IsElementaryAbelian 2 (A.map π) := by let := hA; exact IsElementaryAbelian.map π
  have hh := projected_g2_residual_dichotomy qbar hqbar hpbar C hresbar hc hC hsq
    (V.map π) (X.map π) (hpbar.to_le hVbar) (map_mono hXV)
    (A.map π) hAb (hAbar.symm ▸ hcard) hidxbar
  have hresπ : (pResidual 2 S).map π = pResidual 2 (S ⧸ Z) := map_pResidual_quotient 2 Z
  rcases hh with hh | hh
  · left
    have hm : (⁅X,pResidual 2 S⁆).map π ≤ ⊥ := by rw [map_commutator,hresπ,hh]
    have hk := (map_le_iff_le_comap).mp hm
    simpa only [MonoidHom.comap_bot,π,QuotientGroup.ker_mk'] using hk
  · right
    have hm : (⁅V,pResidual 2 S⁆).map π ≤ X.map π := by rwa [map_commutator,hresπ]
    have hk := (map_le_iff_le_comap).mp hm
    simpa only [comap_map_eq,π,QuotientGroup.ker_mk'] using hk


end Projected

open Stellmacher.PushingUp.AmalgamGraph
open ChapterC BinaryMS.MS93 BinaryMS.MS93.NaturalStructure.Exclusion
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
local notation "T" => R.subgroupOf (L ⊔ R)

private theorem radius_le_of_normalized_edge
    {a t : Vertex T} (ha : color T a = false) (hat : Adjacent T a t)
    (K : Subgroup (FreeAmalgam T)) (hEK : V T t ≤ K)
    (hn : stabilizer T a ≤ normalizer (K : Set (FreeAmalgam T))) : V T a ≤ K := by
  apply radius_le_of_m_ball ha
  intro d hd hdist
  have hseed {v w : Vertex T} (hvw : Adjacent T v w) : Z T v ≤ V T w :=
    le_iSup_of_le v (le_iSup_of_le
      ((SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj T _ _).mpr hvw)).le.trans
        (by decide : 1 ≤ 2)) le_rfl)
  by_cases hda : d = a
  · subst d
    exact (hseed hat).trans hEK
  have htwo : (cosetGraph T).dist a d = 2 := by
    have hne : (cosetGraph T).dist a d ≠ 0 := by
      intro hz
      exact hda ((cosetGraph_connected T).dist_eq_zero_iff.mp hz).symm
    have heven : Even ((cosetGraph T).dist a d) := by
      obtain ⟨w,hw⟩ := (cosetGraph_connected T).exists_walk_length_eq_dist a d
      rw [←hw,walk_even_iff_color_eq,ha,hd]
    rw [Nat.even_iff] at heven
    rw [SimpleGraph.dist_comm] at hdist
    omega
  obtain ⟨v,hav,hdv⟩ := exists_common_neighbor_of_dist_two T a d htwo
  obtain ⟨g,hg,hgv⟩ := stabilizer_transitive_neighbors T a hat hav
  have hVK : V T v ≤ K := by
    rw [←hgv,V_act]
    exact (map_mono hEK).trans
      (mem_normalizer_iff_map_conj_eq.mp (hn ((stabilizer T a).inv_mem hg))).le
  exact (hseed hdv).trans hVK

variable (h : SmallMSPair KnownSimple.IsKnownSimple L R)
  (e : (L ⧸ centralPreimage (pCore 2 L)) ≃* commutator (Atlas.G2.Model (ZMod 2)))
include h

/-- The abelian incident radius turns the source residual dichotomy into
centrality of the radius commutator with its actual vertex kernel. -/
theorem radius_kernel_commutator_central_of_dichotomy
    (hb : 2 < (geometry h).b T) (a t : Vertex T)
    (ha : color T a = false) (hat : Adjacent T a t)
    (hd : ⁅⁅V T a,Q T a⁆,Ltilde T a⁆ ≤ Z T a ∨
      ⁅V T a,Ltilde T a⁆ ≤ ⁅V T a,Q T a⁆ ⊔ Z T a) :
    ⁅V T a,Q T a⁆ ≤ centralizer (V T a : Set (FreeAmalgam T)) := by
  let S := stabilizer T a
  let V₀ := (V T a).subgroupOf S
  let E := (V T t).subgroupOf S
  let Z₀ := (Z T a).subgroupOf S
  let P := (Q T a).subgroupOf S
  let T₀ := (Q T t).subgroupOf S
  let := finite_stabilizer T a
  let : V₀.Normal := normal_subgroupOf_of_le_normalizer (V_normalized a)
  let : P.Normal := Q_normal T a
  let : Z₀.Normal := (geometry h).Z_normal a
  have hVQ := (geometry h).V_le_Q hb a ha
  have hVS : V T a ≤ S := hVQ.trans (fun _ hx => hx.1)
  have htV := edge_radius_le_radius ha hat
  have hES : V T t ≤ S := htV.trans hVS
  have hQS : Q T a ≤ S := fun _ hx => hx.1
  have hTS : Q T t ≤ S := CriticalCriterion.edge_le_stabilizer T ha hat
  have hVm : V₀.map S.subtype = V T a := map_subgroupOf_eq_of_le hVS
  have hEm : E.map S.subtype = V T t := map_subgroupOf_eq_of_le hES
  have hZm : Z₀.map S.subtype = Z T a := map_subgroupOf_eq_of_le (Z_le_stabilizer T a)
  have hPm : P.map S.subtype = Q T a := map_subgroupOf_eq_of_le hQS
  have hTm : T₀.map S.subtype = Q T t := map_subgroupOf_eq_of_le hTS
  have ht : color T t = true := by
    have hn := adjacent_color_ne T hat
    cases ht : color T t <;> simp_all
  have hPT : P ≤ T₀ := comap_mono (Q_le_adjacent_h T ht hat)
  have hTE : T₀ ≤ normalizer (E : Set S) := by
    apply le_normalizer_iff.mpr
    intro x hx y hy
    exact le_normalizer_iff.mp (V_normalized t) _ hx.1 _ hy
  have hgen : pResidual 2 S ⊔ T₀ = ⊤ := by
    apply map_injective S.subtype_injective
    rw [Subgroup.map_sup,hTm,←MonoidHom.range_eq_map,range_subtype]
    exact local_generation_edge h ha hat
  have hEV : E ≤ V₀ := comap_mono htV
  have hZE : Z₀ ≤ E := comap_mono (le_iSup_of_le a (le_iSup_of_le
    ((SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj T _ _).mpr hat)).le.trans
      (by decide : 1 ≤ 2)) le_rfl))
  have hE : E ≤ centralizer (E : Set S) := by
    have hc := le_centralizer_iff_isMulCommutative.mpr
      (edge_radius_commutative (geometry h) hb a t ha hat)
    intro x hx y hy
    exact Subtype.ext (hc hx y hy)
  have hclosure : V₀ = normalClosure (E : Set S) := by
    apply le_antisymm
    · have hmap : V T a ≤ (normalClosure (E : Set S)).map S.subtype := by
        apply radius_le_of_normalized_edge ha hat
        · rw [←hEm]
          exact map_mono le_normalClosure
        · have hn := le_normalizer_map (H := normalClosure (E : Set S)) S.subtype
          rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hn
          exact hn
      intro x hx
      obtain ⟨y,hy,hyx⟩ := hmap hx
      have he : y = x := Subtype.ext hyx
      exact he ▸ hy
    · exact normalClosure_le_normal hEV
  have hc : ⁅V₀,P⁆ ≤ centralizer (V₀ : Set S) := by
    rcases hd with hd | hd
    · have hfixed : ⁅⁅V₀,P⁆,pResidual 2 S⁆ ≤ Z₀ := by
        apply (map_le_map_iff_of_injective S.subtype_injective).mp
        rwa [map_commutator,map_commutator,hVm,hPm,hZm]
      exact edge_commutator_central_of_residual_fixed V₀ P E Z₀ (pResidual 2 S) T₀
        hclosure hEV hZE hTE hPT hgen hE hfixed
    · have hcover : ⁅V₀,pResidual 2 S⁆ ≤ E ⊔ ⁅V₀,P⁆ := by
        have hh : ⁅V₀,pResidual 2 S⁆ ≤ ⁅V₀,P⁆ ⊔ Z₀ := by
          apply (map_le_map_iff_of_injective S.subtype_injective).mp
          rwa [Subgroup.map_sup,map_commutator,map_commutator,hVm,hPm,hZm]
        exact hh.trans (sup_le le_sup_right (hZE.trans le_sup_left))
      have hvgen : V₀ ≤ E ⊔ ⁅V₀,pResidual 2 S⁆ := by
        apply (map_le_map_iff_of_injective S.subtype_injective).mp
        rw [Subgroup.map_sup,map_commutator,hEm,hVm]
        exact (radius_eq_moving_sup_edge h ha hat).le.trans (le_of_eq (sup_comm _ _))
      exact edge_commutator_central_of_residual_cover V₀ P E (pResidual 2 S)
        (comap_mono hVQ) (hEV.trans (comap_mono hVQ))
        ((Q_isPGroup T (edge_two_group h) (core_le_edge h) a ha).comap_subtype).isNilpotent
        (hPT.trans hTE) hE hvgen hcover
  rw [←hVm,←hPm,←map_commutator]
  exact (map_mono hc).trans (map_centralizer_le_centralizer_image (V₀ : Set S) S.subtype)

open Comparison Comparison.CriticalImage
local notation "H" => (L ⊔ R : Subgroup G)
include e

/-- The radius-index bound gives the source residual alternative on the
original V, Q and Z, with the exact endpoint actor and quotient kernel. -/
theorem radius_kernel_residual_dichotomy_at_critical
    (hb : (geometry h).b T = 4)
    (a z : Vertex T) (ha : color T a = false)
    (hc : CriticalPair T a z ((geometry h).exists_critical a ha))
    (c : Vertex T) (hcColor : color T c = false)
    (hac : (cosetGraph T).dist a c = 2) (hcz : (cosetGraph T).dist c z = 2) :
    ⁅⁅V T a,Q T a⁆,Ltilde T a⁆ ≤ Z T a ∨
      ⁅V T a,Ltilde T a⁆ ≤ ⁅V T a,Q T a⁆ ⊔ Z T a := by
  let S := stabilizer T a
  let := finite_stabilizer T a
  let P := (V T a).subgroupOf S
  let X := (Z T a).subgroupOf S
  let A := (Z T z).subgroupOf S
  let B := (Q T c).subgroupOf S
  have hVQ := (geometry h).V_le_Q (by omega) a ha
  have hDS : V T a ≤ S := hVQ.trans (fun _ hx => hx.1)
  let : P.Normal := normal_subgroupOf_of_le_normalizer (V_normalized a)
  let : X.Normal := (geometry h).Z_normal a
  have hz := critical_endpoint_color T a ha _ hc
  have hrev := critical_reverse T (geometry h) (edgeCentralizer h e) a ha (by
    rw [(geometry h).distance_constant a ha]; exact (positive_even h e).1) z hz hc
  have hAS := Z_le_stabilizer_of_dist_le z ((geometry h).exists_critical z hz) hrev.1.le
  let := (geometry h).Z_elementary (by omega) z hz
  have hA : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf hAS
  obtain ⟨d⟩ := endpointModel_knownSimple h e ha
  have hAc : Nat.card (A.map d.actor) = 8 := critical_image_card_eight h e z a hz hrev d
  have hcomm : ⁅P ⊓ B,A⁆ ≤ X := by
    have hi := radius_intersection_seed h e (by omega) a z ha hc c hcColor hcz
    have hh : ⁅(P ⊓ B).map S.subtype,A.map S.subtype⁆ ≤ Z T a :=
      (commutator_mono (by
        rintro x ⟨y,hy,rfl⟩
        exact ⟨hy.1,hy.2⟩) (by rintro x ⟨y,hy,rfl⟩; exact hy)).trans hi
    intro x hx
    exact hh (by rw [←map_commutator]; exact mem_map_of_mem S.subtype hx)
  have hidx : B.relIndex P ≤ 8 := by
    have hh : B.relIndex P = (Q T c).relIndex (V T a) := by
      change ((Q T c).comap S.subtype).relIndex P = _
      rw [relIndex_comap,map_subgroupOf_eq_of_le hDS]
    rw [hh]
    exact radius_index_le_eight h e hb a c ha hcColor hac
  obtain ⟨i,hi,hir,_,_,hiQ⟩ :=
    RankTwo.Sp4Four.SourceComparison.vertex_coordinates_with_kernel T
      (edge_two_group h) (core_le_edge h) ha
  let j : H ≃* S := (MonoidHom.ofInjective hi).trans (MulEquiv.subgroupCongr hir)
  have hj (s : S) : i (j.symm s) = s.val := congrArg Subtype.val (j.apply_symm_apply s)
  let q₀ := QuotientGroup.mk' (pCore 2 H)
  let q := q₀.comp j.symm.toMonoidHom
  have hq : Function.Surjective q := (QuotientGroup.mk'_surjective _).comp j.symm.surjective
  have hqk : q.ker = (pCore 2 H).comap j.symm.toMonoidHom := by
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
  have hp : IsPGroup 2 q.ker := by
    rw [hqk]
    exact pCore_isPGroup.comap_of_injective j.symm.toMonoidHom j.symm.injective
  have hqQ : q.ker.map S.subtype = Q T a := by
    rw [hqk,←hiQ]
    apply le_antisymm
    · rintro _ ⟨s,hs,rfl⟩
      exact ⟨j.symm s,hs,hj s⟩
    · rintro _ ⟨s,hs,rfl⟩
      refine ⟨j s,?_,rfl⟩
      change j.symm (j s) ∈ pCore 2 H
      rwa [j.symm_apply_apply]
  have hk : q.ker = d.actor.ker :=
    (map_injective S.subtype_injective) (hqQ.trans d.actor_kernel.symm)
  have hcA : Nat.card (A.map q) = 8 := by
    rw [←relIndex_ker,hk,relIndex_ker]
    exact hAc
  let C := quotientComponent (L := L) (R := R)
  let := (quotientComponent_structure h e).1
  let := (quotientComponent_structure h e).2.1
  let := (quotientComponent_structure h e).2.2.1
  have hres : (pResidual 2 S).map q = C := by
    change (pResidual 2 S).map (q₀.comp j.symm.toMonoidHom) = C
    rw [←map_map,map_pResidual_of_surjective 2 j.symm.toMonoidHom j.symm.surjective,
      relative_residual h]
    rfl
  have hPk : P ≤ q.ker := by
    intro x hx
    have hh := hVQ hx
    rw [←hqQ] at hh
    obtain ⟨y,hy,hyx⟩ := hh
    exact (Subtype.ext hyx : y = x) ▸ hy
  have hXP : X ≤ P := comap_mono (Z_le_VBall T a 2)
  have hbudget : (centralizerModulo P A X).relIndex P ≤ 8 :=
    (SymmetricSixBudget.centralizerModulo_relIndex_le_of_commutator P A X B hcomm).trans hidx
  have hout := projected_g2_residual_dichotomy_modulo q hq hp C hres
    (quotientComponent_card h e) (quotientComponent_structure h e).2.2.2
    (quotientComponent_sqtk h) P X hXP hPk A hA hcA hbudget
    ⁅P,q.ker⁆ (commutator_le_left P _)
  rcases hout with hout | hout
  · left
    have hm := map_mono (f := S.subtype) hout
    rw [map_commutator,map_commutator,map_subgroupOf_eq_of_le hDS,hqQ,
      map_subgroupOf_eq_of_le (Z_le_stabilizer T a)] at hm
    exact hm
  · right
    have hm := map_mono (f := S.subtype) hout
    rw [Subgroup.map_sup,map_commutator,map_commutator,map_subgroupOf_eq_of_le hDS,hqQ,
      map_subgroupOf_eq_of_le (Z_le_stabilizer T a)] at hm
    exact hm

/-- The whole vertex kernel acts centrally on the radius. -/
theorem radius_kernel_commutator_centralizes_radius
    (hb : (geometry h).b T = 4) (a : Vertex T) (ha : color T a = false) :
    ⁅V T a,Q T a⁆ ≤ centralizer (V T a : Set (FreeAmalgam T)) := by
  obtain ⟨z,hcrit⟩ := criticalPair_exists T a ((geometry h).exists_critical a ha)
  have hd : (cosetGraph T).dist a z = 4 :=
    hcrit.1.trans (((geometry h).distance_constant a ha).trans hb)
  obtain ⟨t,hat,htz⟩ := exists_adjacent_dist_sub_one T a z (by omega)
  obtain ⟨c,htc,hcz⟩ := exists_adjacent_dist_sub_one T t z (by omega)
  have hcColor : color T c = false := by
    have ht := adjacent_color_ne T hat
    have hc := adjacent_color_ne T htc
    rw [ha] at ht
    cases hc' : color T c <;> cases ht' : color T t <;> simp_all
  have hat1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj T _ _).mpr hat)
  have htc1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj T _ _).mpr htc)
  have h₁ := (cosetGraph_connected T).dist_triangle (u := a) (v := t) (w := c)
  have h₂ := (cosetGraph_connected T).dist_triangle (u := a) (v := c) (w := z)
  exact radius_kernel_commutator_central_of_dichotomy h (by omega) a t ha hat
    (radius_kernel_residual_dichotomy_at_critical h e hb a z ha hcrit c hcColor (by omega) (by omega))

/-- The derived radius lies in the elementary center of its whole kernel,
which is stronger than centrality in the radius itself. -/
theorem radius_derived_le_omegaCenter
    (hb : (geometry h).b T = 4) (a : Vertex T) (ha : color T a = false) :
    ⁅V T a,V T a⁆ ≤ X T a :=
  SectionFive.radius_derived_le_X T (geometry h) (by omega) ha
    (radius_kernel_commutator_centralizes_radius h e hb a ha)

/-- The entire critical commutator lies in the midpoint's elementary
kernel center; all three vertices and the original groups are retained. -/
theorem critical_commutator_le_midpoint_omegaCenter
    (hb : (geometry h).b T = 4)
    (a z c : Vertex T) (hcColor : color T c = false)
    (hac : (cosetGraph T).dist a c = 2) (hcz : (cosetGraph T).dist c z = 2) :
    ⁅Z T a,Z T z⁆ ≤ X T c := by
  have haV : Z T a ≤ V T c := le_iSup_of_le a (le_iSup_of_le hac.le le_rfl)
  have hzV : Z T z ≤ V T c := le_iSup_of_le z (le_iSup_of_le
    (by rw [SimpleGraph.dist_comm,hcz]) le_rfl)
  exact (commutator_mono haV hzV).trans (radius_derived_le_omegaCenter h e hb c hcColor)

/-- The triple is contained in the starting moving seed and in the
midpoint elementary center. The latter is not the midpoint fixed core. -/
theorem critical_triple_le_moving_inf_midpoint_omegaCenter
    (hb : (geometry h).b T = 4)
    (a z : Vertex T) (ha : color T a = false)
    (hc : CriticalPair T a z ((geometry h).exists_critical a ha))
    (t c : Vertex T) (hcColor : color T c = false)
    (hat : Adjacent T a t) (hct : Adjacent T c t)
    (hac : (cosetGraph T).dist a c = 2) (hcz : (cosetGraph T).dist c z = 2) :
    ⁅⁅Z T a,Z T z⁆,Q T t⁆ ≤ U T a ⊓ X T c := by
  refine le_inf (critical_triple_le_start_moving h a z ha hc t hat) ?_
  exact (critical_triple_control h e hb a z ha hc t c hcColor hat hct hac hcz).1.trans
    (critical_commutator_le_midpoint_omegaCenter h e hb a z c hcColor hac hcz)

/-- The source triple commutator centralizes the entire midpoint kernel. -/
theorem critical_triple_centralizes_midpoint_kernel
    (hb : (geometry h).b T = 4)
    (a z : Vertex T) (ha : color T a = false)
    (hc : CriticalPair T a z ((geometry h).exists_critical a ha))
    (t c : Vertex T) (hcColor : color T c = false)
    (hat : Adjacent T a t) (hct : Adjacent T c t)
    (hac : (cosetGraph T).dist a c = 2) (hcz : (cosetGraph T).dist c z = 2) :
    ⁅⁅Z T a,Z T z⁆,Q T t⁆ ≤ centralizer (Q T c : Set (FreeAmalgam T)) := by
  exact ((critical_triple_le_moving_inf_midpoint_omegaCenter h e hb a z ha hc
    t c hcColor hat hct hac hcz).trans inf_le_right).trans
      (le_centralizer_iff.mp (Q_le_centralizer_X T c))


end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.G2Reconstruction.DistanceTwo.DistanceFour
