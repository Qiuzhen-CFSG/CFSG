module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerElementary.Coordinates
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerCentralizer
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerPlane
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionLocalTable

/-!
# The literal plane core in the exceptional Sylow coordinates

The source commutator [Q₂,⟨f⟩]=⟨t⟩ fixes the marked short involution.
The fixed translations together with f form a normal two-subgroup of E₂,
and its coordinate order sixteen identifies it with A₂. Its mixed wreath
coordinates then identify N_T(A₂) with C_T(t).

Source: Aschbacher–Smith F.5.4(4), printed p.301.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
open BinaryPermutation.AlternatingFiveExtension
open SylowModel SylowCommutator ElementaryCoordinates
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)
  (t : G) (hf : FusionFacts c i z t)
local notation "T" => Source.sylowImage c i
include h hf in
theorem fusion_t_eq_marked_short : t = sourceMarkedShort c i := by
  classical
  have ht : t∈zpowers (sourceMarkedShort c i) := by
    rw [←source_short_commutator c i h.embedding_injective,hf.t_commutator]
    exact mem_zpowers t
  rw [mem_zpowers_iff_mem_range_orderOf,source_short_order c i h.embedding_injective] at ht
  obtain ⟨n,hnum,he⟩ := Finset.mem_image.mp ht
  have hn2 := Finset.mem_range.mp hnum
  interval_cases n
  · simp only [pow_zero] at he
    have ho := hf.t_order
    rw [←he,orderOf_one] at ho
    omega
  · simpa only [pow_one] using he.symm

include h hf in
theorem plane_graph_core_le_A :
    (Q c i true ⊓ C c i) ⊔ zpowers (Source.graphElement c i) ≤ A c i true := by
  apply sup_le
  · have hp : IsPGroup 2 (Q c i true) :=
      (source_Q_plane_elementary c i).isPGroup
    apply le_pCoreIn_of_normalizes (hp.to_le inf_le_left)
    · exact inf_le_inf ((source_Q_plane_le_sylowImage c i).trans (sylowImage_le_M c i true)) le_rfl
    · apply le_trans (le_inf ?_ (inf_le_right.trans (C c i).le_normalizer))
        inf_normalizer_le_normalizer_inf
      rw [normalizer_Q_eq_plane c i z h]
      exact inf_le_left
  · exact zpowers_le.mpr (graph_mem_A c i z t hf true)

private def fT : T := ⟨Source.graphElement c i,source_graph_mem_sylowImage c i⟩
private def tT : T := ⟨t,hf.t_mem⟩

omit [Finite G] in
private theorem mapped_graph_centralizer (e : T ≃* PlaneWreath) :
    (centralizer ({fT c i} : Set T)).map e.toMonoidHom =
      centralizer ({e (fT c i)} : Set PlaneWreath) := by
  ext x
  constructor
  · rintro ⟨a,ha,rfl⟩
    change a∈centralizer ({fT c i} : Set T) at ha
    rw [mem_centralizer_singleton_iff] at ha ⊢
    change e a * e (fT c i) = e (fT c i) * e a
    simpa only [map_mul] using congrArg e ha
  · intro hx
    refine ⟨e.symm x,?_,e.apply_symm_apply x⟩
    change e.symm x∈centralizer ({fT c i} : Set T)
    rw [mem_centralizer_singleton_iff] at hx ⊢
    apply e.injective
    simpa only [map_mul,e.apply_symm_apply] using hx

include h hf in
/-- The actual plane two-core is one of the two mixed elementary subgroups;
the same coordinates send the literal short involution to its axis. -/
theorem exists_plane_A_coordinates :
    ∃ (e : T ≃* PlaneWreath) (j : Bit),
      ((Q c i true).subgroupOf T).map e.toMonoidHom = baseMap.range ∧
      e ⟨t,hf.t_mem⟩ = baseMap (axis j) ∧
      ((A c i true).subgroupOf T).map e.toMonoidHom = mixed j := by
  obtain ⟨e,he⟩ := exists_source_marked_sylow_equiv c i h.embedding_injective
  have htQ : t∈Q c i true := (fusion_t_eq_marked_short c i z h t hf) ▸ source_short_mem_Q c i
  have hcomm : ⁅(Q c i true).subgroupOf T,zpowers (fT c i)⁆ = zpowers (tT c i z t hf) := by
    apply map_injective (T).subtype_injective
    rw [map_commutator,subgroupOf_map_subtype,
      inf_eq_left.mpr (source_Q_plane_le_sylowImage c i),MonoidHom.map_zpowers,MonoidHom.map_zpowers]
    exact hf.t_commutator
  have hcomm' := congrArg (fun U : Subgroup T => U.map e.toMonoidHom) hcomm
  rw [map_commutator,he,MonoidHom.map_zpowers,MonoidHom.map_zpowers] at hcomm'
  obtain ⟨u,hu⟩ : e (tT c i z t hf) ∈ baseMap.range := by
    rw [←he]
    exact mem_map_of_mem _ htQ
  have huo : orderOf (baseMap u) = 2 := by
    rw [hu,e.orderOf_eq]
    exact (orderOf_injective (T).subtype (T).subtype_injective (tT c i z t hf)).symm.trans hf.t_order
  change ⁅baseMap.range,zpowers (e (fT c i))⁆ = zpowers (e (tT c i z t hf)) at hcomm'
  rw [←hu] at hcomm'
  have hfo : (e (fT c i))^2=1 := by
    have ho : orderOf (e (fT c i))=2 := by
      rw [e.orderOf_eq]
      exact (orderOf_injective (T).subtype (T).subtype_injective (fT c i)).symm.trans
        (source_graph_order c i h.embedding_injective)
    simpa only [ho] using pow_orderOf_eq_one (e (fT c i))
  obtain ⟨j,huj,hcore⟩ := graph_core_coordinates _ u hfo huo hcomm'
  refine ⟨e,j,he,hu.symm.trans huj,?_⟩
  have hAT : A c i true ≤ T := by
    exact (A_le_TfImage c i z t hf true).trans ((TfImage_eq c i) ▸ inf_le_left)
  have hle : mixed j ≤ ((A c i true).subgroupOf T).map e.toMonoidHom := by
    rw [←hcore,←he,←mapped_graph_centralizer c i e,←map_inf _ _ _ e.injective]
    change _ ⊔ zpowers (e.toMonoidHom (fT c i)) ≤ _
    rw [←MonoidHom.map_zpowers,←Subgroup.map_sup]
    apply map_mono
    apply sup_le
    · intro a ha
      apply plane_graph_core_le_A c i z h t hf
      apply le_sup_left (a := Q c i true ⊓ C c i) (b := zpowers (Source.graphElement c i))
      exact ⟨ha.1,
        mem_centralizer_singleton_iff.mpr (congrArg Subtype.val (mem_centralizer_singleton_iff.mp ha.2))⟩
    · apply zpowers_le.mpr
      exact graph_mem_A c i z t hf true
  apply (eq_of_le_of_card_ge hle ?_).symm
  rw [card_map_of_injective e.injective,Nat.card_congr (subgroupOfEquivOfLe hAT).toEquiv,
    hf.A_card,card_mixed]

include h hf in
/-- Inside the original Sylow subgroup the plane core is normalized exactly
by the centralizer of the literal short involution. -/
theorem normalizer_plane_A_in_T :
    T ⊓ normalizer (A c i true : Set G) = Tcentralizer c i t := by
  obtain ⟨e,j,hQ,ht,hA⟩ := exists_plane_A_coordinates c i z h t hf
  have hAT : A c i true ≤ T :=
    (A_le_TfImage c i z t hf true).trans ((TfImage_eq c i) ▸ inf_le_left)
  have hN : (normalizer ((A c i true).subgroupOf T : Set T)).map e.toMonoidHom =
      centralizer ({e ⟨t,hf.t_mem⟩} : Set PlaneWreath) := by
    rw [map_normalizer_eq_of_bijective _ e.bijective,hA,normalizer_mixed,ht]
  ext x
  constructor
  · rintro ⟨hxT,hxN⟩
    refine ⟨hxT,?_⟩
    have hxN' : (⟨x,hxT⟩ : T)∈normalizer ((A c i true).subgroupOf T : Set T) := by
      rw [←subgroupOf_normalizer_eq hAT]
      exact hxN
    have hx := mem_map_of_mem e.toMonoidHom hxN'
    rw [hN] at hx
    have hh := mem_centralizer_singleton_iff.mp hx
    change e ⟨x,hxT⟩ * e ⟨t,hf.t_mem⟩ = e ⟨t,hf.t_mem⟩ * e ⟨x,hxT⟩ at hh
    have hh' : (⟨x,hxT⟩ : T)*⟨t,hf.t_mem⟩=⟨t,hf.t_mem⟩*⟨x,hxT⟩ := by
      apply e.injective
      simpa only [map_mul] using hh
    exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hh')
  · rintro ⟨hxT,hxt⟩
    refine ⟨hxT,?_⟩
    have hh : e (⟨x,hxT⟩ : T)∈centralizer ({e ⟨t,hf.t_mem⟩} : Set PlaneWreath) := by
      apply mem_centralizer_singleton_iff.mpr
      have hsub : (⟨x,hxT⟩ : T)*⟨t,hf.t_mem⟩=⟨t,hf.t_mem⟩*⟨x,hxT⟩ :=
        Subtype.ext (mem_centralizer_singleton_iff.mp hxt)
      simpa only [map_mul] using congrArg e hsub
    rw [←hN] at hh
    have hxN' := (mem_map_iff_mem e.injective).mp hh
    rw [←subgroupOf_normalizer_eq hAT] at hxN'
    exact hxN'

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
