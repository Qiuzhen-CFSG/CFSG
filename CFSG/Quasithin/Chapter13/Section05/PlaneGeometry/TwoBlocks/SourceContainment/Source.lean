module
public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks.SourceContainment.Action
public import Theory.GroupTheory.PCoreActionSplitting

/-!
# Source consequences for the plane actor

The transported action identifies the actor's intrinsic two-core with its
V₂-centralizing part and proves the nonabelian O₂ conclusion via the existing
source plane-core theorem. Unique maximal two-local control also gives the
ambient N(V) and C(V) containments.
Source: Aschbacher--Smith13.5.4 and13.5.6, printed pp.916–917.
-/
@[expose] public section
open Subgroup BinaryPermutation
namespace CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks
open Section08.SourceCompletion Section07.NaturalAction AmbientSource
variable {G:Type*} [Group G] [Finite G] {T:Sylow 2 G}
  {L V V₁ V₂ V₃ M G₁:Subgroup G}
  (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

theorem planeActor_action_source (hb:ChapterC.IsAlternatingBlock L 6) :
    (letI := source_plane_isKleinFour d;
      Nat.card (((planeActor (L:=L) (V₂:=V₂)).subgroupOf (normalizer (V₂:Set G))).map
        (planeAction V₂))=3) ∧
    IsPGroup 2 (planeActor (L:=L) (V₂:=V₂) ⊓ centralizer (V₂:Set G):Subgroup G) := by
  let := source_plane_isKleinFour d
  let P:=planeLocal (L:=L) (V₂:=V₂)
  let X:=planeActor (L:=L) (V₂:=V₂)
  let N:=normalizer (V₂:Set G)
  let r:P→*Equiv.Perm (Fin 3):=(planeAction V₂).comp (inclusion (show P≤N from inf_le_right))
  obtain ⟨q,hq,hk,hfix⟩:=exists_planeLocal_quotient d hb
  have heker:r.ker=q.ker:=by
    ext g
    exact (planeAction_eq_one V₂ (inclusion (show P≤N from inf_le_right) g)).trans (hfix g).symm
  have hr:Function.Surjective r:=by
    apply MonoidHom.range_eq_top.mp
    apply r.range.eq_top_of_card_eq
    rw [←index_ker,heker,index_ker,MonoidHom.range_eq_top.mpr hq,card_top]
  have hmap:(X.subgroupOf N).map (planeAction V₂)=(pResidual 2 P).map r:=by
    ext g
    constructor
    · rintro ⟨x,hx,rfl⟩
      obtain ⟨p,hp,he⟩:=hx
      refine ⟨p,hp,?_⟩
      exact congrArg (planeAction V₂) (Subtype.ext he)
    · rintro ⟨p,hp,rfl⟩
      exact ⟨inclusion (show P≤N from inf_le_right) p,⟨p,hp,rfl⟩,rfl⟩
  constructor
  · change Nat.card ((X.subgroupOf N).map (planeAction V₂))=3
    rw [hmap,map_pResidual_of_surjective 2 r hr,Equiv.Perm.twoResidual_eq_alternating,
      nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  · have hkimage:q.ker.map P.subtype=P⊓centralizer (V₂:Set G):=by
      ext g
      constructor
      · rintro ⟨p,hp,rfl⟩
        exact ⟨p.property,(hfix p).mp hp⟩
      · intro hg
        exact ⟨⟨g,hg.1⟩,(hfix _).mpr hg.2,rfl⟩
    apply ((hk.map P.subtype).of_equiv (MulEquiv.subgroupCongr hkimage)).to_le
    exact inf_le_inf_right _ planeActor_le

/-- The plane kernel is the intrinsic two-core, and the quotient is cubic. -/
theorem planeActor_core_source (hb:ChapterC.IsAlternatingBlock L 6) :
    (planeActor (L:=L) (V₂:=V₂)).pCoreIn 2=
      planeActor (L:=L) (V₂:=V₂)⊓centralizer (V₂:Set G) ∧
      Nat.card (planeActor (L:=L) (V₂:=V₂) ⧸ pCore 2 (planeActor (L:=L) (V₂:=V₂)))=3 := by
  let := source_plane_isKleinFour d
  let X:=planeActor (L:=L) (V₂:=V₂)
  have hn:X≤normalizer (V₂:Set G):=planeActor_le.trans inf_le_right
  let f:X→*Equiv.Perm (Fin 3):=(planeAction V₂).comp (inclusion hn)
  obtain ⟨hc,hk⟩:=planeActor_action_source d hb
  have hf:f.range=(X.subgroupOf (normalizer (V₂:Set G))).map (planeAction V₂):=by
    ext g
    constructor
    · rintro ⟨x,rfl⟩; exact ⟨inclusion hn x,x.property,rfl⟩
    · rintro ⟨x,hx,rfl⟩; exact ⟨⟨x,hx⟩,rfl⟩
  have hc':Nat.card f.range=3:=by rw [hf]; exact hc
  have hker:f.ker=(centralizer (V₂:Set G)).subgroupOf X:=by
    ext x
    exact planeAction_eq_one V₂ (inclusion hn x)
  have hkp:IsPGroup 2 f.ker:=by
    apply hk.comap_subtype.to_le
    intro x hx
    have hc:x∈(centralizer (V₂:Set G)).subgroupOf X:=hker ▸ hx
    exact ⟨x.property,hc⟩
  have hcore:pCore 2 f.range=⊥:=by
    apply card_eq_one.mp
    rcases (pCore_isPGroup (p:=2) (G:=f.range)).card_eq_or_dvd with hh|hh
    · exact hh
    · have hd:=hh.trans (card_subgroup_dvd_card (pCore 2 f.range))
      rw [hc'] at hd
      norm_num at hd
  have he:=f.ker_eq_pCore_of_range_core_eq_bot 2 hkp hcore
  constructor
  · change (pCore 2 X).map X.subtype=_
    rw [←he,hker,subgroupOf_map_subtype,inf_comm]
  · change Nat.card (X⧸pCore 2 X)=3
    rw [←he,Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv,hc']

/-- The literal original residual, without a separate plane actor,
cubic-image, kernel or module-generation premise. -/
theorem source_planeActor_nonabelian_core (hb:ChapterC.IsAlternatingBlock L 6) :
    ⁅V,planeActor (L:=L) (V₂:=V₂)⁆=V ∧
      V≤(planeActor (L:=L) (V₂:=V₂)).pCoreIn 2 ∧
      ¬IsMulCommutative (pCore 2 (planeActor (L:=L) (V₂:=V₂))) := by
  obtain ⟨hx,hk⟩:=planeActor_action_source d hb
  have hXL:planeActor (L:=L) (V₂:=V₂)≤L:=planeActor_le.trans inf_le_left
  have hXN:planeActor (L:=L) (V₂:=V₂)≤normalizer (V₂:Set G):=planeActor_le.trans inf_le_right
  have hh:=source_plane_residual_core_nonabelian d _ hXL hXN (planeActor_normalized d)
    planeActor_twoPerfect hx hk
  exact ⟨hh.1,hh.2.1,source_plane_intrinsic_core_nonabelian d _ hXL hXN
    (planeActor_normalized d) planeActor_twoPerfect hx hk⟩

/-- The original noncentrality theorem13.3.14 now suffices to normalize
this same residual by the full ambient plane normalizer. -/
theorem source_planeActor_normalized
    (hb:ChapterC.IsAlternatingBlock L 6)
    (hm:⁅(normalizer (V₁:Set G)).pCoreIn 2,V₂⁆≠⊥) :
    normalizer (V₂:Set G)≤normalizer (planeActor (L:=L) (V₂:=V₂):Set G) := by
  let := source_plane_isKleinFour d
  obtain ⟨hx,hk⟩:=planeActor_action_source d hb
  exact (plane_normalClosure T V₁ V₂ (planeActor (L:=L) (V₂:=V₂)) d.line_card d.line_le_plane
    d.line_stable d.plane_stable (planeActor_le.trans inf_le_right)
    (planeActor_normalized d) planeActor_twoPerfect hx hk hm).2.1

/-- Uniqueness already controls the full normalizer of the original V. -/
theorem source_module_normalizer_le
    (hu:∀N:Subgroup G,IsMaximalTwoLocal N→L⊔(T:Subgroup G)≤N→N=M) :
    normalizer (V:Set G)≤M := by
  let := elementary d
  apply normalizer_le_of_unique_maximalTwoLocal hu (IsElementaryAbelian.isPGroup 2 V)
  · intro hV
    have hP:V₁=⊥:=bot_unique ((d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)).trans hV.le)
    have hc:=d.line_card
    rw [hP,card_bot] at hc
    contradiction
  · exact d.normalizes_V

theorem source_module_centralizer_le
    (hu:∀N:Subgroup G,IsMaximalTwoLocal N→L⊔(T:Subgroup G)≤N→N=M) :
    centralizer (V:Set G)≤M :=
  (Subgroup.centralizer_le_normalizer _).trans (source_module_normalizer_le d hu)

end CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks
