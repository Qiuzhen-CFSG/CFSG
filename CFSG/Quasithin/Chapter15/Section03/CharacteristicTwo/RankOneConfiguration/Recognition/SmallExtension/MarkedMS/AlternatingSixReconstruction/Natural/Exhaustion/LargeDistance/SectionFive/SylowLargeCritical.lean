module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowFixedLine
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.Inputs

/-!
# First-edge noncentrality of large critical commutators

For a critical pair with image order at least four, the reverse image is
also large. Its actual first-edge kernel is a two-group. SylowFixedLine gives
a noncentral element of the full moved-cover commutator fixed by that whole
kernel. The literal amalgam embedding puts this element in the first-edge
omega-center seed and in the original critical commutator.

Two successive generating edges would carry that same seed intersection
back to the critical start and make it central there. Hence a large critical
image is impossible in this precise two-generator configuration. No full
point-core equality, elementary radical image, or original Sylow premise is
needed for this local estimate. Both central covers are retained.

SylowShiftChain applies the result to actual successive shifts on the
minimum characteristic replacement, supplying the small R4/R6 critical images
used in the source iteration. This is not the terminal distance exclusion.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3), (5.10)--(5.11), printed pp.866--867,922--924, in particular
the first-edge intersection and small critical-image reduction on p.922.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open scoped commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
namespace SylowLargeCritical
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  {h : SmallMSPair κ L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)


open scoped IsMulCommutative in
/-- A large image inside any two-subgroup gives a noncentral full-cover
commutator fixed by that two-subgroup, in the literal marking. -/
theorem large_two_image_fixed_commutator
    (A T : Subgroup d.overgroup) (hAT : A ≤ T)
    (hT : IsPGroup 2 (T.map s.projection))
    (hcard : 4 ≤ Nat.card (A.map s.projection)) :
    ¬ ⁅replacementMoved d,A⁆ ⊓ centralizer (T : Set d.overgroup) ≤ center d.overgroup := by
  obtain ⟨a,ha,v,hfix,hnon⟩ := SylowFixedLine.cover_model_two_group_fixed_displacement
    (coverAction s) (cover_model s) (A.map s.projection) (T.map s.projection)
    (map_mono hAT) hT hcard
  obtain ⟨a,ha,rfl⟩ := ha
  let r := coverAction s (s.projection a) v-v
  have hr : (r.toMul : d.overgroup) = a*v.toMul*a⁻¹*(v.toMul : d.overgroup)⁻¹ := by
    dsimp only [r]
    rw [toMul_sub,Subgroup.coe_div,div_eq_mul_inv,coverAction_conjugate]
  have hrA : (r.toMul : d.overgroup) ∈ ⁅replacementMoved d,A⁆ := by
    rw [hr,commutator_comm]
    exact commutator_mem_commutator ha v.toMul.property
  have hrT : (r.toMul : d.overgroup) ∈ centralizer (T : Set d.overgroup) := by
    intro t ht
    have hh := congrArg (fun z : Additive (replacementMoved d) => (z.toMul : d.overgroup))
      (hfix (s.projection t) (mem_map_of_mem _ ht))
    rw [coverAction_conjugate] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  intro hcentral
  have hc := hcentral ⟨hrA,hrT⟩
  apply hnon
  intro g
  obtain ⟨t,rfl⟩ := s.surjective g
  change (coverAction s (s.projection t) r).toMul = r.toMul
  apply Subtype.ext
  rw [coverAction_conjugate]
  rw [(mem_center_iff.mp hc t),mul_inv_cancel_right]

include s in
private theorem large_critical_first_seed_noncentral_base
    (hc : DistanceTwo.CentralLayer d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) :
    ¬ ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ ⊓ Z d.radical (p.walk.getVert 1) ≤
      centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) := by
  have hp := replacementDistance_pos h d
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  let t := p.walk.getVert 1
  have hat : Adjacent d.radical (alpha d.radical) t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    change false ≠ color d.radical t at hh
    cases he : color d.radical t <;> simp_all
  have hAt : Z d.radical a' ≤ Q d.radical t := by
    apply Z_le_Q_of_dist_lt d.radical a' ((replacementGeometry h d).exists_critical a' p.end_color)
    rw [SimpleGraph.dist_comm,p.dist_end,(replacementGeometry h d).distance_constant _ p.end_color]
    change p.walk.length-1 < replacementDistance h d
    omega
  have htG : Q d.radical t ≤ stabilizer d.radical (alpha d.radical) :=
    fun _ hx => hx.2 _ (adjacent_symm d.radical hat)
  let A := (Z d.radical a').comap (embedM d.radical)
  let T := (Q d.radical t).comap (embedM d.radical)
  have hmA : A.map (embedM d.radical) = Z d.radical a' :=
    map_comap_eq_self ((hAt.trans htG).trans_eq (stabilizer_m_base d.radical))
  have hmT : T.map (embedM d.radical) = Q d.radical t :=
    map_comap_eq_self (htG.trans_eq (stabilizer_m_base d.radical))
  have hcard : 4 ≤ Nat.card (A.map s.projection) := by
    change 4 ≤ Nat.card (graphImage s (Z d.radical a'))
    rw [graphImage_card s _ (hAt.trans htG)]
    exact reverse_critical_image_four_le s hc hp p hlarge
  have hQt : IsPGroup 2 (Q d.radical t) := by
    obtain ⟨g,hg | hg⟩ := (adjacent_iff_exists_common d.radical _ _).mp hat
    · rw [hg.2]
      have hh := Q_act d.radical g (beta d.radical)
      simp only [beta,act_hVertex,one_mul] at hh
      rw [hh]
      change IsPGroup 2 ((Q d.radical (beta d.radical)).map _)
      rw [Q_beta]
      exact ((replacement_radical_isPGroup h d).map _).map _
    · have hh : color d.radical (alpha d.radical) = true := by rw [hg.1]; rfl
      cases hh
  have hT : IsPGroup 2 (T.map s.projection) :=
    (hQt.comap_of_injective (embedM d.radical) (embedM_injective d.radical)).map s.projection
  have hn := large_two_image_fixed_commutator s A T (comap_mono hAt) hT hcard
  intro hcentral
  apply hn
  rintro x ⟨hx,hxT⟩
  have hxD : embedM d.radical x ∈ ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ := by
    have hh := mem_map_of_mem (embedM d.radical) hx
    rw [map_commutator,hmA,←hc.U_eq_moved] at hh
    exact commutator_mono (DistanceEight.U_le_Z d.radical _) le_rfl hh
  have hxZ : embedM d.radical x ∈ Z d.radical (alpha d.radical) :=
    (((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans
      (DistanceEight.U_le_Z d.radical _)) hxD
  have hxQ : embedM d.radical x ∈ Q d.radical t := by
    apply Q_le_adjacent_h d.radical ht hat
    apply Z_le_Q_of_dist_lt d.radical _ ((replacementGeometry h d).exists_critical _ rfl) _ hxZ
    rw [SimpleGraph.dist_self,(replacementGeometry h d).distance_constant _ rfl]
    exact hp
  have hxC : embedM d.radical x ∈ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    rw [←hmT]
    exact map_centralizer_le_centralizer_image (T : Set d.overgroup) (embedM d.radical)
      (mem_map_of_mem _ hxT)
  have hxseed : embedM d.radical x ∈ Z d.radical t := by
    rw [Z,if_neg (by simp [ht])]
    let := (replacementGeometry h d).Z_elementary hp (alpha d.radical) rfl
    exact mem_omegaCenter_iff.mpr ⟨hxQ,elemPow_eq_one_of_isElementaryAbelian _ hxZ,hxC⟩
  apply mem_center_iff.mpr
  intro m
  apply embedM_injective d.radical
  simp only [map_mul]
  apply hcentral ⟨hxD,hxseed⟩
  change embedM d.radical m ∈ stabilizer d.radical (mVertex d.radical 1)
  rw [stabilizer_m_base]
  exact ⟨m,rfl⟩


include s in
/-- A large critical image meets its first edge seed noncentrally, for either
cover and every radical image. -/
theorem large_critical_first_seed_noncentral
    (hc : DistanceTwo.CentralLayer d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) :
    ¬ ⁅Z d.radical a,Z d.radical a'⁆ ⊓ Z d.radical (p.walk.getVert 1) ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have base := large_critical_first_seed_noncentral_base s hc
    (a' := act d.radical g⁻¹ a')
  rw [←hbase] at base
  intro hcentral
  have hlarge₀ : 4 ≤ (Q d.radical (act d.radical g⁻¹ a')).relIndex
      (Z d.radical (act d.radical g⁻¹ a)) := by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hlarge
  apply base (p.act g⁻¹) hlarge₀
  have hh := (map_mono (f := (MulAut.conj g).toMonoidHom) hcentral).trans
    (map_centralizer_le_centralizer_image _ _)
  rw [map_inf _ _ _ (MulAut.conj g).injective,map_commutator] at hh
  simpa only [CriticalPath.act,actWalk_getVert,Z_act,stabilizer_act,inv_inv,Subgroup.coe_map] using hh

private theorem terminal_central_fixed_map {F : Type*} [Group F] (H K : Subgroup F)
    (hHK : H ≤ centralizer (K : Set F)) {x : F} (hx : x ∈ K) :
    H.map (MulAut.conj x).toMonoidHom = H :=
  mem_normalizer_iff_map_conj_eq.mp
    (Subgroup.centralizer_le_normalizer _ (le_centralizer_iff.mp hHK hx))

include s in
/-- The same two generating edges and component transporter exclude the
critical configuration for both cover orders. -/
theorem large_critical_three_shift_generators_false (hc : DistanceTwo.CentralLayer d)
    {a e : Vertex d.radical} (p : CriticalPath d.radical (replacementGeometry h d) a e)
    (hlarge : 4 ≤ (Q d.radical e).relIndex (Z d.radical a))
    (c v z f g : Vertex d.radical)
    (hct : Adjacent d.radical c (p.walk.getVert 1)) (hcv : Adjacent d.radical c v)
    (hgenC : Q d.radical (p.walk.getVert 1)⊔Z d.radical f=stabilizer d.radical c)
    (hgenD : Q d.radical v⊔Z d.radical g=stabilizer d.radical z)
    (hRf : ⁅Z d.radical a,Z d.radical e⁆≤centralizer (Z d.radical f:Set (FreeAmalgam d.radical)))
    (hRg : ⁅Z d.radical a,Z d.radical e⁆≤centralizer (Z d.radical g:Set (FreeAmalgam d.radical)))
    (x : FreeAmalgam d.radical) (hx : x∈stabilizer d.radical c) (hxa : act d.radical x z=a) : False := by
  let H := ⁅Z d.radical a,Z d.radical e⁆⊓Z d.radical (p.walk.getVert 1)
  have hnon := large_critical_first_seed_noncentral s hc p hlarge
  have ht : color d.radical (p.walk.getVert 1)=true := by
    have hcol := p.vertex_color (show 1≤p.walk.length by
      have hh : 0<p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
      omega)
    have hf : ¬color d.radical (p.walk.getVert 1)=false := by
      intro hh
      have he := hcol.mp hh
      norm_num at he
    cases he : color d.radical (p.walk.getVert 1) <;> simp_all
  have hseed (w : Vertex d.radical) (hw : color d.radical w=true) :
      Z d.radical w≤centralizer (Q d.radical w:Set (FreeAmalgam d.radical)) := by
    intro z hz
    rw [Z,if_neg (by simp [hw])] at hz
    exact (mem_omegaCenter_iff.mp hz).2.2
  have hHC : H≤centralizer (stabilizer d.radical c:Set (FreeAmalgam d.radical)) := by
    apply le_centralizer_iff.mp
    rw [←hgenC]
    exact sup_le (le_centralizer_iff.mp (inf_le_right.trans (hseed _ ht)))
      (le_centralizer_iff.mp (inf_le_left.trans hRf))
  have hHv : H≤Z d.radical v := by
    obtain ⟨y,hy,hyt⟩ := stabilizer_transitive_neighbors d.radical c hct hcv
    rw [←hyt,Z_act]
    rw [←terminal_central_fixed_map H (stabilizer d.radical c) hHC ((stabilizer d.radical c).inv_mem hy)]
    exact map_mono inf_le_right
  have hc0 : color d.radical c=false := by
    have hh := adjacent_color_ne d.radical hct
    rw [ht] at hh
    cases he : color d.radical c <;> simp_all
  have hv : color d.radical v=true := by
    have hh := adjacent_color_ne d.radical hcv
    rw [hc0] at hh
    cases he : color d.radical v <;> simp_all
  have hHD : H≤centralizer (stabilizer d.radical z:Set (FreeAmalgam d.radical)) := by
    apply le_centralizer_iff.mp
    rw [←hgenD]
    exact sup_le (le_centralizer_iff.mp (hHv.trans (hseed _ hv)))
      (le_centralizer_iff.mp (inf_le_left.trans hRg))
  have hHA : H≤centralizer (stabilizer d.radical a:Set (FreeAmalgam d.radical)) := by
    rw [←hxa,stabilizer_act]
    have hh := (map_mono (f:=(MulAut.conj x⁻¹).toMonoidHom) hHD).trans
      (map_centralizer_le_centralizer_image _ _)
    rwa [terminal_central_fixed_map H (stabilizer d.radical c) hHC ((stabilizer d.radical c).inv_mem hx)] at hh
  exact hnon hHA

end SylowLargeCritical
end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
