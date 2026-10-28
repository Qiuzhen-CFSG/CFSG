module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.RadiusGrowth
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CoreBounds

/-!
# Endpoint movement and the full core supplement

A nonabelian selected orbit span has faithful symmetric-six action on its
central quotient. Its component-moved subgroup therefore escapes the starting
seed. The component acts idempotently on this moved subgroup. If the critical
endpoint fixed it modulo the seed, the normal-section action would force the
whole component to fix it there, contradicting that escape.

This proves the endpoint movement needed in the small-index residual argument
without first recognizing a natural central quotient. The resulting supplement
contains the full original core in the starting seed times the selected moved
span. The actual core and moved span have equal derived subgroups. The final
application feeds this supplement into the common-core commutator estimate.
Both cover orders and all original embedding and quotient conventions remain.

Source: MS93 (3.10) and the final core estimates of (5.12), printed
pp.879--881 and 926--927. This is an alternative proof of the movement premise
in SelectedSpan.selected_core_commutator_le_seed_sup_moved_span. The normal
section and transport arguments reuse the existing ForwardKernel, RadiusGrowth
and SelectedSpan proofs, without their natural-subgroup specialization.

The selected paths, their nonabelianness, the core index and endpoint estimates,
and fixedness of the selected derived subgroup remain source obligations of
qt-e-ms-small-a6-exhaustion-large-distance. This module proves neither terminal
distance exclusion. Final unconditional reconstruction remains with
qt-e-ms-small-a6-reconstruction.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  {h : SmallMSPair κ L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include h in
private theorem selected_span_le_core
    (hb : 2 < replacementDistance h d) {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a') :
    localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ≤ Q d.radical (alpha d.radical) := by
  apply (localZSpan_le_V d.radical _).trans
    (V_le_Q d.radical (geometry := replacementGeometry h d) rfl hb)
  rw [SimpleGraph.dist_comm,p.dist_start (by have hh : p.walk.length = replacementDistance h d := p.length_eq_b; omega)]


omit [Finite G] in
private theorem selected_normalized_comap_normal (J : Subgroup (FreeAmalgam d.radical))
    (hJ : stabilizer d.radical (alpha d.radical)≤normalizer (J:Set (FreeAmalgam d.radical))) :
    (J.comap (embedM d.radical)).Normal := by
  constructor
  intro n hn g
  change embedM d.radical (g*n*g⁻¹)∈J
  rw [map_mul,map_mul,map_inv]
  exact (le_normalizer_iff.mp hJ (embedM d.radical g)
    (by change embedM d.radical g∈stabilizer d.radical (mVertex d.radical 1); rw [stabilizer_m_base]; exact ⟨g,rfl⟩)) _ hn



include s in
/-- A nontrivial marked actor fixing a normal section forces the original
component to fix the same section. -/
theorem component_commutator_le_of_section_fixed
    (D Z A : Subgroup d.overgroup) [D.Normal] [Z.Normal]
    (hcomm : ⁅D,A⁆ ≤ Z) (hne : ¬ A ≤ pCore 2 d.overgroup) :
    ⁅D,replacementComponent d⁆ ≤ Z := by
  let B : NoncentralChiefRefinement.NormalNode d.overgroup := ⟨Z,(inferInstance : Z.Normal)⟩
  let C : NoncentralChiefRefinement.NormalNode d.overgroup := ⟨D,(inferInstance : D.Normal)⟩
  let ρ := NoncentralChiefRefinement.sectionAction B C
  let : MulDistribMulAction d.overgroup (NoncentralChiefRefinement.Section B C) :=
    MulDistribMulAction.compHom _ ρ
  have hfixed : FixedPoints.subgroup A (NoncentralChiefRefinement.Section B C) = ⊤ := by
    apply top_unique
    intro x _ a
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf D) x
    change QuotientGroup.mk' (Z.subgroupOf D) (MulAut.conjNormal a.val x) =
      QuotientGroup.mk' (Z.subgroupOf D) x
    apply QuotientGroup.eq_iff_div_mem.mpr
    change a.val*x.val*a.val⁻¹/x.val ∈ Z
    simpa only [commutatorElement_def,div_eq_mul_inv] using
      (show ⁅a.val,x.val⁆ ∈ Z from hcomm (by
        rw [commutator_comm]; exact commutator_mem_commutator a.property x.property))
  by_contra hm
  have hi := section_index_two_le s B C hm A hne
  change 2 ≤ (FixedPoints.subgroup A (NoncentralChiefRefinement.Section B C)).index at hi
  rw [hfixed,index_top] at hi
  omega

include s in
/-- Nonabelianness of the selected span forces its actual residual-moved
subgroup to escape the starting seed, before natural-section recognition. -/
theorem selected_moved_span_not_le_seed_of_nonabelian
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hnonabelian : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥) :
    ¬ forwardMovedSpan d.radical (p.walk.getVert 2) ≤ Z d.radical (alpha d.radical) := by
  let c := p.walk.getVert 2
  let P := localZSpan d.radical c (alpha d.radical)
  have hPQ : P ≤ Q d.radical (alpha d.radical) := selected_span_le_core hb p
  have hZC : Z d.radical (alpha d.radical) ≤ centralizer (P : Set (FreeAmalgam d.radical)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical _ rfl)).trans
      (centralizer_le hPQ)
  intro hW
  have hkernel := selected_span_central_action_kernel s hc hb p hnonabelian
  have hLker : replacementComponent d ≤ (forwardSpanCentralAction d.radical c).ker := by
    intro m hm
    change forwardSpanCentralAction d.radical c m = 1
    apply MulEquiv.ext
    intro x
    change forwardSpanCentralAction d.radical c m x = x
    induction x using QuotientGroup.induction_on with
    | H x =>
      change forwardSpanCentralAction d.radical c m (QuotientGroup.mk' (center P) x) =
        QuotientGroup.mk' (center P) x
      rw [forwardSpanCentralAction_apply]
      apply QuotientGroup.eq_iff_div_mem.mpr
      apply mem_center_iff.mpr
      intro y
      apply Subtype.ext
      have hmL : embedM d.radical m ∈ Ltilde d.radical (alpha d.radical) := by
        rw [Ltilde_alpha,replacement_residual h d]
        exact mem_map_of_mem _ hm
      have hw : ⁅embedM d.radical m,x.val⁆ ∈ forwardMovedSpan d.radical c := by
        rw [forwardMovedSpan,commutator_comm]
        exact commutator_mem_commutator hmL x.property
      change y.val*(embedM d.radical m*x.val*(embedM d.radical m)⁻¹/x.val) =
        (embedM d.radical m*x.val*(embedM d.radical m)⁻¹/x.val)*y.val
      simpa only [commutatorElement_def,div_eq_mul_inv] using hZC (hW hw) y y.property
  have hL : replacementComponent d ≤ pCore 2 d.overgroup := hLker.trans_eq hkernel
  have hi := map_mono (f := s.projection) hL
  have hk : s.projection.ker.map s.projection = ⊥ := (Subgroup.map_eq_bot_iff _).mpr le_rfl
  rw [s.component_image,←s.projection_kernel,hk] at hi
  have hzAlt : alternatingGroup (Fin 6) = ⊥ := le_bot_iff.mp hi
  exact (nontrivial_iff_ne_bot _).mp (inferInstance : Nontrivial (alternatingGroup (Fin 6))) hzAlt

include s in
/-- The critical endpoint moves the residual-moved span modulo the original
seed. Only nonabelianness of the selected span is needed for this estimate. -/
theorem selected_moved_span_endpoint_movement_of_nonabelian
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hnonabelian : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥) :
    ¬ ⁅forwardMovedSpan d.radical (p.walk.getVert 2),Z d.radical a'⁆ ≤
      Z d.radical (alpha d.radical) := by
  let c := p.walk.getVert 2
  let P := localZSpan d.radical c (alpha d.radical)
  let W := forwardMovedSpan d.radical c
  let f := embedM d.radical
  let Pm := P.comap f
  let Wm := W.comap f
  let Zm := (Z d.radical (alpha d.radical)).comap f
  let Am := (Z d.radical a').comap f
  let K := replacementComponent d
  have hGa : stabilizer d.radical (alpha d.radical) = f.range := stabilizer_m_base d.radical
  have hPQ : P ≤ Q d.radical (alpha d.radical) := selected_span_le_core hb p
  have hPG : P ≤ f.range := (hPQ.trans (fun _ hx => hx.1)).trans_eq hGa
  have hPm : Pm.map f = P := map_comap_eq_self hPG
  have hWm : Wm.map f = W := map_comap_eq_self ((forwardMovedSpan_le d.radical c).trans hPG)
  have hZm : Zm.map f = Z d.radical (alpha d.radical) :=
    map_comap_eq_self ((Z_le_stabilizer d.radical _).trans_eq hGa)
  have hAm : Am.map f = Z d.radical a' := map_comap_eq_self
    ((critical_Z_le_stabilizer d.radical (replacementGeometry h d) (alpha d.radical)
      rfl (replacementDistance_pos h d) p.critical).trans_eq hGa)
  have hKm : K.map f = Ltilde d.radical (alpha d.radical) := by
    rw [Ltilde_alpha,replacement_residual h d]
  let : Pm.Normal := selected_normalized_comap_normal _ (localZSpan_normalized d.radical _ _)
  let : Wm.Normal := selected_normalized_comap_normal _ (forwardMovedSpan_normalized d.radical _)
  let : Zm.Normal := selected_normalized_comap_normal _ (Z_normalized d.radical _)
  have hPcore : Pm ≤ pCore 2 d.overgroup := by
    have hh := comap_mono (f := f) hPQ
    rwa [Q_alpha_comap d.radical (replacement_radical_isPGroup h d)
      (replacement_core_le_radical h d)] at hh
  have hWP : Wm = ⁅Pm,K⁆ := by
    apply map_injective (embedM_injective d.radical)
    rw [map_commutator,hWm,hPm,hKm]
    rfl
  have hKperfect : IsPPerfect 2 K := by
    rw [show K = pResidual 2 d.overgroup from (replacement_residual h d).symm]
    exact isPPerfect_pResidual 2
  have hidem : ⁅Wm,K⁆ = Wm := by
    rw [hWP]
    exact commutator_isPPerfect_idempotent K Pm hKperfect
      (pCore_isPGroup.to_le hPcore) le_normalizer_of_normal
  have hA : ¬ Am ≤ pCore 2 d.overgroup := by
    intro ha
    apply (critical_reverse_pair s hc p).2
    have hh := map_mono (f := f) ha
    rwa [hAm,←Q_alpha d.radical (replacement_radical_isPGroup h d)
      (replacement_core_le_radical h d)] at hh
  intro hcomm
  have hcommm : ⁅Wm,Am⁆ ≤ Zm := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator,hWm,hAm]
    exact hcomm
  have hfixed := component_commutator_le_of_section_fixed s Wm Zm Am hcommm hA
  change ⁅Wm,K⁆ ≤ Zm at hfixed
  rw [hidem] at hfixed
  have hh := map_mono (f := f) hfixed
  rw [hWm,hZm] at hh
  exact selected_moved_span_not_le_seed_of_nonabelian s hc hb p hnonabelian hh

include s in
/-- The original core is covered by the starting seed and the selected moved
span. The endpoint movement follows from nonabelianness, without natural
coordinates or a fixed-derived-subgroup premise. -/
theorem selected_core_supplement_of_nonabelian_span
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hnonabelian : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥)
    (hindex : (Q d.radical (p.walk.getVert 2)).relIndex
      ⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆ ≤ 2)
    (hactor : ⁅⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆ ⊓
      Q d.radical (p.walk.getVert 2),Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical)) :
    ⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆ ≤
      Z d.radical (alpha d.radical) ⊔ forwardMovedSpan d.radical (p.walk.getVert 2) := by
  let c := p.walk.getVert 2
  let Q₀ := ⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆
  let P₀ := forwardMovedSpan d.radical c
  let D := Q₀⊓Q d.radical c
  let f := embedM d.radical
  let Qm := ⁅pCore 2 d.overgroup,pResidual 2 d.overgroup⁆
  let Um := (Z d.radical (alpha d.radical)).comap f
  let Wm := P₀.comap f
  let Dm := D.comap f
  let Am := (Z d.radical a').comap f
  have hQf : Qm.map f=Q₀ := by
    dsimp only [Qm,Q₀,f]
    rw [map_commutator,←Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d),←Ltilde_alpha]
  have hGa : stabilizer d.radical (alpha d.radical)=f.range := stabilizer_m_base d.radical
  have hQGa : Q d.radical (alpha d.radical)≤stabilizer d.radical (alpha d.radical) := fun _ hx => hx.1
  have hPQ : P₀≤Q d.radical (alpha d.radical) := (forwardMovedSpan_le d.radical c).trans
    (selected_span_le_core hb p)
  have hP₀Q₀ : P₀≤Q₀ := commutator_mono
    (selected_span_le_core hb p) le_rfl
  have hPf : Wm.map f=P₀ := map_comap_eq_self (hPQ.trans (hQGa.trans_eq hGa))
  have hUf : Um.map f=Z d.radical (alpha d.radical) := map_comap_eq_self
    ((Z_le_stabilizer d.radical _).trans_eq hGa)
  have hQ₀Ga : Q₀≤stabilizer d.radical (alpha d.radical) :=
    (le_normalizer_iff_commutator_le_left.mp
      ((Ltilde_le_stabilizer _).trans (Q_normalized d.radical _))).trans hQGa
  have hDf : Dm.map f=D := map_comap_eq_self (inf_le_left.trans (hQ₀Ga.trans_eq hGa))
  have hAf : Am.map f=Z d.radical a' := map_comap_eq_self
    ((critical_Z_le_stabilizer d.radical (replacementGeometry h d) (alpha d.radical) rfl (replacementDistance_pos h d) p.critical).trans_eq hGa)
  have hQm : Q₀.comap f=Qm := by
    rw [←hQf,comap_map_eq_self_of_injective (embedM_injective d.radical)]
  let : Um.Normal := selected_normalized_comap_normal _ (Z_normalized d.radical _)
  let : Wm.Normal := selected_normalized_comap_normal _ (forwardMovedSpan_normalized d.radical _)
  have hWQ : Wm≤Qm := by rw [←hQm]; exact comap_mono hP₀Q₀
  have hDQ : Dm≤Qm := by rw [←hQm]; exact comap_mono inf_le_left
  have hi : Dm.relIndex Qm≤2 := by
    rw [relIndex_comap,hQf]
    simpa only [D,inf_relIndex_left] using hindex
  have hmove : ⁅Qm,pResidual 2 d.overgroup⁆=Qm :=
    commutator_isPPerfect_idempotent _ _ (isPPerfect_pResidual 2) pCore_isPGroup le_normalizer_of_normal
  have hDA : ⁅Dm,Am⁆≤Um := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator,hDf,hAf]
    exact hactor
  have hnot : ¬Wm≤Dm := by
    intro he
    have hPD : P₀≤D := by rw [←hPf,←hDf]; exact map_mono he
    exact selected_moved_span_endpoint_movement_of_nonabelian s hc hb p hnonabelian
      ((commutator_mono hPD le_rfl).trans hactor)
  obtain ⟨t,ht,hswap⟩ := small_critical_image_swap s hc p hsmall
  have hodd : ¬ Am.map s.projection ≤ alternatingGroup (Fin 6) := by
    intro hh
    have hs := Equiv.Perm.mem_alternatingGroup.mp (hh ht)
    rw [hswap.sign_eq] at hs
    exact (by decide : (-1 : Units ℤ) ≠ 1) hs
  have hresult := residual_moved_le_of_symmetricSix_odd_small_index s.projection
    s.surjective
    (by rw [s.projection_kernel]; exact pCore_isPGroup)
    Qm Um Wm Dm Am hWQ hDQ hi hmove hDA hnot
    hodd
  have hh := map_mono (f:=f) hresult
  rwa [hQf,Subgroup.map_sup,hUf,hPf] at hh


/-- On the original replacement the nonabelian selected span supplies the
core supplement and the equality of the literal core and moved-span derived
subgroups. The source core-index and endpoint-commutator estimates remain
explicit; natural-section coordinates are no longer premises. -/
theorem selected_core_supplement_knownSimple_of_nonabelian
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hnonabelian : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥)
    (hindex : (Q d.radical (p.walk.getVert 2)).relIndex
      ⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆ ≤ 2)
    (hactor : ⁅⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆ ⊓
      Q d.radical (p.walk.getVert 2),Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical)) :
    let C := ⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆
    let W := forwardMovedSpan d.radical (p.walk.getVert 2)
    C ≤ Z d.radical (alpha d.radical) ⊔ W ∧ ⁅C,C⁆ = ⁅W,W⁆ := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hs := selected_core_supplement_of_nonabelian_span s hc hb p hsmall hnonabelian hindex hactor
  exact ⟨hs,selected_core_derived_eq_of_supplement hb p hs⟩

/-- The same source estimates now feed the actual common-core commutator
bound without a natural-quotient coordinate callback. Fixedness of the
selected derived subgroup remains a source obligation. -/
theorem selected_core_cross_bound_knownSimple_of_nonabelian
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hnonabelian : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥)
    (hfixed : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≤
      centralizer (Ltilde d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)))
    (hindex : (Q d.radical (p.walk.getVert 2)).relIndex
      ⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆ ≤ 2)
    (hactor : ⁅⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆ ⊓
      Q d.radical (p.walk.getVert 2),Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical)) :
    let C := ⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆
    ⁅Q d.radical (alpha d.radical) ⊓ Q d.radical (p.walk.getVert 2),C⁆ ≤ ⁅C,C⁆ :=
  selected_core_cross_commutator_of_supplement hb p hfixed
    (selected_core_supplement_knownSimple_of_nonabelian (e := e) (hz := hz) (hn := hn)
      hb p hsmall hnonabelian hindex hactor).1


end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
