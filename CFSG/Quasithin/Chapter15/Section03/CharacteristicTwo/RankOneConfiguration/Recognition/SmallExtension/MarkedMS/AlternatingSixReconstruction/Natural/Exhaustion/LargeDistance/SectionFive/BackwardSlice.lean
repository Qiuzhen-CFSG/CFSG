module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.ReciprocalSlice
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EdgeKernels
public import Theory.GroupTheory.Commutator.RelativeGeneration
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreEvenGeneration

/-!
# Backward critical shifts and upper slice bounds in the large-image branch

On an edge which generates the initial stabilizer with the opposite seed,
an eligible backward cover cannot lie in the predecessor kernel. Indeed,
that containment would bound its endpoint commutator by the starting seed.
The generated two-seed product is then normal in the starting stabilizer;
its residual action places the backward cover in the Baumann slice, a
contradiction. This uses the actual radius commutator estimate under
point-core containment, with both moved-cover orders retained.

For a small backward critical image, the incident edge normalizes its full
kernel. The same normal-product argument puts that kernel in the Baumann
slice and proves the upper slice index two. Transport of the prescribed
neighbor uses one stabilizer element, and the constructed critical walk
retains every overlapping vertex. A slice index greater than two therefore
forces a large backward image and radius indices at least eight at both
ends of that same walk.

In the full point-core branch, the even critical actor constructs the
generating edge. The original replacement applications discharge the
symmetric-action and central-layer inputs, construct an eligible backward
critical path, and apply the strict-radius propagation to the canonical
quotient map. Full point-core equality is an explicit branch hypothesis;
it is not inferred from containment or from a natural quotient.

Source: Meierfrankenfeld--Stellmacher (1993), (5.5)(a), (5.7), (5.8) and
(5.12)(3), printed pp.915,919--920,926--927, using (5.2)(i). The normal-product
and generating-edge arguments adapt SymplecticSetup.BackwardCritical,
SelectedKernel and CriticalGeneration to the full central cover.
The source choices for the other radical images, the small-original-image
backward step, exclusion of radius index four, intermediate R4/R6
noncentrality and both terminal contradictions remain with
qt-e-ms-small-a6-exhaustion-large-distance. No distance bound is asserted.
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
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)


include s in
private theorem backward_kernel_le_slice_of_large_image
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hR : d.radical.map s.projection ≤
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom)
    {a' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical)))
    (hat : Adjacent d.radical (alpha d.radical) t) (hct : Adjacent d.radical c t)
    (hgen : Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical))
    (A : Subgroup (FreeAmalgam d.radical))
    (hAc : A ≤ Z d.radical c)
    (hAQ : A ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hAn : Q d.radical t ≤ normalizer (A : Set (FreeAmalgam d.radical))) :
    A ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) := by
  have hdist : (cosetGraph d.radical).dist c (alpha d.radical) ≤ 2 := by
    have h1 : (cosetGraph d.radical).dist c t = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hct)
    have h2 : (cosetGraph d.radical).dist t (alpha d.radical) = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr
        ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
    simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle
      (u := c) (v := t) (w := alpha d.radical)
  have hAV : A ≤ V d.radical (alpha d.radical) :=
    hAc.trans ((Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hdist))
  have hAG := hAV.trans ((replacementGeometry h d).V_local _ rfl hb)
  have hmove : ⁅A,Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical) :=
    (commutator_mono (le_inf hAV hAQ) le_rfl).trans
      (critical_radius_commutator_le_Z s hc u hR hb p hlarge)
  have hZmove : ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ ≤
      Z d.radical (alpha d.radical) :=
    ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans
      (DistanceEight.U_le_Z d.radical _)
  let Y := A ⊔ Z d.radical (alpha d.radical)
  have hYmove : ⁅Y,Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical) :=
    commutator_sup_le_of_relative_normal (stabilizer d.radical (alpha d.radical))
      A (Z d.radical (alpha d.radical)) (Z d.radical a')
      (Z d.radical (alpha d.radical)) (Z_normalized d.radical _) hAG
      (Z_le_stabilizer d.radical _) hmove hZmove
  have hYn : stabilizer d.radical (alpha d.radical) ≤
      normalizer (Y : Set (FreeAmalgam d.radical)) := by
    rw [←hgen]
    apply sup_le
    · exact (le_inf hAn ((show Q d.radical t ≤ stabilizer d.radical (alpha d.radical) from
        fun _ hx => hx.2 _ (adjacent_symm d.radical hat)).trans
        (Z_normalized d.radical (alpha d.radical)))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
    · exact le_normalizer_iff_commutator_le_left.mpr (hYmove.trans le_sup_right)
  exact le_sup_left.trans (normalized_radius_le_slice_of_critical_commutator s hc hb p Y
    (sup_le hAV (Z_le_VBall d.radical _ 2)) hYn hYmove)

include s in
/-- A generating edge and an eligible moved cover force the backward critical
noncontainment in the large-image branch. The full central cover is retained. -/
theorem large_image_backward_not_le
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hR : d.radical.map s.projection ≤
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom)
    {a' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical)))
    (hat : Adjacent d.radical (alpha d.radical) t) (hct : Adjacent d.radical c t)
    (hgen : Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical))
    (hel : ¬ U d.radical c ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)) :
    ¬ Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) := by
  intro hbad
  apply hel
  apply (DistanceEight.U_le_Z d.radical c).trans
  apply backward_kernel_le_slice_of_large_image s hc hb u hR p hlarge hat hct hgen
    (Z d.radical c) le_rfl hbad
  exact (show Q d.radical t ≤ stabilizer d.radical c from
    fun _ hx => hx.2 _ (adjacent_symm d.radical hct)).trans (Z_normalized d.radical c)

include s in
/-- The full kernel of a small backward critical pair lies in the starting
Baumann slice when the original image is large. Point-core containment is
sufficient; equality with that point core is not assumed. -/
theorem large_image_backward_kernel_le_slice
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hR : d.radical.map s.projection ≤
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom)
    {a' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical)))
    (hat : Adjacent d.radical (alpha d.radical) t) (hct : Adjacent d.radical c t)
    (hgen : Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical))
    (q : CriticalPath d.radical (replacementGeometry h d) c
      (p.walk.getVert (p.walk.length-2))) (hqt : q.walk.getVert 1 = t)
    (hsmall : (Q d.radical (p.walk.getVert (p.walk.length-2))).relIndex (Z d.radical c) < 4) :
    Z d.radical c ⊓ Q d.radical (p.walk.getVert (p.walk.length-2)) ≤
      B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) := by
  let := Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore_elementary
  let : IsElementaryAbelian 2 (Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map
      (MulAut.conj u).toMonoidHom) := IsElementaryAbelian.map _
  let helem : IsElementaryAbelian 2 (d.radical.map s.projection) := IsElementaryAbelian.of_le hR
  have hab : ⁅d.radical.map s.projection,d.radical.map s.projection⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff_isMulCommutative.mpr helem.toIsMulCommutative)
  have hAn := (small_critical_end_kernels_normalized_of_abelian_image s hc hab q hsmall).1
  rw [hqt] at hAn
  exact backward_kernel_le_slice_of_large_image s hc hb u hR p hlarge hat hct hgen _
    inf_le_left inf_le_right hAn

include s in
/-- The selected small backward image supplies the actual upper bound two
on the moved-cover slice, including its possible central kernel. -/
theorem large_image_backward_slice_le_two
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hR : d.radical.map s.projection ≤
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom)
    {a' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical)))
    (hat : Adjacent d.radical (alpha d.radical) t) (hct : Adjacent d.radical c t)
    (hgen : Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical))
    (q : CriticalPath d.radical (replacementGeometry h d) c
      (p.walk.getVert (p.walk.length-2))) (hqt : q.walk.getVert 1 = t)
    (hsmall : (Q d.radical (p.walk.getVert (p.walk.length-2))).relIndex (Z d.radical c) < 4) :
    (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c) ≤ 2 := by
  let := finite_Z d.radical c
  have hB := large_image_backward_kernel_le_slice s hc hb u hR p hlarge hat hct hgen q hqt hsmall
  have hidx := relIndex_le_of_le_left hB
    (index_ne_zero_of_finite (H := (Z d.radical c ⊓
      Q d.radical (p.walk.getVert (p.walk.length-2))).subgroupOf (Z d.radical c)))
  rw [inf_relIndex_left] at hidx
  exact ((relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical c)
    index_ne_zero_of_finite).trans hidx).trans_eq (small_critical_indices s hc q hsmall).1

include s in
/-- Preserve the selected backward conjugator, the first edge and every
shared vertex. A small shifted critical image forces the original eligible
slice to have index two. -/
theorem large_image_backward_shift
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hR : d.radical.map s.projection ≤
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom)
    {a' delta t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical)))
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hel : ¬ U d.radical delta ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _))
    (hat : Adjacent d.radical (alpha d.radical) t)
    (hgen : Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical)) :
    ∃ g ∈ stabilizer d.radical (alpha d.radical),
      act d.radical g (p.walk.getVert 1) = t ∧
      ∃ q : CriticalPath d.radical (replacementGeometry h d) (act d.radical g delta)
        (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1 = t ∧
        (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
        ((Q d.radical (p.walk.getVert (p.walk.length-2))).relIndex
            (Z d.radical (act d.radical g delta)) < 4 →
          (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
            (U d.radical delta) = 2) := by
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have ha1 : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors d.radical (alpha d.radical) ha1 hat
  let c := act d.radical g delta
  have hct : Adjacent d.radical c t := by
    rw [←hgt]
    exact (adjacent_act_iff d.radical g delta (p.walk.getVert 1)).mpr hdelta
  have hcol : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    change false ≠ color d.radical t at h1
    cases hc : color d.radical c <;> cases ht : color d.radical t <;> simp_all
  have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb (alpha d.radical) rfl ((stabilizer d.radical (alpha d.radical)).inv_mem hg))
  have helc : ¬ U d.radical c ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) := by
    intro hh
    apply hel
    change U d.radical (act d.radical g delta) ≤ _ at hh
    rw [U_act,←hB] at hh
    exact (map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective).mp hh
  have hbad := large_image_backward_not_le s hc hb u hR p hlarge hat hct hgen helc
  let w : (cosetGraph d.radical).Walk c (alpha d.radical) :=
    .cons ((cosetGraph_adj d.radical _ _).mpr hct)
      (.cons ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat)) .nil)
  have hw : w.length = 2 := rfl
  let q := p.prepend_two (by exact Nat.le_of_lt hb) hcol w hw hbad
  have hqt : q.walk.getVert 1 = t := by
    simp only [q,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
      hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
      SimpleGraph.Walk.getVert_zero]
  refine ⟨g,hg,hgt,q,hqt,fun i hi => p.prepend_two_overlap _ _ _ _ _ hi,?_⟩
  intro hsmall
  have hbound := large_image_backward_slice_le_two s hc hb u hR p hlarge hat hct hgen q hqt hsmall
  change (B d.radical (alpha d.radical) _).relIndex (U d.radical (act d.radical g delta)) ≤ 2 at hbound
  rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective] at hbound
  let := finite_Z d.radical delta
  let : Finite (U d.radical delta) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical delta)) (inclusion_injective _)
  have hp : 0 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta) := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hn : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta) ≠ 1 := fun he => hel (relIndex_eq_one.mp he)
  omega

include s in
/-- In the full point-core branch the actual even critical actor selects a
generating neighbor. Only the quotient marking is used, so both central
cover orders remain possible. -/
theorem large_image_full_point_generating_neighbor
    (hc : DistanceTwo.CentralLayer d) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map s.projection =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical) := by
  obtain ⟨a,ha,hao,haeven⟩ := exists_even_involution_reverse_critical_image s hc
    (replacementDistance_pos h d) p hlarge
  obtain ⟨k,hk⟩ := PointCoreEvenGeneration.exists_even_conjugate_pointCore_generates
    u ⟨a,haeven⟩ ((Subgroup.orderOf_coe ⟨a,haeven⟩).symm.trans hao)
  have hkL : k.val ∈ (replacementComponent d).map s.projection := by
    rw [s.component_image]
    exact k.property
  obtain ⟨g,hg,hgk⟩ := hkL
  let A := (Z d.radical a').comap (embedM d.radical)
  have hm : (d.radical.map (MulAut.conj g).toMonoidHom).map s.projection =
      (d.radical.map s.projection).map (MulAut.conj k.val).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change s.projection (g*x*g⁻¹) = k.val*s.projection x*k.val⁻¹
    rw [map_mul,map_mul,map_inv,hgk]
  have hQ : (pCore 2 d.overgroup).map (MulAut.conj g).toMonoidHom = pCore 2 d.overgroup :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
  have hker : s.projection.ker ≤ d.radical.map (MulAut.conj g).toMonoidHom := by
    rw [s.projection_kernel,←hQ]
    exact map_mono (replacement_core_le_radical h d)
  have hgen : d.radical.map (MulAut.conj g).toMonoidHom ⊔ A = ⊤ := by
    apply map_injective_of_ker_le s.projection (hker.trans le_sup_left) le_top
    rw [Subgroup.map_sup,hm,hfull,map_top_of_surjective s.projection s.surjective]
    apply top_unique
    rw [←hk]
    exact sup_le_sup_left (zpowers_le.mpr ha) _
  let f := (embedM d.radical g)⁻¹
  have hf : f ∈ stabilizer d.radical (alpha d.radical) := by
    change f ∈ stabilizer d.radical (mVertex d.radical 1)
    rw [stabilizer_m_base]
    exact ⟨g⁻¹,by simp only [map_inv,f]⟩
  have hfix : act d.radical f (alpha d.radical) = alpha d.radical := hf
  refine ⟨act d.radical f (beta d.radical),?_,?_⟩
  · rw [←hfix]
    exact (adjacent_act_iff d.radical f (alpha d.radical) (beta d.radical)).mpr
      (base_adjacent d.radical)
  · have hmapA : A.map (embedM d.radical) = Z d.radical a' :=
      map_comap_eq_self ((critical_Z_le_stabilizer d.radical (replacementGeometry h d)
        (alpha d.radical) rfl (replacementDistance_pos h d) p.critical).trans_eq
          (stabilizer_m_base d.radical))
    have hh := congrArg (Subgroup.map (embedM d.radical)) hgen
    rw [Subgroup.map_sup,hmapA,←MonoidHom.range_eq_map] at hh
    rw [Q_act,Q_beta]
    change _ = stabilizer d.radical (mVertex d.radical 1)
    rw [stabilizer_m_base]
    have hmapR : (d.radical.map (embedM d.radical)).map (MulAut.conj f⁻¹).toMonoidHom =
        (d.radical.map (MulAut.conj g).toMonoidHom).map (embedM d.radical) := by
      rw [map_map,map_map]
      congr 1
      apply MonoidHom.ext
      intro x
      change f⁻¹*embedM d.radical x*(f⁻¹)⁻¹=embedM d.radical (g*x*g⁻¹)
      simp only [f,inv_inv,map_mul,map_inv]
    rw [hmapR]
    exact hh

/-- On the original replacement, the full point-core branch transports an
eligible slice of index greater than two to a backward critical pair with
large seed images and radius indices at least eight at both endpoints.
The generating edge and all overlapping path vertices are constructed. -/
theorem large_image_backward_large_radii_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom)
    {a' delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical)))
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hindex : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta)) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical) ∧
      ∃ g ∈ stabilizer d.radical (alpha d.radical),
        act d.radical g (p.walk.getVert 1) = t ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d) (act d.radical g delta)
          (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = t ∧
          (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
          4 ≤ (Q d.radical (p.walk.getVert (p.walk.length-2))).relIndex
            (Z d.radical (act d.radical g delta)) ∧
          4 ≤ (Q d.radical (act d.radical g delta)).relIndex
            (Z d.radical (p.walk.getVert (p.walk.length-2))) ∧
          8 ≤ (Q d.radical (p.walk.getVert (p.walk.length-2))).relIndex
            (V d.radical (act d.radical g delta)) ∧
          8 ≤ (Q d.radical (act d.radical g delta)).relIndex
            (V d.radical (p.walk.getVert (p.walk.length-2))) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hfull' : d.radical.map s.projection =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  obtain ⟨t,hat,hgen⟩ := large_image_full_point_generating_neighbor s hc u hfull' p hlarge
  have hel : ¬ U d.radical delta ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) := by
    intro he
    have hi := relIndex_eq_one.mpr he
    omega
  obtain ⟨g,hg,hgt,q,hqt,hover,hsmall⟩ := large_image_backward_shift s hc hb u hfull'.le
    p hlarge hdelta hel hat hgen
  have hqlarge : 4 ≤ (Q d.radical (p.walk.getVert (p.walk.length-2))).relIndex
      (Z d.radical (act d.radical g delta)) := by
    by_contra! hh
    have he := hsmall hh
    omega
  have hrlarge := reverse_critical_image_four_le s hc (replacementDistance_pos h d) q hqlarge
  have hrad := critical_radius_index_two_mul_seed_le s hc hb q
  let qr : CriticalPath d.radical (replacementGeometry h d)
      (p.walk.getVert (p.walk.length-2)) (act d.radical g delta) :=
    ⟨q.end_color,q.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,q.shortest,SimpleGraph.dist_comm],
      critical_reverse_pair s hc q⟩
  have hrad' := critical_radius_index_two_mul_seed_le s hc hb qr
  exact ⟨t,hat,hgen,g,hg,hgt,q,hqt,hover,hqlarge,hrlarge,by omega,by omega⟩

/-- The full point-core branch constructs an eligible backward critical walk
without an independently assumed neighbor, generation equation or slice bound.
The entire overlap with the original walk is retained. -/
theorem large_image_full_point_backward_path_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) :
    ∃ c t, Adjacent d.radical (alpha d.radical) t ∧
      Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical) ∧
      ∃ q : CriticalPath d.radical (replacementGeometry h d) c
        (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1 = t ∧
        (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
        2 ≤ (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical c) ∧
        ((Q d.radical (p.walk.getVert (p.walk.length-2))).relIndex (Z d.radical c) < 4 →
          (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
            (U d.radical c) = 2) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hfull' : d.radical.map s.projection =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  obtain ⟨t,hat,hgen⟩ := large_image_full_point_generating_neighbor s hc u hfull' p hlarge
  obtain ⟨c,hct,hel⟩ := exists_eligible_neighbor_at_edge s hc hb rfl hat
  have hcol : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    change false ≠ color d.radical t at h1
    cases hc : color d.radical c <;> cases ht : color d.radical t <;> simp_all
  have hbad := large_image_backward_not_le s hc hb u hfull'.le p hlarge hat hct hgen hel
  let w : (cosetGraph d.radical).Walk c (alpha d.radical) :=
    .cons ((cosetGraph_adj d.radical _ _).mpr hct)
      (.cons ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat)) .nil)
  have hw : w.length = 2 := rfl
  let q := p.prepend_two (Nat.le_of_lt hb) hcol w hw hbad
  have hqt : q.walk.getVert 1 = t := by
    simp only [q,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
      hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
      SimpleGraph.Walk.getVert_zero]
  have hover (i : ℕ) (hi : i ≤ p.walk.length-2) :
      q.walk.getVert (i+2) = p.walk.getVert i := p.prepend_two_overlap _ _ _ _ _ hi
  have hqa : q.walk.getVert 2 = alpha d.radical := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (Nat.zero_le _)
  have hlo := critical_start_slice_index_two_le s hc hb q
  rw [hqa] at hlo
  refine ⟨c,t,hat,hgen,q,hqt,hover,hlo,?_⟩
  intro hs
  exact Nat.le_antisymm
    (large_image_backward_slice_le_two s hc hb u hfull'.le p hlarge hat hct hgen q hqt hs) hlo

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
