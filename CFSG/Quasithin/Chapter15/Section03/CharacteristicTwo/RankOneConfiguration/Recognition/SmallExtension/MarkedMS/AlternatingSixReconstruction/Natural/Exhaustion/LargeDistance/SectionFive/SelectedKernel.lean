module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SmallKernel
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SelectedSpan

/-!
# The source forward slice and the actual selected natural quotient

The kernel in the starting two-core centralizing the forward Baumann slice
is normalized by the entire starting stabilizer. The selected conjugate
seed span lies in this kernel. If the forward slice has index at most two,
the full-cover fixed-space theorem bounds the kernel's second-vertex image
by two, and hence bounds the selected span's image by two.

The full small critical-kernel fixer supplies the endpoint commutator
estimate from the literal fixed-kernel premise. Together these calculations
feed the actual natural central quotient, its derived-line transfer, and
the conditional terminal contradiction. The natural quotient is never
replaced by a subgroup, and both original cover orders remain possible.

Source: MS93 (5.12)(3) and its final paragraph, printed pp.926--927,
using (3.10), pp.879--881. The normalization and span arguments adapt
SymplecticSetup.ForwardKernel and ForwardSpanDerived; SmallKernel replaces
their natural-subgroup and full-point-image restrictions.

The source forward slice choice, fixed critical kernel, nonabelianness,
fixed derived subgroup, and opposite core bounds remain obligations of
qt-e-ms-small-a6-exhaustion-large-distance. The same owner retains (5.11)
and final large-distance assembly. The final unconditional reconstruction
remains with qt-e-ms-small-a6-reconstruction.
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

private theorem fixed_mod_central_normalizes_centralizer {G : Type*} [Group G]
    (A Q L : Subgroup G) (hLQ : L ≤ normalizer (Q : Set G))
    (hLA : ⁅L,A⁆ ≤ centralizer (Q : Set G)) :
    L ≤ normalizer ((Q ⊓ centralizer (A : Set G) : Subgroup G) : Set G) := by
  apply le_normalizer_iff.mpr
  intro l hl q hq
  refine ⟨(mem_normalizer_iff.mp (hLQ hl) q).mp hq.1,?_⟩
  intro a ha
  have hh := hLA (commutator_mem_commutator (L.inv_mem hl) ha)
  have h1 : Commute ⁅l⁻¹,a⁆ q := (hh q hq.1).symm
  have h2 : Commute a q := hq.2 a ha
  have hc : Commute (l⁻¹*a*l) q := by
    have he : ⁅l⁻¹,a⁆*a=l⁻¹*a*l := by simp [commutatorElement_def,mul_assoc]
    exact he ▸ h1.mul_left h2
  have hm := hc.map (MulAut.conj l).toMonoidHom
  change Commute (l*(l⁻¹*a*l)*l⁻¹) (l*q*l⁻¹) at hm
  have he : l*(l⁻¹*a*l)*l⁻¹=a := by group
  rw [he] at hm
  exact hm.eq

include h in
private theorem core_residual_edge_generation {a t : Vertex d.radical}
    (ha : color d.radical a = false) (hat : Adjacent d.radical a t) :
    Ltilde d.radical a ⊔ Q d.radical t = stabilizer d.radical a := by
  have hsup : replacementComponent d ⊔ d.radical = ⊤ := by
    apply top_unique
    intro g _
    obtain ⟨k,hk,r,hr,rfl⟩ := replacement_product h d g
    exact mul_mem (mem_sup_left hk) (mem_sup_right hr)
  have hbase : Ltilde d.radical (alpha d.radical) ⊔ Q d.radical (beta d.radical) =
      stabilizer d.radical (alpha d.radical) := by
    rw [Ltilde_alpha,replacement_residual h d,Q_beta,←Subgroup.map_sup,hsup]
    exact (MonoidHom.range_eq_map (embedM d.radical)).symm.trans (stabilizer_m_base d.radical).symm
  obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common d.radical a t).mp hat
  · rcases hg with ⟨rfl,rfl⟩
    have he := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hbase
    rw [Subgroup.map_sup,←Ltilde_act,←Q_act,←stabilizer_act] at he
    simpa only [alpha,beta,act_mVertex,act_hVertex,one_mul] using he
  · rw [hg.1] at ha
    cases ha

include h in
/-- The forward slice kernel is normal relative to the starting stabilizer. -/
theorem selected_forward_kernel_normalized (hb : 2 < replacementDistance h d) {a c t : Vertex d.radical}
    (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t) :
    stabilizer d.radical a ≤ normalizer ((Q d.radical a ⊓ centralizer
      (U d.radical c ⊓ B d.radical a ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical)) :
        Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
  let K := U d.radical c ⊓ B d.radical a ((replacementGeometry h d).Z_normal _)
  have hb' : 2 < criticalDistance d.radical a ((replacementGeometry h d).exists_critical a ha) := by
    rw [(replacementGeometry h d).distance_constant a ha]
    exact hb
  have hVL := (replacementGeometry h d).V_local a ha hb'
  have hLK : ⁅Ltilde d.radical a,K⁆ ≤ centralizer (Q d.radical a : Set (FreeAmalgam d.radical)) := by
    apply le_trans _ (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a ha))
    apply commutator_le.mpr
    intro l hl k hk
    exact ((mem_B_iff d.radical a _ hVL k).mp hk.2).2 l hl
  have hLN := fixed_mod_central_normalizes_centralizer K (Q d.radical a) (Ltilde d.radical a)
    ((Ltilde_le_stabilizer a).trans (Q_normalized d.radical a)) hLK
  have htG : Q d.radical t ≤ stabilizer d.radical a := fun _ hx => hx.2 _ (adjacent_symm d.radical hat)
  have htC : Q d.radical t ≤ stabilizer d.radical c := fun _ hx => hx.2 _ (adjacent_symm d.radical hct)
  have htK : Q d.radical t ≤ normalizer (K : Set (FreeAmalgam d.radical)) :=
    (le_inf (htC.trans (U_normalized c))
      (htG.trans (Escape.Propagation.Rigidity.B_normalized hb a ha))).trans
        inf_normalizer_le_normalizer_inf
  have htCK : Q d.radical t ≤ normalizer (centralizer (K : Set (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) :=
    htK.trans (le_normalizer_of_normal_subgroupOf (Subgroup.centralizer_le_normalizer _))
  have htN := (le_inf (htG.trans (Q_normalized d.radical a)) htCK).trans
    inf_normalizer_le_normalizer_inf
  rw [←core_residual_edge_generation (h := h) ha hat]
  exact sup_le hLN htN



include h in
/-- The actual selected orbit span is contained in the forward slice kernel. -/
theorem selected_span_le_forward_kernel
    (hb : 2 < replacementDistance h d) {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a') :
    localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ≤
      Q d.radical (alpha d.radical) ⊓ centralizer
        (U d.radical (p.walk.getVert 2) ⊓ B d.radical (alpha d.radical)
          ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical)) := by
  let c := p.walk.getVert 2
  let T := Q d.radical (alpha d.radical) ⊓ centralizer
    (U d.radical c ⊓ B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hc : color d.radical c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent d.radical c (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hZT : Z d.radical c ≤ T := by
    apply le_inf
    · apply Z_le_Q_of_dist_lt d.radical c ((replacementGeometry h d).exists_critical c hc)
      rw [(replacementGeometry h d).distance_constant c hc,SimpleGraph.dist_comm,
        p.dist_start (by omega)]
      exact hb
    · let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) c hc
      exact (le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
        (centralizer_le (inf_le_left.trans (DistanceEight.U_le_Z d.radical c)))
  have hn := selected_forward_kernel_normalized (h := h) hb rfl hat hct
  rw [localZSpan_eq_conjugates]
  apply iSup_le
  intro g
  rintro _ ⟨z,hz,rfl⟩
  exact (mem_normalizer_iff.mp
    (hn ((stabilizer d.radical (alpha d.radical)).inv_mem g.property)) z).mp (hZT hz)

include s in
/-- Source (5.12)(3)'s small forward slice bounds both the whole slice
kernel and the selected span at the literal second vertex. -/
theorem selected_span_index_of_forward_slice
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2) :
    let T := Q d.radical (alpha d.radical) ⊓ centralizer
      (U d.radical (p.walk.getVert 2) ⊓ B d.radical (alpha d.radical)
        ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
    (Q d.radical (p.walk.getVert 2)).relIndex T ≤ 2 ∧
      (Q d.radical (p.walk.getVert 2)).relIndex
        (localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)) ≤ 2 := by
  let c := p.walk.getVert 2
  let K := U d.radical c ⊓ B d.radical (alpha d.radical)
    ((replacementGeometry h d).Z_normal _)
  let T := Q d.radical (alpha d.radical) ⊓ centralizer (K : Set (FreeAmalgam d.radical))
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcol : color d.radical c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent d.radical c (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color d.radical (p.walk.getVert 1) = true := by
    have hh := adjacent_color_ne d.radical hat
    change false ≠ color d.radical (p.walk.getVert 1) at hh
    cases he : color d.radical (p.walk.getVert 1) <;> simp_all
  have hTG : T ≤ stabilizer d.radical c :=
    (inf_le_left.trans (Q_le_adjacent_h d.radical ht hat)).trans
      (fun _ hx => hx.2 _ (adjacent_symm d.radical hct))
  let := finite_Z d.radical c
  let : Finite (U d.radical c) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical c)) (inclusion_injective _)
  have hfix : K ≤ centralizer (T : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp inf_le_right
  have hidx : (centralizer (T : Set (FreeAmalgam d.radical))).relIndex (U d.radical c) ≤ 2 := by
    have hh := relIndex_le_of_le_left hfix (index_ne_zero_of_finite (H := K.subgroupOf (U d.radical c)))
    change (centralizer (T : Set (FreeAmalgam d.radical))).relIndex (U d.radical c) ≤
      K.relIndex (U d.radical c) at hh
    exact hh.trans (by simpa only [K,inf_relIndex_left] using hslice)
  have hTidx := moving_small_fixed_index_image s hc hcol T hTG hidx
  let := finite_stabilizer d.radical (alpha d.radical)
  let : Finite T := Finite.of_injective
    (inclusion (inf_le_left.trans (show Q d.radical (alpha d.radical) ≤
      stabilizer d.radical (alpha d.radical) from fun _ hx => hx.1))) (inclusion_injective _)
  exact ⟨hTidx,(relIndex_le_of_le_right (selected_span_le_forward_kernel (h := h) hb p)
    index_ne_zero_of_finite).trans hTidx⟩

include s in
/-- The full small critical kernel supplies the selected-span endpoint bound
from its source fixed-kernel premise. -/
theorem selected_span_endpoint_commutator_of_kernel_fixed
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hfix : localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊓
        Q d.radical (p.walk.getVert 2) ≤ centralizer
          (Z d.radical a' ⊓ Q d.radical (alpha d.radical) : Set (FreeAmalgam d.radical))) :
    ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊓
        Q d.radical (p.walk.getVert 2), Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical) := by
  apply small_critical_predecessor_commutator s hc (by omega) p hsmall _ _ hfix
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  simpa only [hl,Nat.reduceSub] using
    (inf_le_right : localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊓
      Q d.radical (p.walk.getVert 2) ≤ Q d.radical (p.walk.getVert 2))

/-- The source forward slice and fixed critical kernel supply the numerical
and endpoint-action premises of the actual selected natural quotient and
derived-line transfer. The source slice choice, nonabelianness and fixed
derived subgroup remain with the large-distance assembly owner. -/
theorem selected_natural_quotient_and_transfer_of_forward_slice_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : replacementDistance h d = 4)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hnonabelian : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥)
    (hfixed : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≤
      centralizer (Ltilde d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)))
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2)
    (hkernel : localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊓
        Q d.radical (p.walk.getVert 2) ≤ centralizer
          (Z d.radical a' ⊓ Q d.radical (alpha d.radical) : Set (FreeAmalgam d.radical))) :
    ∃ (E : ((forwardMovedSpan d.radical (p.walk.getVert 2)) ⧸
          center (forwardMovedSpan d.radical (p.walk.getVert 2))) ≃*
        Multiplicative (BinaryPermutation.natural (Fin 6)))
      (τ : Equiv.Perm (Fin 6) ≃* Equiv.Perm (Fin 6)),
      (∀ (m : d.overgroup) (x : forwardMovedSpan d.radical (p.walk.getVert 2)),
        (E (QuotientGroup.mk' _ (forwardMovedSpanAction d.radical (p.walk.getVert 2) m x))).toAdd =
          BinaryPermutation.naturalRepresentation (Fin 6)
            (τ (SourceReduction.projection h e hz hn d m))
            (E (QuotientGroup.mk' _ x)).toAdd) ∧
      (center (forwardMovedSpan d.radical (p.walk.getVert 2))).index = 16 ∧
      Nat.card (⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
        localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
      ∀ A : Subgroup (FreeAmalgam d.radical), A ≤ localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) →
        A.relIndex (localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)) ≤ 2 →
        ⁅A,A⁆ = ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  exact selected_natural_quotient_and_transfer_knownSimple
    (e := e) (hz := hz) (hn := hn) hb2 p hsmall hnonabelian hfixed
    (selected_span_index_of_forward_slice s hc hb2 p hslice).2
    (selected_span_endpoint_commutator_of_kernel_fixed s hc hb p hsmall hkernel)

/-- Actual terminal application with its selected-span index and endpoint
commutator supplied by the source forward slice and fixed critical kernel.
The remaining source premises stay explicit for final assembly. -/
theorem selected_natural_terminal_false_of_forward_slice_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : replacementDistance h d = 4)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hnonabelian : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥)
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hfixed : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≤
      centralizer (Ltilde d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)))
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2)
    (hkernel : localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊓
        Q d.radical (p.walk.getVert 2) ≤ centralizer
          (Z d.radical a' ⊓ Q d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)))
    (hCcard : Nat.card (⁅⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆,
      ⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆⁆ :
        Subgroup (FreeAmalgam d.radical)) ≤ 2)
    (hcross : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊓
      Q d.radical (p.walk.getVert 2),
      ⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆⁆ ≤
      ⁅⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆,
        ⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆⁆) : False := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  exact selected_natural_terminal_false_knownSimple
    (e := e) (hz := hz) (hn := hn) hb2 p hnonabelian hsmall hfixed
    (selected_span_index_of_forward_slice s hc hb2 p hslice).2
    (selected_span_endpoint_commutator_of_kernel_fixed s hc hb p hsmall hkernel)
    hCcard hcross

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
