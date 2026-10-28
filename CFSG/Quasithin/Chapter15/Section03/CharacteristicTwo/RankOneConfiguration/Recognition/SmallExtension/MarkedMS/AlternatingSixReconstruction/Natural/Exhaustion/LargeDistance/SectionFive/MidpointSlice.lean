module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SelectedCoreMovement
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.ForwardKernelLine

/-!
# Midpoint slices and the whole common-kernel endpoint action

For a critical path of length four, suppose its two endpoints are conjugate
in the midpoint stabilizer. The midpoint Baumann slice of the last seed
lies in the product of the starting and midpoint seeds: this product is
normalized by the midpoint component and its incident edge kernel. If the
opposite moving-layer slice has index at most two, the full seed slice is
exactly the reverse critical kernel. Both critical seed indices are two.

Consequently the whole common two-kernel fixes the reverse critical kernel.
The full-cover pointwise-fixer theorem places its endpoint commutator in the
original critical line. The starting seed supplies the reverse inclusion,
so these commutators are equal. Both cover orders and the central attachment
are retained; no natural subgroup or full point-radical image is assumed.

On the conjugate path obtained from a nonabelian selected span, the same
conjugator transports the original slice bound and fixes the midpoint.
The application retains all three intermediate vertices and gives the
actual order-two common-kernel commutator. The final two applications
remove the separate fixed-kernel premise from the selected natural quotient
and the endpoint-action premise from the whole-core supplement and derived
equality. Source slice selection, nonabelianness, derived fixedness and the
core index are still required where stated. This does not establish either
terminal distance contradiction.

Source: MS93 (5.12), printed pp.925--927, and (3.10), pp.879--881.
The slice-normalization argument adapts the existing
SymplecticSetup.ForwardCoreEndpoint proof to the original full central covers;
SmallKernel supplies the pointwise fixer without the native full-point
restriction. The remaining source-selected paths, strict radius bounds,
R4/R6 noncentrality and terminal assembly belong to
qt-e-ms-small-a6-exhaustion-large-distance. Final unconditional reconstruction
remains with qt-e-ms-small-a6-reconstruction.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
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

private theorem normalizes_join_of_displacement {G : Type*} [Group G]
    (N H K : Subgroup G) (hn : K≤normalizer (N:Set G))
    (hcomm : ⁅K,H⁆≤N) : K≤normalizer ((N⊔H:Subgroup G):Set G) := by
  apply le_normalizer_iff.mpr
  intro k hk x hx
  have hm : (N⊔H).map (MulAut.conj k).toMonoidHom≤N⊔H := by
    rw [Subgroup.map_sup]
    refine sup_le ((mem_normalizer_iff_map_conj_eq.mp (hn hk)).le.trans le_sup_left) ?_
    rintro _ ⟨y,hy,rfl⟩
    have hh := (N⊔H).mul_mem
      (mem_sup_left (hcomm (commutator_mem_commutator hk hy))) (mem_sup_right hy)
    simpa [MulAut.conj_apply,commutatorElement_def,mul_assoc] using hh
  exact hm (mem_map_of_mem (MulAut.conj k).toMonoidHom hx)

private theorem relIndex_sup_of_normalized {G : Type*} [Group G]
    (B A : Subgroup G) (hn : A≤normalizer (B:Set G)) :
    B.relIndex (B⊔A)=B.relIndex A := by
  let J := B⊔A
  let : (B.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer (sup_le B.le_normalizer hn)
  have hi := relIndex_sup_left (A.subgroupOf J) (B.subgroupOf J)
  rw [←subgroupOf_sup le_sup_left le_sup_right,relIndex_subgroupOf le_rfl,
    relIndex_subgroupOf le_sup_right] at hi
  exact hi

private theorem inf_eq_fixed_of_small_index {G : Type*} [Group G]
    (Z B A : Subgroup G) [Finite Z]
    (hBC : Z⊓B≤centralizer (A:Set G))
    (hne : ¬ Z≤centralizer (A:Set G)) (hi : B.relIndex Z≤2) :
    Z⊓B=Z⊓centralizer (A:Set G) := by
  let E := Z⊓B
  let F := Z⊓centralizer (A:Set G)
  have hEF : E≤F := le_inf inf_le_left hBC
  have hF : 1<F.relIndex Z := by
    have hp : 0<F.relIndex Z := Nat.pos_of_ne_zero index_ne_zero_of_finite
    have hn : F.relIndex Z≠1 := by
      intro he
      exact hne ((relIndex_eq_one.mp he).trans inf_le_right)
    omega
  have hm := relIndex_mul_relIndex E F Z hEF inf_le_left
  have hE : E.relIndex Z≤2 := by simpa only [E,inf_relIndex_left] using hi
  let : Finite F := Finite.of_injective (inclusion (show F≤Z from inf_le_left)) (inclusion_injective _)
  have hpEF : 0<E.relIndex F := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hEF1 : E.relIndex F=1 := by nlinarith
  exact le_antisymm hEF (relIndex_eq_one.mp hEF1)

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
/-- A seed orbit transports its Baumann slice inside the two-seed product. -/
theorem midpoint_conjugate_seed_slice_le
    (hb : 2<replacementDistance h d) {a c t : Vertex d.radical}
    (hc : color d.radical c=false) (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (g : FreeAmalgam d.radical) (hg : g∈stabilizer d.radical c) :
    Z d.radical (act d.radical g a)⊓B d.radical c ((replacementGeometry h d).Z_normal _)≤Z d.radical a⊔Z d.radical c := by
  let D := Z d.radical a⊓B d.radical c ((replacementGeometry h d).Z_normal _)
  let H := Z d.radical c⊔D
  have hLc : Ltilde d.radical c≤normalizer (H:Set (FreeAmalgam d.radical)) := by
    apply normalizes_join_of_displacement
    · exact (Ltilde_le_stabilizer c).trans (Z_normalized d.radical c)
    · apply commutator_le.mpr
      intro l hl z hz
      exact ((mem_B_iff d.radical c _ (((replacementGeometry h d).V_le_Q hb c hc).trans (fun _ hx => hx.1)) z).mp hz.2).2 l hl
  have htGa : Q d.radical t≤stabilizer d.radical a := fun _ hx => hx.2 _ (adjacent_symm d.radical hat)
  have htGc : Q d.radical t≤stabilizer d.radical c := fun _ hx => hx.2 _ (adjacent_symm d.radical hct)
  have hBn := Escape.Propagation.Rigidity.B_normalized (geometry:=(replacementGeometry h d)) hb c hc
  have hD : Q d.radical t≤normalizer (D:Set (FreeAmalgam d.radical)) := by
    intro x hx
    rw [mem_normalizer_iff_map_conj_eq]
    dsimp only [D]
    rw [Subgroup.map_inf _ _ _ (MulAut.conj x).injective,
      mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical a (htGa hx)),
      mem_normalizer_iff_map_conj_eq.mp (hBn (htGc hx))]
  have hGn : stabilizer d.radical c≤normalizer (H:Set (FreeAmalgam d.radical)) := by
    rw [←core_residual_edge_generation (h := h) hc hct]
    exact sup_le hLc ((le_inf (htGc.trans (Z_normalized d.radical c)) hD).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _))
  have hmap : D.map (MulAut.conj g⁻¹).toMonoidHom=
      Z d.radical (act d.radical g a)⊓B d.radical c ((replacementGeometry h d).Z_normal _) := by
    dsimp only [D]
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective,←Z_act,
      MulEquiv.toMonoidHom_eq_coe,
      mem_normalizer_iff_map_conj_eq.mp (hBn ((stabilizer d.radical c).inv_mem hg))]
  rw [←hmap]
  apply le_trans (map_mono (show D≤H from le_sup_right))
  rw [MulEquiv.toMonoidHom_eq_coe,mem_normalizer_iff_map_conj_eq.mp (hGn ((stabilizer d.radical c).inv_mem hg))]
  exact sup_le le_sup_right (inf_le_left.trans le_sup_left)


include s in
/-- A small opposite Baumann slice on a midpoint conjugate is the entire
reverse critical kernel. Both critical indices are two, and the full kernel
lies in the product of the two inner seeds. -/
theorem midpoint_slice_eq_reverse_kernel
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical (p.walk.getVert 2))
    (he : act d.radical g a = a')
    (hindex : (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical a') ≤ 2) :
    Z d.radical a' ⊓ B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _) =
        Z d.radical a' ⊓ Q d.radical a ∧
      Z d.radical a' ⊓ Q d.radical a ≤
        Z d.radical a ⊔ Z d.radical (p.walk.getVert 2) ∧
      (Q d.radical a').relIndex (Z d.radical a) = 2 ∧
      (Q d.radical a).relIndex (Z d.radical a') = 2 := by
  let c := p.walk.getVert 2
  let Bc := B d.radical c ((replacementGeometry h d).Z_normal _)
  have hl : p.walk.length=4 := p.length_eq_b.trans hb
  have hb2 : 2<replacementDistance h d := by omega
  have hcol : color d.radical c=false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i:=0) (by omega)
  have hct : Adjacent d.radical c (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i:=1) (by omega)))
  have hce : (cosetGraph d.radical).dist c a'=2 := by
    simpa only [c,hl,Nat.reduceSub] using p.dist_end 2
  have hZeGc : Z d.radical a'≤stabilizer d.radical c := Z_le_stabilizer_of_dist_le a' _ (by
    rw [(replacementGeometry h d).distance_constant a' p.end_color,SimpleGraph.dist_comm,hce]
    change 2≤replacementDistance h d
    omega)
  have hBslice : Z d.radical a'⊓Bc≤Z d.radical a⊔Z d.radical c := by
    rw [←he]
    exact midpoint_conjugate_seed_slice_le (h := h) hb2 hcol hat hct g hg
  have hBC : Z d.radical a'⊓Bc≤centralizer (Z d.radical a:Set (FreeAmalgam d.radical)) := by
    apply le_centralizer_iff.mpr
    apply (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a p.start_color)).trans
    apply centralizer_le
    apply hBslice.trans (sup_le _ _)
    · exact (Z_le_VBall d.radical a 2).trans ((replacementGeometry h d).V_le_Q hb2 _ p.start_color)
    · apply Z_le_Q_of_dist_lt d.radical c ((replacementGeometry h d).exists_critical c hcol)
      rw [(replacementGeometry h d).distance_constant c hcol,SimpleGraph.dist_comm]
      change (cosetGraph d.radical).dist a (p.walk.getVert 2)<replacementDistance h d
      rw [p.dist_start (by omega)]
      omega
  have hlast : Adjacent d.radical a' (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have hlastc : Adjacent d.radical c (p.walk.getVert (p.walk.length-1)) := by
    simpa only [c,hl,Nat.reduceSub] using
      ((cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i:=2) (by omega)))
  have hseedB : Z d.radical (p.walk.getVert (p.walk.length-1))≤Bc :=
    (adjacent_Z_le d.radical hcol hlastc).trans (Escape.EdgeTransfer.Z_le_B hb2 c hcol)
  have hZeSup : Z d.radical a'≤Bc⊔U d.radical a' := by
    rw [DistanceTwo.CentralLayer.Z_eq_moving_sup_edge_at h e hz d p.end_color hlast]
    exact sup_le le_sup_right (hseedB.trans le_sup_left)
  have hBn : stabilizer d.radical c≤normalizer (Bc:Set (FreeAmalgam d.radical)) :=
    Escape.Propagation.Rigidity.B_normalized hb2 c hcol
  have hUG : U d.radical a'≤stabilizer d.radical c := (DistanceEight.U_le_Z d.radical a').trans hZeGc
  have hBG : Bc≤stabilizer d.radical c := by
    intro x hx
    exact (((replacementGeometry h d).V_le_Q hb2 c hcol).trans (fun _ hx => hx.1))
      (((mem_B_iff d.radical c _ (((replacementGeometry h d).V_le_Q hb2 c hcol).trans (fun _ hx => hx.1)) x).mp hx).1)
  let := finite_stabilizer d.radical c
  let : Finite (Bc⊔U d.radical a':Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion (sup_le hBG hUG)) (inclusion_injective _)
  let : Finite (Z d.radical a') := Finite.of_injective (inclusion hZeGc) (inclusion_injective _)
  let : Finite (U d.radical a') := Finite.of_injective (inclusion hUG) (inclusion_injective _)
  have hZi : Bc.relIndex (Z d.radical a')≤2 := by
    calc
      _≤Bc.relIndex (Bc⊔U d.radical a') := relIndex_le_of_le_right hZeSup index_ne_zero_of_finite
      _=Bc.relIndex (U d.radical a') := relIndex_sup_of_normalized _ _ (hUG.trans hBn)
      _≤2 := hindex
  have hne : ¬ Z d.radical a'≤centralizer (Z d.radical a:Set (FreeAmalgam d.radical)) := by
    intro hn
    apply p.critical.2
    rw [←C_eq_Q s hc a' p.end_color]
    exact le_inf (Z_le_stabilizer_of_dist_le a _ p.critical.1.le)
      (le_centralizer_iff.mp hn)
  have hfixeq := inf_eq_fixed_of_small_index (Z d.radical a') Bc (Z d.radical a) hBC hne hZi
  have hkernel : Z d.radical a' ⊓ centralizer
      (Z d.radical a : Set (FreeAmalgam d.radical)) =
        Z d.radical a' ⊓ Q d.radical a := by
    apply le_antisymm
    · exact le_inf inf_le_left (by
        rw [←C_eq_Q s hc a p.start_color]
        exact le_inf (inf_le_left.trans (critical_Z_le_stabilizer d.radical
          (replacementGeometry h d) a p.start_color (by
            rw [(replacementGeometry h d).distance_constant a p.start_color]
            exact replacementDistance_pos h d) p.critical)) inf_le_right)
    · exact inf_le_inf_left _ (le_centralizer_iff.mp
        (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a p.start_color)))
  have hslice : Z d.radical a' ⊓ Bc = Z d.radical a' ⊓ Q d.radical a :=
    hfixeq.trans hkernel
  have hsmall : (Q d.radical a).relIndex (Z d.radical a') < 4 := by
    have hi := hZi
    rw [←inf_relIndex_left,hslice,inf_relIndex_left] at hi
    omega
  let q := CriticalPath.ofPair (geometry := replacementGeometry h d) p.end_color
    (critical_reverse_pair s hc p)
  have hi := small_critical_indices s hc q hsmall
  exact ⟨hslice,hslice ▸ hBslice,hi.2,hi.1⟩

include s in
/-- On the same midpoint-selected path, the entire common two-kernel fixes
the reverse critical kernel and acts on the endpoint through the actual
critical commutator line. No full point-radical image is required. -/
theorem midpoint_common_kernel_endpoint_commutator
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical (p.walk.getVert 2))
    (he : act d.radical g a = a')
    (hindex : (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical a') ≤ 2) :
    Q d.radical a ⊓ Q d.radical (p.walk.getVert 2) ≤ centralizer
        (Z d.radical a' ⊓ Q d.radical a : Set (FreeAmalgam d.radical)) ∧
      ⁅Q d.radical a ⊓ Q d.radical (p.walk.getVert 2),Z d.radical a'⁆ =
        ⁅Z d.radical a,Z d.radical a'⁆ := by
  have hs := midpoint_slice_eq_reverse_kernel s hc hb p g hg he hindex
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hcol : color d.radical (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  let D := Q d.radical a ⊓ Q d.radical (p.walk.getVert 2)
  have hDC : D ≤ centralizer
      ((Z d.radical a ⊔ Z d.radical (p.walk.getVert 2) : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
    apply le_centralizer_iff.mpr
    exact sup_le
      ((commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a p.start_color)).trans
        (centralizer_le (show D ≤ Q d.radical a from inf_le_left)))
      ((commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical _ hcol)).trans
        (centralizer_le (show D ≤ Q d.radical (p.walk.getVert 2) from inf_le_right)))
  have hfix := hDC.trans (centralizer_le hs.2.1)
  have hb2 : 2 < replacementDistance h d := by omega
  have hZaQ : Z d.radical a ≤ Q d.radical a :=
    (Z_le_VBall d.radical a 2).trans ((replacementGeometry h d).V_le_Q hb2 a p.start_color)
  have hZaQc : Z d.radical a ≤ Q d.radical (p.walk.getVert 2) := by
    apply Z_le_Q_of_dist_lt d.radical a ((replacementGeometry h d).exists_critical a p.start_color)
    rw [(replacementGeometry h d).distance_constant a p.start_color,p.dist_start (by omega)]
    change 2 < replacementDistance h d
    exact hb2
  refine ⟨hfix,le_antisymm
    (small_critical_kernel_commutator s hc p (by rw [hs.2.2.1]; decide) D ?_ hfix)
    (commutator_mono (le_inf hZaQ hZaQc) le_rfl)⟩
  have hct : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 3) :=
    (cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have het : Adjacent d.radical a' (p.walk.getVert 3) := by
    have hh := p.walk.adj_getVert_succ (i := 3) (by omega)
    rw [show 3 + 1 = p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have ht : color d.radical (p.walk.getVert 3) = true := by
    have hh := adjacent_color_ne d.radical hct
    rw [hcol] at hh
    cases hx : color d.radical (p.walk.getVert 3) <;> simp_all
  exact (inf_le_right.trans (Q_le_adjacent_h d.radical ht hct)).trans
    (fun _ hx => hx.2 _ (adjacent_symm d.radical het))

/-- A nonabelian selected span supplies an actual conjugate critical path.
The original forward slice transports through its same conjugator, giving
both critical indices and the exact common-kernel commutator on that path. -/
theorem selected_span_conjugate_path_kernel_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hnonabelian : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥)
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2) :
    replacementDistance h d = 4 ∧
      ∃ x ∈ stabilizer d.radical (alpha d.radical),
        ∃ q : CriticalPath d.radical (replacementGeometry h d)
            (p.walk.getVert 2) (act d.radical x (p.walk.getVert 2)),
          q.walk.getVert 1 = p.walk.getVert 1 ∧
          q.walk.getVert 2 = alpha d.radical ∧
          q.walk.getVert 3 = act d.radical x (p.walk.getVert 1) ∧
          (Q d.radical (act d.radical x (p.walk.getVert 2))).relIndex
            (Z d.radical (p.walk.getVert 2)) = 2 ∧
          (Q d.radical (p.walk.getVert 2)).relIndex
            (Z d.radical (act d.radical x (p.walk.getVert 2))) = 2 ∧
          ⁅Q d.radical (p.walk.getVert 2) ⊓ Q d.radical (alpha d.radical),
              Z d.radical (act d.radical x (p.walk.getVert 2))⁆ =
            ⁅Z d.radical (p.walk.getVert 2),Z d.radical (act d.radical x (p.walk.getVert 2))⁆ ∧
          Nat.card (⁅Q d.radical (p.walk.getVert 2) ⊓ Q d.radical (alpha d.radical),
              Z d.radical (act d.radical x (p.walk.getVert 2))⁆ : Subgroup (FreeAmalgam d.radical)) = 2 := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨hb4,x,hx,q,hq1,hq2,hq3⟩ := selected_span_conjugate_critical_path (h := h) hb p hnonabelian
  have hxq : x ∈ stabilizer d.radical (q.walk.getVert 2) := hq2.symm ▸ hx
  have hBn := Escape.Propagation.Rigidity.B_normalized
    (geometry := replacementGeometry h d) hb (alpha d.radical) rfl
  have hBm : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj x⁻¹).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (hBn ((stabilizer d.radical (alpha d.radical)).inv_mem hx))
  have hi : (B d.radical (q.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (act d.radical x (p.walk.getVert 2))) ≤ 2 := by
    rw [hq2,U_act,←hBm,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hslice
  have hbounds := midpoint_slice_eq_reverse_kernel s hc hb4 q x hxq rfl hi
  have hcomm := (midpoint_common_kernel_endpoint_commutator s hc hb4 q x hxq rfl hi).2
  rw [hq2] at hcomm
  refine ⟨hb4,x,hx,q,hq1,hq2,hq3,hbounds.2.2.1,hbounds.2.2.2,hcomm,?_⟩
  rw [hcomm]
  exact small_critical_commutator_card s hc q (by rw [hbounds.2.2.1]; decide)

/-- The actual midpoint orbit and the two Baumann slice bounds discharge the
critical-index and fixed-kernel premises of the selected natural quotient.
Nonabelianness and fixedness of the selected derived subgroup remain explicit. -/
theorem selected_natural_quotient_and_transfer_of_midpoint_slices_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : replacementDistance h d = 4)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hnonabelian : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥)
    (hfixed : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≤
      centralizer (Ltilde d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)))
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2)
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical (p.walk.getVert 2))
    (he : act d.radical g (alpha d.radical) = a')
    (hopposite : (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical a') ≤ 2) :
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
  have hi := (midpoint_slice_eq_reverse_kernel s hc hb p g hg he hopposite).2.2.1
  have hk := (midpoint_common_kernel_endpoint_commutator s hc hb p g hg he hopposite).1
  have hPQ := (selected_span_le_forward_kernel (h := h) hb2 p).trans inf_le_left
  exact selected_natural_quotient_and_transfer_of_forward_slice_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p (by omega) hnonabelian hfixed hslice
    ((inf_le_inf_right _ hPQ).trans hk)

/-- Application to the whole original core: the midpoint slice supplies its
endpoint bound, so the supplement and derived equality retain only the core
index, selected-span nonabelianness, and the geometric orbit and slice inputs. -/
theorem selected_core_supplement_of_midpoint_slice_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : replacementDistance h d = 4)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hnonabelian : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥)
    (hindex : (Q d.radical (p.walk.getVert 2)).relIndex
      ⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆ ≤ 2)
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical (p.walk.getVert 2))
    (he : act d.radical g (alpha d.radical) = a')
    (hopposite : (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical a') ≤ 2) :
    let C := ⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆
    let W := forwardMovedSpan d.radical (p.walk.getVert 2)
    C ≤ Z d.radical (alpha d.radical) ⊔ W ∧ ⁅C,C⁆ = ⁅W,W⁆ := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hi := (midpoint_slice_eq_reverse_kernel s hc hb p g hg he hopposite).2.2.1
  have hk := (midpoint_common_kernel_endpoint_commutator s hc hb p g hg he hopposite).2.le
  have hCQ : ⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆ ≤
      Q d.radical (alpha d.radical) :=
    le_normalizer_iff_commutator_le_left.mp
      ((Ltilde_le_stabilizer _).trans (Q_normalized d.radical _))
  have hactor := (commutator_mono (inf_le_inf_right _ hCQ) le_rfl).trans hk
  exact selected_core_supplement_knownSimple_of_nonabelian
    (e := e) (hz := hz) (hn := hn) hb2 p (by omega) hnonabelian hindex
    (hactor.trans (((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans
      (DistanceEight.U_le_Z d.radical _)))

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
