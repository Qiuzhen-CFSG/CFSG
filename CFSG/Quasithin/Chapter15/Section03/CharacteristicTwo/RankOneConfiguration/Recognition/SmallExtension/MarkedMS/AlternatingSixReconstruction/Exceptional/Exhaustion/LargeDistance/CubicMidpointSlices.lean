module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicForwardClosure

/-!
# Midpoint kernels on the original cubic graph

A nonabelian selected orbit span has two noncommuting conjugate seeds.
The walk through the original first edge and base vertex has length four;
minimality of the critical distance makes it an actual critical path.
Thus all selected spans are abelian above distance four.

At distance four, conjugating an endpoint about the midpoint puts its
Baumann slice in the two-seed product. If the opposite moving-cover slice
has index at most two, this full seed slice is exactly the reverse critical
kernel. The proof uses the literal seed-centralizer intersection with Q;
it never identifies the full centralizer E with Q. The whole common
two-kernel consequently fixes the reverse critical kernel, and its endpoint
commutator equals the original critical line.

For the constructed conjugate path the same conjugator transports the
slice bound and every intermediate vertex. In the small nonabelian branch,
the common-kernel commutator is the entire derived subgroup of the selected
span. It has order two, is central at the original base, and is disjoint
from the stabilizer center at the second vertex. Both full moving covers
and the cubic kernel remain intact.

The whole-core and literal C.1.32 consumers retain the abelian-span branch,
strict slice selection, remaining edge-image choices, R4/R6 and distance-four
exclusions. These lemmas supply the midpoint fixed-kernel and endpoint-action
premises used in the last paragraph of MS93 (5.12); they do not prove (5.11)
or (5.12). Final assembly remains with qt-e-ms-small-a6-reconstruction,
including discharge of natural exhaustion from its independent owner
qt-e-ms-small-a6-exhaustion-large-distance.

Source: Meierfrankenfeld--Stellmacher (1993), (5.9), pp.920--922,
and (5.12), pp.925--927. Adapts the selected-conjugate and midpoint proofs
in Natural.Exhaustion.LargeDistance.SectionFive.SelectedSpan and
MidpointSlice, using the original cubic action and full-cover fixer.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "W" => (⁅centralOmega L R,L.subgroupOf (L ⊔ R)⁆ : Subgroup M)
local notation "Rg" => edge L R
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
private theorem core_residual_edge_generation {a t : Vertex Rg}
    (ha : color Rg a = false) (hat : Adjacent Rg a t) :
    Ltilde Rg a ⊔ Q Rg t = stabilizer Rg a := by
  apply CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.local_residual_edge_generation Rg
  · rw [h.relative_residual]
    exact (codisjoint_subgroupOf_sup L R).eq_top
  · exact ha
  · exact hat

include h e in
private theorem reverse_pair {a c : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a c) :
    CriticalPair Rg c a ((sourceGeometry h).exists_critical c p.end_color) :=
  critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
    a p.start_color (by rw [(sourceGeometry h).distance_constant a p.start_color]; exact sourceDistance_pos h)
    c p.end_color p.critical

omit hk in
include h e hz in
private theorem vertex_seed_eq_moving_sup_edge {c b : Vertex Rg}
    (hc : color Rg c = false) (hcb : Adjacent Rg c b) :
    Z Rg c = U Rg c ⊔ Z Rg b := by
  obtain ⟨g,hg | hg⟩ := (adjacent_iff_exists_common Rg c b).mp hcb
  · rcases hg with ⟨rfl,rfl⟩
    have hb := CubicAction.graph_Z_eq_moved_sup_edge h e hz (base_adjacent Rg)
    rw [graph_U_map h e hz] at hb
    have he := congrArg (fun A : Subgroup (FreeAmalgam Rg) =>
      A.map (MulAut.conj g⁻¹).toMonoidHom) hb
    rw [Subgroup.map_sup,←Z_act,←U_act,←Z_act] at he
    simpa [alpha,beta] using he
  · rw [hg.1] at hc
    cases hc


include h in
/-- A seed orbit transports its Baumann slice inside the two-seed product. -/
theorem midpoint_conjugate_seed_slice_le
    (hb : 2<sourceDistance h) {a c t : Vertex Rg}
    (hc : color Rg c=false) (hat : Adjacent Rg a t) (hct : Adjacent Rg c t)
    (g : FreeAmalgam Rg) (hg : g∈stabilizer Rg c) :
    Z Rg (act Rg g a)⊓B Rg c ((sourceGeometry h).Z_normal _)≤Z Rg a⊔Z Rg c := by
  let D := Z Rg a⊓B Rg c ((sourceGeometry h).Z_normal _)
  let H := Z Rg c⊔D
  have hLc : Ltilde Rg c≤normalizer (H:Set (FreeAmalgam Rg)) := by
    apply normalizes_join_of_displacement
    · exact (Ltilde_le_stabilizer c).trans (Z_normalized Rg c)
    · apply commutator_le.mpr
      intro l hl z hz
      exact ((mem_B_iff Rg c _ (((sourceGeometry h).V_le_Q hb c hc).trans (fun _ hx => hx.1)) z).mp hz.2).2 l hl
  have htGa : Q Rg t≤stabilizer Rg a := fun _ hx => hx.2 _ (adjacent_symm Rg hat)
  have htGc : Q Rg t≤stabilizer Rg c := fun _ hx => hx.2 _ (adjacent_symm Rg hct)
  have hBn := Escape.Propagation.Rigidity.B_normalized (geometry:=(sourceGeometry h)) hb c hc
  have hD : Q Rg t≤normalizer (D:Set (FreeAmalgam Rg)) := by
    intro x hx
    rw [mem_normalizer_iff_map_conj_eq]
    dsimp only [D]
    rw [Subgroup.map_inf _ _ _ (MulAut.conj x).injective,
      mem_normalizer_iff_map_conj_eq.mp (Z_normalized Rg a (htGa hx)),
      mem_normalizer_iff_map_conj_eq.mp (hBn (htGc hx))]
  have hGn : stabilizer Rg c≤normalizer (H:Set (FreeAmalgam Rg)) := by
    rw [←core_residual_edge_generation h hc hct]
    exact sup_le hLc ((le_inf (htGc.trans (Z_normalized Rg c)) hD).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _))
  have hmap : D.map (MulAut.conj g⁻¹).toMonoidHom=
      Z Rg (act Rg g a)⊓B Rg c ((sourceGeometry h).Z_normal _) := by
    dsimp only [D]
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective,←Z_act,
      MulEquiv.toMonoidHom_eq_coe,
      mem_normalizer_iff_map_conj_eq.mp (hBn ((stabilizer Rg c).inv_mem hg))]
  rw [←hmap]
  apply le_trans (map_mono (show D≤H from le_sup_right))
  rw [MulEquiv.toMonoidHom_eq_coe,mem_normalizer_iff_map_conj_eq.mp (hGn ((stabilizer Rg c).inv_mem hg))]
  exact sup_le le_sup_right (inf_le_left.trans le_sup_left)


include h e hz hk in
/-- A small opposite Baumann slice on a midpoint conjugate is the entire
reverse critical kernel. Both critical indices are two, and the full kernel
lies in the product of the two inner seeds. -/
theorem midpoint_slice_eq_reverse_kernel
    (hb : sourceDistance h = 4)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (g : FreeAmalgam Rg) (hg : g ∈ stabilizer Rg (p.walk.getVert 2))
    (he : act Rg g a = a')
    (hindex : (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg a') ≤ 2) :
    Z Rg a' ⊓ B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _) =
        Z Rg a' ⊓ Q Rg a ∧
      Z Rg a' ⊓ Q Rg a ≤
        Z Rg a ⊔ Z Rg (p.walk.getVert 2) ∧
      (Q Rg a').relIndex (Z Rg a) = 2 ∧
      (Q Rg a).relIndex (Z Rg a') = 2 := by
  let c := p.walk.getVert 2
  let Bc := B Rg c ((sourceGeometry h).Z_normal _)
  have hl : p.walk.length=4 := p.length_eq_b.trans hb
  have hb2 : 2<sourceDistance h := by omega
  have hcol : color Rg c=false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent Rg a (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i:=0) (by omega)
  have hct : Adjacent Rg c (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i:=1) (by omega)))
  have hce : (cosetGraph Rg).dist c a'=2 := by
    simpa only [c,hl,Nat.reduceSub] using p.dist_end 2
  have hZeGc : Z Rg a'≤stabilizer Rg c := Z_le_stabilizer_of_dist_le a' _ (by
    rw [(sourceGeometry h).distance_constant a' p.end_color,SimpleGraph.dist_comm,hce]
    change 2≤sourceDistance h
    omega)
  have hBslice : Z Rg a'⊓Bc≤Z Rg a⊔Z Rg c := by
    rw [←he]
    exact midpoint_conjugate_seed_slice_le h hb2 hcol hat hct g hg
  have hBC : Z Rg a'⊓Bc≤centralizer (Z Rg a:Set (FreeAmalgam Rg)) := by
    apply le_centralizer_iff.mpr
    apply (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg a p.start_color)).trans
    apply centralizer_le
    apply hBslice.trans (sup_le _ _)
    · exact (Z_le_VBall Rg a 2).trans ((sourceGeometry h).V_le_Q hb2 _ p.start_color)
    · apply Z_le_Q_of_dist_lt Rg c ((sourceGeometry h).exists_critical c hcol)
      rw [(sourceGeometry h).distance_constant c hcol,SimpleGraph.dist_comm]
      change (cosetGraph Rg).dist a (p.walk.getVert 2)<sourceDistance h
      rw [p.dist_start (by omega)]
      omega
  have hlast : Adjacent Rg a' (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have hlastc : Adjacent Rg c (p.walk.getVert (p.walk.length-1)) := by
    simpa only [c,hl,Nat.reduceSub] using
      ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i:=2) (by omega)))
  have hseedB : Z Rg (p.walk.getVert (p.walk.length-1))≤Bc :=
    (adjacent_Z_le Rg hcol hlastc).trans (Escape.EdgeTransfer.Z_le_B hb2 c hcol)
  have hZeSup : Z Rg a'≤Bc⊔U Rg a' := by
    rw [vertex_seed_eq_moving_sup_edge h e hz p.end_color hlast]
    exact sup_le le_sup_right (hseedB.trans le_sup_left)
  have hBn : stabilizer Rg c≤normalizer (Bc:Set (FreeAmalgam Rg)) :=
    Escape.Propagation.Rigidity.B_normalized hb2 c hcol
  have hUG : U Rg a'≤stabilizer Rg c := (DistanceEight.U_le_Z Rg a').trans hZeGc
  have hBG : Bc≤stabilizer Rg c := by
    intro x hx
    exact (((sourceGeometry h).V_le_Q hb2 c hcol).trans (fun _ hx => hx.1))
      (((mem_B_iff Rg c _ (((sourceGeometry h).V_le_Q hb2 c hcol).trans (fun _ hx => hx.1)) x).mp hx).1)
  let := finite_stabilizer Rg c
  let : Finite (Bc⊔U Rg a':Subgroup (FreeAmalgam Rg)) :=
    Finite.of_injective (inclusion (sup_le hBG hUG)) (inclusion_injective _)
  let : Finite (Z Rg a') := Finite.of_injective (inclusion hZeGc) (inclusion_injective _)
  let : Finite (U Rg a') := Finite.of_injective (inclusion hUG) (inclusion_injective _)
  have hZi : Bc.relIndex (Z Rg a')≤2 := by
    calc
      _≤Bc.relIndex (Bc⊔U Rg a') := relIndex_le_of_le_right hZeSup index_ne_zero_of_finite
      _=Bc.relIndex (U Rg a') := relIndex_sup_of_normalized _ _ (hUG.trans hBn)
      _≤2 := hindex
  have hne : ¬ Z Rg a'≤centralizer (Z Rg a:Set (FreeAmalgam Rg)) := by
    intro hn
    have hh : Z Rg a ≤ Q Rg a' := by
      intro z hz
      exact ((critical_seed_centralizer_intersection h e p) ▸
        (show z ∈ Z Rg a ⊓ centralizer (Z Rg a' : Set (FreeAmalgam Rg)) from
          ⟨hz,le_centralizer_iff.mp hn hz⟩)).2
    exact p.critical.2 hh
  have hfixeq := inf_eq_fixed_of_small_index (Z Rg a') Bc (Z Rg a) hBC hne hZi
  let q := CriticalPath.ofPair (geometry := sourceGeometry h) p.end_color (reverse_pair h e p)
  have hkernel : Z Rg a' ⊓ centralizer
      (Z Rg a : Set (FreeAmalgam Rg)) = Z Rg a' ⊓ Q Rg a :=
    critical_seed_centralizer_intersection h e q
  have hslice : Z Rg a' ⊓ Bc = Z Rg a' ⊓ Q Rg a :=
    hfixeq.trans hkernel
  have hsmall : (Q Rg a).relIndex (Z Rg a') < 4 := by
    have hi := hZi
    rw [←inf_relIndex_left,hslice,inf_relIndex_left] at hi
    omega
  have hi := small_critical_indices h e hz hk q hsmall
  exact ⟨hslice,hslice ▸ hBslice,hi.2,hi.1⟩

include h e hz hk in
/-- On the same midpoint-selected path, the entire common two-kernel fixes
the reverse critical kernel and acts on the endpoint through the actual
critical commutator line. No full point-radical image is required. -/
theorem midpoint_common_kernel_endpoint_commutator
    (hb : sourceDistance h = 4)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (g : FreeAmalgam Rg) (hg : g ∈ stabilizer Rg (p.walk.getVert 2))
    (he : act Rg g a = a')
    (hindex : (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg a') ≤ 2) :
    Q Rg a ⊓ Q Rg (p.walk.getVert 2) ≤ centralizer
        (Z Rg a' ⊓ Q Rg a : Set (FreeAmalgam Rg)) ∧
      ⁅Q Rg a ⊓ Q Rg (p.walk.getVert 2),Z Rg a'⁆ =
        ⁅Z Rg a,Z Rg a'⁆ := by
  have hs := midpoint_slice_eq_reverse_kernel h e hz hk hb p g hg he hindex
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hcol : color Rg (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  let D := Q Rg a ⊓ Q Rg (p.walk.getVert 2)
  have hDC : D ≤ centralizer
      ((Z Rg a ⊔ Z Rg (p.walk.getVert 2) : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) := by
    apply le_centralizer_iff.mpr
    exact sup_le
      ((commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg a p.start_color)).trans
        (centralizer_le (show D ≤ Q Rg a from inf_le_left)))
      ((commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg _ hcol)).trans
        (centralizer_le (show D ≤ Q Rg (p.walk.getVert 2) from inf_le_right)))
  have hfix := hDC.trans (centralizer_le hs.2.1)
  have hb2 : 2 < sourceDistance h := by omega
  have hZaQ : Z Rg a ≤ Q Rg a :=
    (Z_le_VBall Rg a 2).trans ((sourceGeometry h).V_le_Q hb2 a p.start_color)
  have hZaQc : Z Rg a ≤ Q Rg (p.walk.getVert 2) := by
    apply Z_le_Q_of_dist_lt Rg a ((sourceGeometry h).exists_critical a p.start_color)
    rw [(sourceGeometry h).distance_constant a p.start_color,p.dist_start (by omega)]
    change 2 < sourceDistance h
    exact hb2
  refine ⟨hfix,le_antisymm
    (small_critical_kernel_commutator h e hz hk p (by rw [hs.2.2.1]; decide) D ?_ hfix)
    (commutator_mono (le_inf hZaQ hZaQc) le_rfl)⟩
  have hct : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 3) :=
    (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have het : Adjacent Rg a' (p.walk.getVert 3) := by
    have hh := p.walk.adj_getVert_succ (i := 3) (by omega)
    rw [show 3 + 1 = p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have ht : color Rg (p.walk.getVert 3) = true := by
    have hh := adjacent_color_ne Rg hct
    rw [hcol] at hh
    cases hx : color Rg (p.walk.getVert 3) <;> simp_all
  exact (inf_le_right.trans (Q_le_adjacent_h Rg ht hct)).trans
    (fun _ hx => hx.2 _ (adjacent_symm Rg het))

include h in
/-- A nonabelian selected orbit span supplies a critical conjugate of its
seed. The walk uses the original first edge, passes through the original
base vertex, and then uses its image under the same conjugator. -/
theorem selected_span_conjugate_critical_path
    (hb : 2 < sourceDistance h) {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hnonabelian : ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
      localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≠ ⊥) :
    sourceDistance h = 4 ∧
      ∃ x ∈ stabilizer Rg (alpha Rg),
        ∃ q : CriticalPath Rg (sourceGeometry h)
          (p.walk.getVert 2) (act Rg x (p.walk.getVert 2)),
          q.walk.getVert 1 = p.walk.getVert 1 ∧
          q.walk.getVert 2 = alpha Rg ∧
          q.walk.getVert 3 = act Rg x (p.walk.getVert 1) := by
  classical
  let c := p.walk.getVert 2
  let P := localZSpan Rg c (alpha Rg)
  have hex : ∃ x ∈ stabilizer Rg (alpha Rg),
      ⁅Z Rg c,Z Rg (act Rg x c)⁆ ≠ ⊥ := by
    by_contra! hn
    have hZC : Z Rg c ≤ centralizer (P : Set (FreeAmalgam Rg)) := by
      apply le_centralizer_iff.mpr
      dsimp only [P]
      rw [localZSpan_eq_conjugates]
      apply iSup_le
      intro g
      have hg := le_centralizer_iff.mp
        (commutator_eq_bot_iff_le_centralizer.mp (hn g g.property))
      rwa [Z_act] at hg
    have hPC : P ≤ centralizer (P : Set (FreeAmalgam Rg)) := by
      conv_lhs => dsimp only [P]; rw [localZSpan_eq_conjugates]
      apply iSup_le
      intro g
      have hg := (map_mono (f := (MulAut.conj (g : FreeAmalgam Rg)⁻¹).toMonoidHom)
        hZC).trans (map_centralizer_le_centralizer_image _ _)
      have hnP := mem_normalizer_iff_map_conj_eq.mp
        (localZSpan_normalized Rg c (alpha Rg)
          ((stabilizer Rg (alpha Rg)).inv_mem g.property))
      change P.map (MulAut.conj (g : FreeAmalgam Rg)⁻¹).toMonoidHom = P at hnP
      change (Z Rg c).map (MulAut.conj (g : FreeAmalgam Rg)⁻¹).toMonoidHom ≤
        centralizer ((P.map (MulAut.conj (g : FreeAmalgam Rg)⁻¹).toMonoidHom) : Set (FreeAmalgam Rg)) at hg
      rwa [hnP] at hg
    exact hnonabelian (commutator_eq_bot_iff_le_centralizer.mpr hPC)
  obtain ⟨x,hx,hcomm⟩ := hex
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hc : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hxc : color Rg (act Rg x c) = false := by
    rw [action_preserves_color,hc]
  have hn : ¬ Z Rg c ≤ Q Rg (act Rg x c) := by
    intro hh
    exact hcomm (commutator_eq_bot_iff_le_centralizer.mpr
      (hh.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q Rg _ hxc)))))
  let v := p.walk.take 2
  have hv : v.length = 2 := by
    rw [SimpleGraph.Walk.take_length,inf_eq_left.mpr (by omega)]
  have hfix : act Rg x (alpha Rg) = alpha Rg := hx
  let w := v.reverse.append ((actWalk Rg x v).copy hfix rfl)
  have hw : w.length = 4 := by
    rw [SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_reverse,
      SimpleGraph.Walk.length_copy,actWalk_length,hv]
  have hdist : (cosetGraph Rg).dist c (act Rg x c) ≤ 4 :=
    hw ▸ SimpleGraph.dist_le w
  have hmin := criticalDistance_le Rg c
    ((sourceGeometry h).exists_critical c hc) hn
  rw [(sourceGeometry h).distance_constant c hc] at hmin
  change sourceDistance h ≤ _ at hmin
  have heven := sourceDistance_even h
  rw [Nat.even_iff] at heven
  have hb4 : sourceDistance h = 4 := by omega
  have hd : (cosetGraph Rg).dist c (act Rg x c) =
      sourceDistance h := by omega
  let q : CriticalPath Rg (sourceGeometry h) c (act Rg x c) := {
    start_color := hc
    walk := w
    shortest := hw.trans (hd.trans hb4).symm
    critical := ⟨by rw [(sourceGeometry h).distance_constant c hc]; exact hd,hn⟩ }
  refine ⟨hb4,x,hx,q,?_,?_,?_⟩
  · change w.getVert 1 = _
    simp only [w,SimpleGraph.Walk.getVert_append,SimpleGraph.Walk.length_reverse,hv,
      show (1:ℕ) < 2 by decide,if_pos,SimpleGraph.Walk.getVert_reverse,
      v,SimpleGraph.Walk.take_getVert]
    rfl
  · change w.getVert 2 = _
    simp only [w,SimpleGraph.Walk.getVert_append',SimpleGraph.Walk.length_reverse,hv,
      le_refl,if_pos,SimpleGraph.Walk.getVert_reverse,Nat.sub_self,
      SimpleGraph.Walk.getVert_zero]
  · change w.getVert 3 = _
    simp only [w,SimpleGraph.Walk.getVert_append,SimpleGraph.Walk.length_reverse,hv,
      show ¬ (3:ℕ) < 2 by decide,SimpleGraph.Walk.getVert_copy,actWalk_getVert,
      v,SimpleGraph.Walk.take_getVert]
    rfl

include h e hz hk in
/-- A nonabelian selected span supplies an actual conjugate critical path.
The original forward slice transports through its same conjugator, giving
both critical indices and the exact common-kernel commutator on that path. -/
theorem selected_span_conjugate_path_kernel
    (hb : 2 < sourceDistance h)
    {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hnonabelian : ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
      localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≠ ⊥)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2) :
    sourceDistance h = 4 ∧
      ∃ x ∈ stabilizer Rg (alpha Rg),
        ∃ q : CriticalPath Rg (sourceGeometry h)
            (p.walk.getVert 2) (act Rg x (p.walk.getVert 2)),
          q.walk.getVert 1 = p.walk.getVert 1 ∧
          q.walk.getVert 2 = alpha Rg ∧
          q.walk.getVert 3 = act Rg x (p.walk.getVert 1) ∧
          (Q Rg (act Rg x (p.walk.getVert 2))).relIndex
            (Z Rg (p.walk.getVert 2)) = 2 ∧
          (Q Rg (p.walk.getVert 2)).relIndex
            (Z Rg (act Rg x (p.walk.getVert 2))) = 2 ∧
          ⁅Q Rg (p.walk.getVert 2) ⊓ Q Rg (alpha Rg),
              Z Rg (act Rg x (p.walk.getVert 2))⁆ =
            ⁅Z Rg (p.walk.getVert 2),Z Rg (act Rg x (p.walk.getVert 2))⁆ ∧
          Nat.card (⁅Q Rg (p.walk.getVert 2) ⊓ Q Rg (alpha Rg),
              Z Rg (act Rg x (p.walk.getVert 2))⁆ : Subgroup (FreeAmalgam Rg)) = 2 := by
  obtain ⟨hb4,x,hx,q,hq1,hq2,hq3⟩ := selected_span_conjugate_critical_path h hb p hnonabelian
  have hxq : x ∈ stabilizer Rg (q.walk.getVert 2) := hq2.symm ▸ hx
  have hBn := Escape.Propagation.Rigidity.B_normalized
    (geometry := sourceGeometry h) hb (alpha Rg) rfl
  have hBm : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).map
      (MulAut.conj x⁻¹).toMonoidHom = B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (hBn ((stabilizer Rg (alpha Rg)).inv_mem hx))
  have hi : (B Rg (q.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (act Rg x (p.walk.getVert 2))) ≤ 2 := by
    rw [hq2,U_act,←hBm,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hslice
  have hbounds := midpoint_slice_eq_reverse_kernel h e hz hk hb4 q x hxq rfl hi
  have hcomm := (midpoint_common_kernel_endpoint_commutator h e hz hk hb4 q x hxq rfl hi).2
  rw [hq2] at hcomm
  refine ⟨hb4,x,hx,q,hq1,hq2,hq3,hbounds.2.2.1,hbounds.2.2.2,hcomm,?_⟩
  rw [hcomm]
  exact small_critical_commutator_card h e hz hk q (by rw [hbounds.2.2.1]; decide)

include h in
/-- Above distance four, every selected orbit span is abelian. Otherwise
its noncommuting generators give a critical path of length four. -/
theorem selected_span_abelian_of_four_lt
    (hb : 4 < sourceDistance h) {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a') :
    ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
      localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ = ⊥ := by
  by_contra hn
  have he := (selected_span_conjugate_critical_path h (by omega) p hn).1
  omega

include h e hz hk in
/-- In the small nonabelian branch, the whole derived subgroup of the
selected span is the common-kernel commutator on a constructed critical
path. It is central at the original start and disjoint from the center at
the second vertex. No conjugate path or common-kernel premise is assumed. -/
theorem small_selected_span_derived_critical_path
    (hb : 2 < sourceDistance h) {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (hnonabelian : ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
      localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≠ ⊥) :
    let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
    sourceDistance h = 4 ∧ Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
      ⁅P,P⁆ ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
      ⁅P,P⁆ ⊓ centralizer
        (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg)) = ⊥ ∧
      ∃ x ∈ stabilizer Rg (alpha Rg),
        ∃ q : CriticalPath Rg (sourceGeometry h)
            (p.walk.getVert 2) (act Rg x (p.walk.getVert 2)),
          q.walk.getVert 1 = p.walk.getVert 1 ∧
          q.walk.getVert 2 = alpha Rg ∧
          q.walk.getVert 3 = act Rg x (p.walk.getVert 1) ∧
          (Q Rg (act Rg x (p.walk.getVert 2))).relIndex
            (Z Rg (p.walk.getVert 2)) = 2 ∧
          (Q Rg (p.walk.getVert 2)).relIndex
            (Z Rg (act Rg x (p.walk.getVert 2))) = 2 ∧
          ⁅Q Rg (p.walk.getVert 2) ⊓ Q Rg (alpha Rg),
              Z Rg (act Rg x (p.walk.getVert 2))⁆ = ⁅P,P⁆ ∧
          ⁅Z Rg (p.walk.getVert 2),Z Rg (act Rg x (p.walk.getVert 2))⁆ = ⁅P,P⁆ := by
  let c := p.walk.getVert 2
  let P := localZSpan Rg c (alpha Rg)
  have hd := small_selected_span_derived h e hz hk hb p hsmall hslice hnonabelian
  obtain ⟨hb4,x,hx,q,hq1,hq2,hq3,hi,hi',hcomm,hcard⟩ :=
    selected_span_conjugate_path_kernel h e hz hk hb p hnonabelian hslice
  have hZcP : Z Rg c ≤ P := Z_le_localZSpan Rg _ _
  have hZxP : Z Rg (act Rg x c) ≤ P := by
    rw [Z_act]
    have hm : P.map (MulAut.conj x⁻¹).toMonoidHom = P :=
      mem_normalizer_iff_map_conj_eq.mp
        (localZSpan_normalized Rg _ _ ((stabilizer Rg (alpha Rg)).inv_mem hx))
    exact (map_mono hZcP).trans_eq hm
  have hle : ⁅Z Rg c,Z Rg (act Rg x c)⁆ ≤ ⁅P,P⁆ := commutator_mono hZcP hZxP
  let : Finite (⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) := Nat.finite_of_card_ne_zero (by
    have hp : Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) = 2 := hd.2.1
    omega)
  have heq : ⁅Z Rg c,Z Rg (act Rg x c)⁆ = ⁅P,P⁆ :=
    eq_of_le_of_card_ge hle (by
      have hc : Nat.card (⁅Z Rg c,Z Rg (act Rg x c)⁆ : Subgroup (FreeAmalgam Rg)) = 2 :=
        hcomm ▸ hcard
      have hp : Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) = 2 := hd.2.1
      omega)
  have hdis : ⁅P,P⁆ ⊓ centralizer (stabilizer Rg c : Set (FreeAmalgam Rg)) = ⊥ := by
    rw [←heq]
    exact small_critical_commutator_inf_centralizer h e hz hk q (by rw [hi]; decide)
  exact ⟨hb4,hd.2.1,hd.2.2,hdis,x,hx,q,hq1,hq2,hq3,hi,hi',hcomm.trans heq,heq⟩

omit hk in
include h e hz in
/-- Whole-core application: above distance four the selected spans are
abelian; a small nonabelian selected span gives the actual midpoint path
and its entire derived line. Strict slice choices and the remaining
terminal branches stay with the reconstruction owner. -/
theorem coreExhaustion_or_cubic_midpoint_slices :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false → Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      (∀ a' : Vertex Rg, ∀ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a',
        4 < sourceDistance h →
        ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
          localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ = ⊥) ∧
      (∀ a' : Vertex Rg, ∀ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a',
        (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4 →
        (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
          (U Rg (p.walk.getVert 2)) ≤ 2 →
        let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
        ⁅P,P⁆ = ⊥ ∨ sourceDistance h = 4 ∧ Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
          ⁅P,P⁆ ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
          ⁅P,P⁆ ⊓ centralizer
            (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg)) = ⊥ ∧
          ∃ x ∈ stabilizer Rg (alpha Rg),
            ∃ q : CriticalPath Rg (sourceGeometry h)
                (p.walk.getVert 2) (act Rg x (p.walk.getVert 2)),
              q.walk.getVert 1 = p.walk.getVert 1 ∧
              q.walk.getVert 2 = alpha Rg ∧
              q.walk.getVert 3 = act Rg x (p.walk.getVert 1) ∧
              (Q Rg (act Rg x (p.walk.getVert 2))).relIndex
                (Z Rg (p.walk.getVert 2)) = 2 ∧
              (Q Rg (p.walk.getVert 2)).relIndex
                (Z Rg (act Rg x (p.walk.getVert 2))) = 2 ∧
              ⁅Q Rg (p.walk.getVert 2) ⊓ Q Rg (alpha Rg),
                  Z Rg (act Rg x (p.walk.getVert 2))⁆ = ⁅P,P⁆ ∧
              ⁅Z Rg (p.walk.getVert 2),Z Rg (act Rg x (p.walk.getVert 2))⁆ = ⁅P,P⁆) := by
  rcases CubicEven.coreExhaustion_or_cubic_fullSymmetric h e hz with hx | ⟨hk,hs,hb⟩
  · exact Or.inl hx
  · refine Or.inr ⟨hk,hs,hb,graph_U_card h e hz hk,?_,?_⟩
    · intro a' p hb4
      exact selected_span_abelian_of_four_lt h hb4 p
    · intro a' p hsmall hslice
      by_cases hn : ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
          localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ = ⊥
      · exact Or.inl hn
      · exact Or.inr (small_selected_span_derived_critical_path h e hz hk hb p hsmall hslice hn)

omit hk in
include h e hz in
/-- Literal C.1.32 application of the same midpoint alternatives, preserving
the cubic projection and both complete moving covers. -/
theorem rankTwo_or_cubic_midpoint_slices :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false → Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      (∀ a' : Vertex Rg, ∀ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a',
        4 < sourceDistance h →
        ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
          localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ = ⊥) ∧
      (∀ a' : Vertex Rg, ∀ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a',
        (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4 →
        (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
          (U Rg (p.walk.getVert 2)) ≤ 2 →
        let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
        ⁅P,P⁆ = ⊥ ∨ sourceDistance h = 4 ∧ Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
          ⁅P,P⁆ ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
          ⁅P,P⁆ ⊓ centralizer
            (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg)) = ⊥ ∧
          ∃ x ∈ stabilizer Rg (alpha Rg),
            ∃ q : CriticalPath Rg (sourceGeometry h)
                (p.walk.getVert 2) (act Rg x (p.walk.getVert 2)),
              q.walk.getVert 1 = p.walk.getVert 1 ∧
              q.walk.getVert 2 = alpha Rg ∧
              q.walk.getVert 3 = act Rg x (p.walk.getVert 1) ∧
              (Q Rg (act Rg x (p.walk.getVert 2))).relIndex
                (Z Rg (p.walk.getVert 2)) = 2 ∧
              (Q Rg (p.walk.getVert 2)).relIndex
                (Z Rg (act Rg x (p.walk.getVert 2))) = 2 ∧
              ⁅Q Rg (p.walk.getVert 2) ⊓ Q Rg (alpha Rg),
                  Z Rg (act Rg x (p.walk.getVert 2))⁆ = ⁅P,P⁆ ∧
              ⁅Z Rg (p.walk.getVert 2),Z Rg (act Rg x (p.walk.getVert 2))⁆ = ⁅P,P⁆) :=
  (coreExhaustion_or_cubic_midpoint_slices h e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
