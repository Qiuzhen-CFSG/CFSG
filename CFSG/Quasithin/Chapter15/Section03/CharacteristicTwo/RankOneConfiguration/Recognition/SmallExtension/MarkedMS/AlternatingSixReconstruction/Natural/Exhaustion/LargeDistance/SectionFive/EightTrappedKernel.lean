module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightBackwardKernel
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeFullKernel
public import Theory.GroupTheory.NormalizedSupConsequences
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTrappedKernel

/-!
# Whole kernels and trapped radii in the image-eight branch

The actual edge's unique small mover is the centralizer of both the small
critical line and the common full kernel. It normalizes every edge-conjugate
full critical kernel. Each such hyperplane has index two over the common
kernel, so the mover acts trivially on that quotient and fixes the kernel.
The entire opposite-core intersection inherits these estimates.

If the whole starting radius is trapped in the critical predecessor core,
it lies in the reverse small mover. Its endpoint image is larger than two;
the mover has image four, so the radius fills it modulo the endpoint core.
Every full reverse critical kernel is moved and has precisely the common
kernel as its radius fixer. The fixer in the entire endpoint seed is also
that same common kernel: a larger fixer would give fixed index at most two
on the faithful natural quotient, contradicting the radius image of four.
A two-edge seed with nonzero kernel movement is selected inside the radius.

Small-mover subactors have whole-seed commutator of order at most eight,
using quadraticity and the full moved-cover orders sixteen or thirty-two.
The original-radical consumer retains its literal embedding, its index two
over the replacement edge and the entire central attachment. It applies
all the kernel, radius and selected-seed statements on the same graph.
Small critical index, movement of the critical line and radius trapping are
explicit branch hypotheses. Their terminal exclusion, unconditional backward
selection and the general distance-four bounds remain to be proved.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.7)--(5.8), printed pp.919--920. The internal CubeFullKernel import
reuses only its subgroup-product commutator lemma; it asserts no equality
of radical images or graphs. The generic nonzero-kernel theorem comes from
SylowTrappedKernel, without an image-sixteen hypothesis.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightTrappedKernel
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include e hz hn in
/-- The maximum small mover is the edge centralizer of both the critical
line and common kernel, and normalizes every full critical-kernel conjugate. -/
theorem common_kernel_centralizer_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hmove : ¬ Q d.radical (p.walk.getVert 1) ≤ centralizer
      ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    let T := Q d.radical (p.walk.getVert 1)
    let D := ⁅Z d.radical a,Z d.radical a'⁆
    let K := Z d.radical a ⊓ Q d.radical a'
    let F := Z d.radical a ⊓ centralizer (componentOrbit (Z d.radical a') T : Set _)
    let J := SmallMover.join (U d.radical a) (Q d.radical a) T 4
    T ⊓ centralizer (D : Set (FreeAmalgam d.radical)) = J ∧
      T ⊓ centralizer (F : Set (FreeAmalgam d.radical)) = J ∧
      T ⊓ normalizer (K : Set (FreeAmalgam d.radical)) = J ∧
      ∀ x ∈ T,
        J ≤ normalizer (K.map (MulAut.conj x).toMonoidHom : Set (FreeAmalgam d.radical)) := by
  let T := Q d.radical (p.walk.getVert 1)
  let D := ⁅Z d.radical a,Z d.radical a'⁆
  let K := Z d.radical a ⊓ Q d.radical a'
  let F := Z d.radical a ⊓ centralizer (componentOrbit (Z d.radical a') T : Set _)
  let J := SmallMover.join (U d.radical a) (Q d.radical a) T 4
  have hl : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
  have hk := EightSmallMovers.critical_kernel_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall
  dsimp only at hk
  have hJ := EightSmallMovers.edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p.start_color hat
  have hJnorm : T ≤ normalizer (J : Set (FreeAmalgam d.radical)) := hJ.2.2.2.2.2.2.1
  have hJT : J ≤ T := hJ.2.2.2.1
  have hTK : T ⊓ normalizer (K : Set (FreeAmalgam d.radical)) = J := hk.2.2 hmove
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hKN := small_critical_kernel_normalizer_eq_line_centralizer s hc p hsmall
  have hTG : T ≤ stabilizer d.radical a := fun _ hx => hx.2 a (adjacent_symm d.radical hat)
  have hTC : T ⊓ centralizer (D : Set (FreeAmalgam d.radical)) = J := by
    apply le_antisymm
    · intro x hx
      have hn : x ∈ stabilizer d.radical a ⊓ normalizer (K : Set (FreeAmalgam d.radical)) := by
        rw [hKN]
        exact ⟨hTG hx.1,hx.2⟩
      rw [←hTK]
      exact ⟨hx.1,hn.2⟩
    · exact le_inf hJT hk.1
  have hJF : J ≤ centralizer (F : Set (FreeAmalgam d.radical)) := by
    apply le_centralizer_iff.mp
    apply commutator_eq_bot_iff_le_centralizer.mp
    have hh := EightBackwardKernel.common_kernel_subactor_knownSimple
      (e := e) (hz := hz) (hn := hn) hb p hsmall hmove J hJT
    exact hh.1.trans (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hk.1))
  have hDF : D ≤ F := (le_componentOrbit D T).trans
    (EightBackwardKernel.common_kernel_line_displacement_knownSimple
      (e := e) (hz := hz) (hn := hn) hb p hsmall hmove).1
  have hTF : T ⊓ centralizer (F : Set (FreeAmalgam d.radical)) = J :=
    le_antisymm ((inf_le_inf_left _ (centralizer_le hDF)).trans_eq hTC) (le_inf hJT hJF)
  refine ⟨hTC,hTF,hTK,?_⟩
  intro x hx
  have hJx : J.map (MulAut.conj x).toMonoidHom = J :=
    mem_normalizer_iff_map_conj_eq.mp (hJnorm hx)
  calc
    J = J.map (MulAut.conj x).toMonoidHom := hJx.symm
    _ ≤ (normalizer (K : Set (FreeAmalgam d.radical))).map
        (MulAut.conj x).toMonoidHom := map_mono hk.2.1
    _ ≤ normalizer (K.map (MulAut.conj x).toMonoidHom : Set (FreeAmalgam d.radical)) :=
      K.le_normalizer_map _

include e hz hn in
/-- Every full critical kernel has an index-two common kernel; the maximum
small mover acts trivially modulo that kernel and fixes it pointwise. -/
theorem small_mover_full_kernel_commutator_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hmove : ¬ Q d.radical (p.walk.getVert 1) ≤ centralizer
      ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    let T := Q d.radical (p.walk.getVert 1)
    let K := Z d.radical a ⊓ Q d.radical a'
    let F := Z d.radical a ⊓ centralizer (componentOrbit (Z d.radical a') T : Set _)
    let J := SmallMover.join (U d.radical a) (Q d.radical a) T 4
    ∀ x ∈ T,
      F ≤ K.map (MulAut.conj x).toMonoidHom ∧
      F.relIndex (K.map (MulAut.conj x).toMonoidHom) = 2 ∧
      ⁅K.map (MulAut.conj x).toMonoidHom,J⁆ ≤ F ∧
      ⁅⁅K.map (MulAut.conj x).toMonoidHom,J⁆,J⁆ = ⊥ := by
  let T := Q d.radical (p.walk.getVert 1)
  let K := Z d.radical a ⊓ Q d.radical a'
  let F := Z d.radical a ⊓ centralizer (componentOrbit (Z d.radical a') T : Set _)
  let J := SmallMover.join (U d.radical a) (Q d.radical a) T 4
  have hfix := common_kernel_centralizer_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall hmove
  have hJF : J ≤ centralizer (F : Set (FreeAmalgam d.radical)) := by
    have hh : J ≤ T ⊓ centralizer (F : Set (FreeAmalgam d.radical)) := hfix.2.1.symm.le
    exact hh.trans inf_le_right
  have hl : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
  have hf := EightBackwardKernel.edge_orbit_kernel_eq_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall hmove
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hKZ : K.relIndex (Z d.radical a) = 2 := by
    rw [show K = Z d.radical a ⊓ Q d.radical a' from rfl,inf_relIndex_left]
    exact (small_critical_indices s hc p hsmall).1
  dsimp only
  intro x hx
  let Kx := K.map (MulAut.conj x).toMonoidHom
  have hZmap : (Z d.radical a).map (MulAut.conj x).toMonoidHom = Z d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp
      (Z_normalized d.radical a (hx.2 a (adjacent_symm d.radical hat)))
  have hxZ : Kx ≤ Z d.radical a := (map_mono inf_le_left).trans_eq hZmap
  have hxidx : Kx.relIndex (Z d.radical a) = 2 := by
    change (K.map (MulAut.conj x).toMonoidHom).relIndex (Z d.radical a) = 2
    rw [←hZmap,relIndex_map_map_of_injective _ _ (MulAut.conj x).injective]
    exact hKZ
  have hFx : F ≤ Kx := by
    rw [show F = ⨅ t : T, K.map (MulAut.conj (t : FreeAmalgam d.radical)).toMonoidHom
      from hf.2.1]
    exact iInf_le _ (⟨x,hx⟩ : T)
  have hmul := relIndex_mul_relIndex F Kx (Z d.radical a) hFx hxZ
  have hFZ : F.relIndex (Z d.radical a) = 4 := hf.2.2.1
  rw [hFZ,hxidx] at hmul
  have hidx : F.relIndex Kx = 2 := by omega
  have hcomm : ⁅Kx,J⁆ ≤ F := commutator_le_of_normalized_index_two Kx F J
    hFx hidx (hfix.2.2.2 x hx) (hJF.trans (Subgroup.centralizer_le_normalizer _))
  refine ⟨hFx,hidx,hcomm,?_⟩
  exact le_bot_iff.mp ((commutator_mono hcomm le_rfl).trans_eq
    (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hJF)))


include e hz hn in
/-- The actual opposite-core intersection lies in the maximum small mover.
It normalizes each full critical kernel and acts quadratically on the whole seed. -/
theorem opposite_core_full_kernel_control_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hmove : ¬ Q d.radical (p.walk.getVert 1) ≤ centralizer
      ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    let T := Q d.radical (p.walk.getVert 1)
    let A := T ⊓ Q d.radical a'
    let K := Z d.radical a ⊓ Q d.radical a'
    let F := Z d.radical a ⊓ centralizer (componentOrbit (Z d.radical a') T : Set _)
    let J := SmallMover.join (U d.radical a) (Q d.radical a) T 4
    A ≤ J ∧ A ≤ centralizer (F : Set (FreeAmalgam d.radical)) ∧
      ⁅Z d.radical a,A⁆ ≤ F ∧ ⁅⁅Z d.radical a,A⁆,A⁆ = ⊥ ∧
      ∀ x ∈ T,
        A ≤ normalizer (K.map (MulAut.conj x).toMonoidHom : Set (FreeAmalgam d.radical)) ∧
        ⁅K.map (MulAut.conj x).toMonoidHom,A⁆ ≤ F ∧
        (centralizer (A : Set (FreeAmalgam d.radical))).relIndex
          (K.map (MulAut.conj x).toMonoidHom) ≤ 2 := by
  classical
  let T := Q d.radical (p.walk.getVert 1)
  let A := T ⊓ Q d.radical a'
  let D := ⁅Z d.radical a,Z d.radical a'⁆
  let K := Z d.radical a ⊓ Q d.radical a'
  let F := Z d.radical a ⊓ centralizer (componentOrbit (Z d.radical a') T : Set _)
  let J := SmallMover.join (U d.radical a) (Q d.radical a) T 4
  have hf := common_kernel_centralizer_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall hmove
  have hk := small_mover_full_kernel_commutator_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall hmove
  have hD : D ≤ Z d.radical a' := (critical_Z_commutator_le_moving (h := h) p).trans
    (inf_le_right.trans (DistanceEight.U_le_Z d.radical a'))
  have hAD : A ≤ centralizer (D : Set (FreeAmalgam d.radical)) :=
    inf_le_right.trans ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a' p.end_color))).trans (centralizer_le hD))
  have hAJ : A ≤ J := (le_inf inf_le_left hAD).trans_eq hf.1
  have hJF : J ≤ centralizer (F : Set (FreeAmalgam d.radical)) :=
    hf.2.1.symm.le.trans inf_le_right
  have hAF : A ≤ centralizer (F : Set (FreeAmalgam d.radical)) := hAJ.trans hJF
  have hl : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
  obtain ⟨x,hx,hxm⟩ := SetLike.not_le_iff_exists.mp hmove
  have hp := SylowKernelPair.small_kernel_pair_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall x ⟨T.le_normalizer hx, hx.2 a (adjacent_symm d.radical hat)⟩ hxm
  have hgen : K ⊔ K.map (MulAut.conj x).toMonoidHom = Z d.radical a := hp.2.2.1
  have hZmap : (Z d.radical a).map (MulAut.conj x).toMonoidHom = Z d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp
      (Z_normalized d.radical a (hx.2 a (adjacent_symm d.radical hat)))
  have hxZ : K.map (MulAut.conj x).toMonoidHom ≤ Z d.radical a :=
    (map_mono inf_le_left).trans_eq hZmap
  have h1 : (MulAut.conj (1 : FreeAmalgam d.radical)).toMonoidHom =
      MonoidHom.id (FreeAmalgam d.radical) := by
    apply MonoidHom.ext
    intro y
    simp
  have hKJ : ⁅K,J⁆ ≤ F := by
    simpa only [h1,Subgroup.map_id] using (hk 1 T.one_mem).2.2.1
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a p.start_color
  have hZF : Z d.radical a ≤ normalizer (F : Set (FreeAmalgam d.radical)) :=
    ((le_centralizer (Z d.radical a)).trans (centralizer_le inf_le_left)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hZJ : ⁅Z d.radical a,J⁆ ≤ F := by
    rw [←hgen]
    exact commutator_sup_le_of_relative_normal (Z d.radical a) K
      (K.map (MulAut.conj x).toMonoidHom) J F hZF inf_le_left hxZ hKJ (hk x hx).2.2.1
  have hZA : ⁅Z d.radical a,A⁆ ≤ F := (commutator_mono le_rfl hAJ).trans hZJ
  refine ⟨hAJ,hAF,hZA,?_,?_⟩
  · exact le_bot_iff.mp ((commutator_mono hZA le_rfl).trans_eq
      (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hAF)))
  · intro y hy
    exact ⟨hAJ.trans (hf.2.2.2 y hy),(commutator_mono le_rfl hAJ).trans (hk y hy).2.2.1,
      EightBackwardKernel.common_fixed_full_kernel_indices_knownSimple
        (e := e) (hz := hz) (hn := hn) hb p hsmall hmove A
        (le_centralizer_iff.mp hAF) y hy⟩

include e hz hn in
/-- A trapped radius lies in the reverse maximum small mover, normalizes
every full reverse kernel and moves the endpoint seed into the common kernel
intersected with the actual radius. -/
theorem trapped_radius_full_kernels_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hmove : ¬ Q d.radical (p.walk.getVert (p.walk.length-1)) ≤ centralizer
      ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _))
    (htrap : V d.radical a ≤ Q d.radical (p.walk.getVert (p.walk.length-2))) :
    let T := Q d.radical (p.walk.getVert (p.walk.length-1))
    let K := Z d.radical a' ⊓ Q d.radical a
    let F := Z d.radical a' ⊓ centralizer (componentOrbit (Z d.radical a) T : Set _)
    let J := SmallMover.join (U d.radical a') (Q d.radical a') T 4
    V d.radical a ≤ J ∧
      ⁅Z d.radical a',V d.radical a⁆ ≤ F ⊓ V d.radical a ∧
      ⁅⁅Z d.radical a',V d.radical a⁆,V d.radical a⁆ = ⊥ ∧
      ∀ x ∈ T,
        V d.radical a ≤ normalizer
          (K.map (MulAut.conj x).toMonoidHom : Set (FreeAmalgam d.radical)) ∧
        ⁅K.map (MulAut.conj x).toMonoidHom,V d.radical a⁆ ≤ F ⊓ V d.radical a ∧
        (centralizer (V d.radical a : Set (FreeAmalgam d.radical))).relIndex
          (K.map (MulAut.conj x).toMonoidHom) ≤ 2 := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let r : CriticalPath d.radical (replacementGeometry h d) a' a := {
    start_color := p.end_color
    walk := p.walk.reverse
    shortest := by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm]
    critical := critical_reverse_pair s hc p }
  have hr : r.walk.getVert 1 = p.walk.getVert (p.walk.length-1) :=
    p.walk.getVert_reverse 1
  have hrs : (Q d.radical a).relIndex (Z d.radical a') < 4 := by
    rw [(small_critical_indices s hc p hsmall).2]
    decide
  have hrm : ¬ Q d.radical (r.walk.getVert 1) ≤ centralizer
      ((⁅Z d.radical a',Z d.radical a⁆ : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    rwa [hr,commutator_comm (Z d.radical a')]
  have hh := opposite_core_full_kernel_control_knownSimple
    (e := e) (hz := hz) (hn := hn) hb r hrs hrm
  dsimp only at hh ⊢
  rw [hr] at hh
  let T := Q d.radical (p.walk.getVert (p.walk.length-1))
  let K := Z d.radical a' ⊓ Q d.radical a
  let F := Z d.radical a' ⊓ centralizer (componentOrbit (Z d.radical a) T : Set _)
  let A := T ⊓ Q d.radical a
  have hl : 2 < p.walk.length := p.length_eq_b ▸ (by omega : 2 < replacementDistance h d)
  have hct : Adjacent d.radical (p.walk.getVert (p.walk.length-2))
      (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have het : Adjacent d.radical a' (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have ht : color d.radical (p.walk.getVert (p.walk.length-1)) = true := by
    have hh := adjacent_color_ne d.radical het
    rw [p.end_color] at hh
    cases he : color d.radical (p.walk.getVert (p.walk.length-1)) <;> simp_all
  have hVA : V d.radical a ≤ A := le_inf
    (htrap.trans (Q_le_adjacent_h d.radical ht hct))
    (V_le_Q d.radical (geometry := replacementGeometry h d) p.start_color (by exact (show 2 < replacementDistance h d by omega)))
  have hVF : V d.radical a ≤ centralizer (F : Set (FreeAmalgam d.radical)) :=
    hVA.trans hh.2.1
  have hZV : Z d.radical a' ≤ normalizer (V d.radical a : Set (FreeAmalgam d.radical)) :=
    (critical_Z_le_stabilizer d.radical (replacementGeometry h d) a p.start_color
      (by rw [(replacementGeometry h d).distance_constant a p.start_color]
          exact replacementDistance_pos h d) p.critical).trans (DistanceEight.V_normalized d.radical a)
  have hcomm : ⁅Z d.radical a',V d.radical a⁆ ≤ F :=
    (commutator_mono le_rfl hVA).trans hh.2.2.1
  refine ⟨hVA.trans hh.1,le_inf hcomm
    (le_normalizer_iff_commutator_le_right.mp hZV),?_,?_⟩
  · exact le_bot_iff.mp ((commutator_mono hcomm le_rfl).trans_eq
      (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hVF)))
  · intro x hx
    have hZmap : (Z d.radical a').map (MulAut.conj x).toMonoidHom = Z d.radical a' :=
      mem_normalizer_iff_map_conj_eq.mp
        (Z_normalized d.radical a' (hx.2 a' (adjacent_symm d.radical het)))
    have hxZ : K.map (MulAut.conj x).toMonoidHom ≤ Z d.radical a' :=
      (map_mono inf_le_left).trans_eq hZmap
    have hnorm := hh.2.2.2.2 x hx
    refine ⟨hVA.trans hnorm.1,le_inf
      ((commutator_mono le_rfl hVA).trans hnorm.2.1)
      (le_normalizer_iff_commutator_le_right.mp (hxZ.trans hZV)),?_⟩
    exact EightBackwardKernel.common_fixed_full_kernel_indices_knownSimple
      (e := e) (hz := hz) (hn := hn) hb r hrs hrm (V d.radical a)
      (by simpa only [hr] using le_centralizer_iff.mp hVF) x (by simpa only [hr] using hx)

include e hz hn in
/-- Every full reverse kernel has precisely the common kernel as its
radius centralizer. Its action is nontrivial and has fixed index two. -/
theorem trapped_radius_kernel_centralizers_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hmove : ¬ Q d.radical (p.walk.getVert (p.walk.length-1)) ≤ centralizer
      ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _))
    (htrap : V d.radical a ≤ Q d.radical (p.walk.getVert (p.walk.length-2))) :
    let T := Q d.radical (p.walk.getVert (p.walk.length-1))
    let K := Z d.radical a' ⊓ Q d.radical a
    let F := Z d.radical a' ⊓ centralizer (componentOrbit (Z d.radical a) T : Set _)
    ∀ x ∈ T,
      ⁅K.map (MulAut.conj x).toMonoidHom,V d.radical a⁆ ≠ ⊥ ∧
      (centralizer (V d.radical a : Set (FreeAmalgam d.radical))).relIndex
        (K.map (MulAut.conj x).toMonoidHom) = 2 ∧
      K.map (MulAut.conj x).toMonoidHom ⊓
        centralizer (V d.radical a : Set (FreeAmalgam d.radical)) = F ∧
      ⁅K.map (MulAut.conj x).toMonoidHom,V d.radical a⁆ ≤ F ⊓ V d.radical a := by
  let T := Q d.radical (p.walk.getVert (p.walk.length-1))
  let K := Z d.radical a' ⊓ Q d.radical a
  let F := Z d.radical a' ⊓ centralizer (componentOrbit (Z d.radical a) T : Set _)
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let r : CriticalPath d.radical (replacementGeometry h d) a' a := {
    start_color := p.end_color
    walk := p.walk.reverse
    shortest := by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm]
    critical := critical_reverse_pair s hc p }
  have hr : r.walk.getVert 1 = p.walk.getVert (p.walk.length-1) :=
    p.walk.getVert_reverse 1
  have hrs : (Q d.radical a).relIndex (Z d.radical a') < 4 := by
    rw [(small_critical_indices s hc p hsmall).2]
    decide
  have hrm : ¬ Q d.radical (r.walk.getVert 1) ≤ centralizer
      ((⁅Z d.radical a',Z d.radical a⁆ : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    rwa [hr,commutator_comm (Z d.radical a')]
  have hk := small_mover_full_kernel_commutator_knownSimple
    (e := e) (hz := hz) (hn := hn) hb r hrs hrm
  have ht := trapped_radius_full_kernels_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall hmove htrap
  have hFC := EightBackwardKernel.trapped_radius_common_kernel_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall hmove htrap
  dsimp only at hk ht hFC ⊢
  rw [hr] at hk
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb2
  have het : Adjacent d.radical a' (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,
      p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  intro x hx
  let Kx := K.map (MulAut.conj x).toMonoidHom
  let C := Kx ⊓ centralizer (V d.radical a : Set (FreeAmalgam d.radical))
  have hxG : x ∈ stabilizer d.radical a' := hx.2 a' (adjacent_symm d.radical het)
  have hne : ⁅Kx,V d.radical a⁆ ≠ ⊥ :=
    SylowTrappedKernel.trapped_radius_full_kernels_moved_knownSimple (e := e) (hz := hz) (hn := hn)
      hb p hsmall htrap x hxG
  have hFx : F ≤ Kx := (hk x hx).1
  have hFidx : F.relIndex Kx = 2 := (hk x hx).2.1
  have hZmap : (Z d.radical a').map (MulAut.conj x).toMonoidHom = Z d.radical a' :=
    mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical a' hxG)
  have hxZ : Kx ≤ Z d.radical a' := (map_mono inf_le_left).trans_eq hZmap
  let := finite_Z d.radical a'
  let : Finite Kx := Finite.of_injective (inclusion hxZ) (inclusion_injective _)
  have hidx : (centralizer (V d.radical a : Set (FreeAmalgam d.radical))).relIndex Kx = 2 := by
    have hle : (centralizer (V d.radical a : Set (FreeAmalgam d.radical))).relIndex Kx ≤ 2 :=
      (ht.2.2.2 x hx).2.2
    have hpos : 0 < (centralizer (V d.radical a : Set (FreeAmalgam d.radical))).relIndex Kx :=
      Nat.pos_of_ne_zero index_ne_zero_of_finite
    have hone : (centralizer (V d.radical a : Set (FreeAmalgam d.radical))).relIndex Kx ≠ 1 :=
      fun hh => hne (commutator_eq_bot_iff_le_centralizer.mpr (relIndex_eq_one.mp hh))
    omega
  have hFCx : F ≤ C := le_inf hFx hFC
  have hCidx : C.relIndex Kx = 2 := by
    change (Kx ⊓ centralizer (V d.radical a : Set (FreeAmalgam d.radical))).relIndex Kx = 2
    rwa [inf_relIndex_left]
  have hmul := relIndex_mul_relIndex F C Kx hFCx inf_le_left
  rw [hFidx,hCidx] at hmul
  have hCF : C ≤ F := relIndex_eq_one.mp (by omega : F.relIndex C = 1)
  exact ⟨hne,hidx,le_antisymm hCF hFCx,(ht.2.2.2 x hx).2.1⟩

include e hz hn in
/-- The selected two-edge seed has nontrivial action and exactly the common
kernel as its fixer in the full reverse critical kernel. -/
theorem trapped_radius_selected_seed_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hmove : ¬ Q d.radical (p.walk.getVert (p.walk.length-1)) ≤ centralizer
      ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _))
    (htrap : V d.radical a ≤ Q d.radical (p.walk.getVert (p.walk.length-2))) :
    let T := Q d.radical (p.walk.getVert (p.walk.length-1))
    let K := Z d.radical a' ⊓ Q d.radical a
    let F := Z d.radical a' ⊓ centralizer (componentOrbit (Z d.radical a) T : Set _)
    ∃ c t, color d.radical c = false ∧
      (cosetGraph d.radical).dist c a = 2 ∧
      Adjacent d.radical a t ∧ Adjacent d.radical c t ∧
      Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) ∧
      ⁅K,Z d.radical c⁆ ≠ ⊥ ∧
      ⁅U d.radical a' ⊓ Q d.radical a,Z d.radical c⁆ = ⁅K,Z d.radical c⁆ ∧
      ⁅U d.radical a' ⊓ Q d.radical a,Z d.radical c⁆ ≠ ⊥ ∧
      (centralizer (Z d.radical c : Set (FreeAmalgam d.radical))).relIndex K = 2 ∧
      K ⊓ centralizer (Z d.radical c : Set (FreeAmalgam d.radical)) = F ∧
      ⁅K,Z d.radical c⁆ ≤ F ⊓ Z d.radical c := by
  let T := Q d.radical (p.walk.getVert (p.walk.length-1))
  let K := Z d.radical a' ⊓ Q d.radical a
  let F := Z d.radical a' ⊓ centralizer (componentOrbit (Z d.radical a) T : Set _)
  obtain ⟨c,t,hc,hca,hat,hct,hZtrap,hne,hmeq,hmne⟩ := SylowTrappedKernel.trapped_radius_moving_seed_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall htrap
  have hZV : Z d.radical c ≤ V d.radical a :=
    (V_le_iff d.radical p.start_color _).mp le_rfl c hc hca.le
  have hfix := trapped_radius_kernel_centralizers_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall hmove htrap 1 T.one_mem
  have h1 : (MulAut.conj (1 : FreeAmalgam d.radical)).toMonoidHom = MonoidHom.id _ := by
    apply MonoidHom.ext
    intro z
    simp
  simp only [h1,Subgroup.map_id] at hfix
  have hfixeq : K ⊓ centralizer (V d.radical a : Set (FreeAmalgam d.radical)) = F :=
    hfix.2.2.1
  have hidxK : F.relIndex K = 2 := by
    rw [←hfixeq,inf_relIndex_left]
    exact hfix.2.1
  have hFC : F ≤ centralizer (Z d.radical c : Set (FreeAmalgam d.radical)) :=
    EightBackwardKernel.trapped_backward_seed_common_kernel_knownSimple
      (e := e) (hz := hz) (hn := hn) hb p hsmall hmove hc hca.le hZtrap |>.1
  let := finite_Z d.radical a'
  let : Finite K := Finite.of_injective (inclusion (show K ≤ Z d.radical a' from inf_le_left))
    (inclusion_injective _)
  let C := K ⊓ centralizer (Z d.radical c : Set (FreeAmalgam d.radical))
  have hFCx : F ≤ C := le_inf (hfixeq.symm.le.trans inf_le_left) hFC
  have hidx : (centralizer (Z d.radical c : Set (FreeAmalgam d.radical))).relIndex K = 2 := by
    have hle := (relIndex_le_of_le_left hFC
      (index_ne_zero_of_finite : F.relIndex K ≠ 0)).trans_eq hidxK
    have hpos : 0 < (centralizer (Z d.radical c : Set (FreeAmalgam d.radical))).relIndex K :=
      Nat.pos_of_ne_zero index_ne_zero_of_finite
    have hone : (centralizer (Z d.radical c : Set (FreeAmalgam d.radical))).relIndex K ≠ 1 :=
      fun hh => hne (commutator_eq_bot_iff_le_centralizer.mpr (relIndex_eq_one.mp hh))
    omega
  have hCidx : C.relIndex K = 2 := by
    change (K ⊓ centralizer (Z d.radical c : Set (FreeAmalgam d.radical))).relIndex K = 2
    rwa [inf_relIndex_left]
  have hmul := relIndex_mul_relIndex F C K hFCx inf_le_left
  rw [hidxK,hCidx] at hmul
  have hCF : C = F := le_antisymm (relIndex_eq_one.mp (by omega : F.relIndex C = 1)) hFCx
  have hKG : K ≤ stabilizer d.radical c :=
    (show K ≤ Q d.radical a from inf_le_right).trans
      (fun _ hx => (Q_le_adjacent_h d.radical (by
        have hh := adjacent_color_ne d.radical hat
        rw [p.start_color] at hh
        cases he : color d.radical t <;> simp_all) hat hx).2 c (adjacent_symm d.radical hct))
  have hcomm : ⁅K,Z d.radical c⁆ ≤ F ⊓ Z d.radical c := le_inf
    ((commutator_mono le_rfl hZV).trans hfix.2.2.2 |>.trans inf_le_left)
    (le_normalizer_iff_commutator_le_right.mp (hKG.trans (Z_normalized d.radical c)))
  exact ⟨c,t,hc,hca,hat,hct,hZtrap,hne,hmeq,hmne,hidx,hCF,hcomm⟩

include e hz hn in
/-- A trapped whole radius fills the reverse small mover modulo the endpoint
core. Its endpoint image has order four, not merely order greater than two. -/
theorem trapped_radius_saturates_small_mover_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hmove : ¬ Q d.radical (p.walk.getVert (p.walk.length-1)) ≤ centralizer
      ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _))
    (htrap : V d.radical a ≤ Q d.radical (p.walk.getVert (p.walk.length-2))) :
    let T := Q d.radical (p.walk.getVert (p.walk.length-1))
    let J := SmallMover.join (U d.radical a') (Q d.radical a') T 4
    V d.radical a ⊔ Q d.radical a' = J ∧
      (Q d.radical a').relIndex (V d.radical a) = 4 := by
  let T := Q d.radical (p.walk.getVert (p.walk.length-1))
  let J := SmallMover.join (U d.radical a') (Q d.radical a') T 4
  let E := V d.radical a ⊔ Q d.radical a'
  have hl : 2 < p.walk.length := p.length_eq_b ▸ (by omega : 2 < replacementDistance h d)
  have het : Adjacent d.radical a' (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have hj := EightSmallMovers.edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p.end_color het
  have hQJ : Q d.radical a' ≤ J := hj.2.2.1
  have hJG : J ≤ stabilizer d.radical a' := hj.2.2.2.1.trans
    (fun _ hx => hx.2 a' (adjacent_symm d.radical het))
  have hVJ := (trapped_radius_full_kernels_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall hmove htrap).1
  have hEJ : E ≤ J := sup_le hVJ hQJ
  let := finite_stabilizer d.radical a'
  let : Finite J := Finite.of_injective (inclusion hJG) (inclusion_injective _)
  let : ((Q d.radical a').subgroupOf E).Normal :=
    normal_subgroupOf_of_le_normalizer ((hEJ.trans hJG).trans (Q_normalized d.radical a'))
  have hi : (Q d.radical a').relIndex E = (Q d.radical a').relIndex (V d.radical a) := by
    have hh := relIndex_sup_left ((V d.radical a).subgroupOf E) ((Q d.radical a').subgroupOf E)
    rw [sup_comm ((Q d.radical a').subgroupOf E),
      ←subgroupOf_sup (show V d.radical a ≤ E from le_sup_left)
      (show Q d.radical a' ≤ E from le_sup_right),relIndex_subgroupOf le_rfl,
      relIndex_subgroupOf (show V d.radical a ≤ E from le_sup_left)] at hh
    exact hh
  have hmul := relIndex_mul_relIndex (Q d.radical a') E J le_sup_right hEJ
  have hQidx : (Q d.radical a').relIndex J = 4 := hj.2.2.2.2.1
  rw [hQidx,hi] at hmul
  have hpos : 0 < E.relIndex J := Nat.pos_of_ne_zero index_ne_zero_of_finite
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hlarge := (critical_radius_indices_gt_seed s hc (by omega) p).1
  rw [(small_critical_indices s hc p hsmall).1] at hlarge
  have hidx : E.relIndex J = 1 := by nlinarith
  have heq : E = J := le_antisymm hEJ (relIndex_eq_one.mp hidx)
  exact ⟨heq,by simpa only [hidx,mul_one] using hmul⟩

include e hz hn in
/-- Every subactor of the maximum small mover has whole-seed commutator
of order at most eight, including the order-thirty-two moving cover. -/
theorem small_mover_seed_commutator_card_knownSimple
    (hb : 4 < replacementDistance h d)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t)
    (A : Subgroup (FreeAmalgam d.radical))
    (hA : A ≤ SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4) :
    Nat.card (⁅Z d.radical a,A⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 8 := by
  let J := SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4
  have hj := EightSmallMovers.edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb ha hat
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    cases he : color d.radical t <;> simp_all
  have hZt : Z d.radical t ≤ centralizer (A : Set (FreeAmalgam d.radical)) := by
    intro x hx y hy
    rw [Z,if_neg (by simp [ht])] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2 y (hj.2.2.2.1 (hA hy))
  have hZtN : Z d.radical t ≤ normalizer (U d.radical a : Set (FreeAmalgam d.radical)) :=
    ((adjacent_Z_le d.radical ha hat).trans (Z_le_stabilizer d.radical a)).trans (U_normalized a)
  have hcomm : ⁅Z d.radical a,A⁆ = ⁅U d.radical a,A⁆ := by
    rw [DistanceTwo.CentralLayer.Z_eq_moving_sup_edge_at h e hz d ha hat,
      commutator_sup_fixed _ _ A hZtN hZt]
  have hJG : J ≤ stabilizer d.radical a := hj.2.2.2.1.trans
    (fun _ hx => hx.2 _ (adjacent_symm d.radical hat))
  have hWU : ⁅U d.radical a,J⁆ ≤ U d.radical a :=
    le_normalizer_iff_commutator_le_left.mp (hJG.trans (U_normalized a))
  let F := U d.radical a ⊓ centralizer (J : Set (FreeAmalgam d.radical))
  have hWF : ⁅Z d.radical a,A⁆ ≤ F := by
    rw [hcomm]
    exact (commutator_mono le_rfl hA).trans
      (le_inf hWU (commutator_eq_bot_iff_le_centralizer.mp hj.2.2.2.2.2.2.2.1))
  have hfix : F.relIndex (U d.radical a) = 4 := by
    change (U d.radical a ⊓ centralizer (J : Set _)).relIndex (U d.radical a) = 4
    rw [inf_relIndex_left]
    exact hj.2.2.2.2.2.2.2.2.1
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hUcard : Nat.card (U d.radical a) ≤ 32 := by
    obtain ⟨i,hi,_,_,hiU⟩ := vertex_coordinates (h := h) hc a ha
    rw [←hiU,card_map_of_injective hi]
    rcases moved_card s with he | he <;> omega
  let := finite_Z d.radical a
  let : Finite (U d.radical a) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical a)) (inclusion_injective _)
  let : Finite F := Finite.of_injective (inclusion (show F ≤ U d.radical a from inf_le_left))
    (inclusion_injective _)
  have hprod := relIndex_mul_card_of_le (show F ≤ U d.radical a from inf_le_left)
  rw [hfix] at hprod
  exact (card_le_of_le hWF).trans (by omega)

include e hz hn in
/-- The common reverse kernel is the fixer of the whole radius in the
entire endpoint seed. A larger fixer would give fixed index at most two,
contradicting the radius image of order four on the faithful natural layer. -/
theorem trapped_radius_whole_seed_fixer_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hmove : ¬ Q d.radical (p.walk.getVert (p.walk.length-1)) ≤ centralizer
      ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _))
    (htrap : V d.radical a ≤ Q d.radical (p.walk.getVert (p.walk.length-2))) :
    let T := Q d.radical (p.walk.getVert (p.walk.length-1))
    let F := Z d.radical a' ⊓ centralizer (componentOrbit (Z d.radical a) T : Set _)
    Z d.radical a' ⊓ centralizer (V d.radical a : Set (FreeAmalgam d.radical)) = F ∧
      (centralizer (V d.radical a : Set (FreeAmalgam d.radical))).relIndex
        (Z d.radical a') = 4 := by
  let T := Q d.radical (p.walk.getVert (p.walk.length-1))
  let F := Z d.radical a' ⊓ centralizer (componentOrbit (Z d.radical a) T : Set _)
  let C := Z d.radical a' ⊓ centralizer (V d.radical a : Set (FreeAmalgam d.radical))
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let r : CriticalPath d.radical (replacementGeometry h d) a' a := {
    start_color := p.end_color
    walk := p.walk.reverse
    shortest := by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm]
    critical := critical_reverse_pair s hc p }
  have hr : r.walk.getVert 1 = p.walk.getVert (p.walk.length-1) := p.walk.getVert_reverse 1
  have hrs : (Q d.radical a).relIndex (Z d.radical a') < 4 := by
    rw [(small_critical_indices s hc p hsmall).2]
    decide
  have hrm : ¬ Q d.radical (r.walk.getVert 1) ≤ centralizer
      ((⁅Z d.radical a',Z d.radical a⁆ : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    rwa [hr,commutator_comm (Z d.radical a')]
  have hFidx : F.relIndex (Z d.radical a') = 4 := by
    have hh := (EightBackwardKernel.edge_orbit_kernel_eq_knownSimple
      (e := e) (hz := hz) (hn := hn) hb r hrs hrm).2.2.1
    simpa only [hr] using hh
  have hFC : F ≤ C := le_inf inf_le_left
    (EightBackwardKernel.trapped_radius_common_kernel_knownSimple
      (e := e) (hz := hz) (hn := hn) hb p hsmall hmove htrap)
  have hsat := trapped_radius_saturates_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall hmove htrap
  have hVG : V d.radical a ≤ stabilizer d.radical a' := by
    have hVJ := le_sup_left.trans_eq hsat.1
    have hJT := SmallMover.join_le (U d.radical a') (Q d.radical a') T 4
    have hl : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
    have het : Adjacent d.radical a' (p.walk.getVert (p.walk.length-1)) := by
      have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
      rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
      exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
    exact (hVJ.trans hJT).trans (fun _ hx => hx.2 a' (adjacent_symm d.radical het))
  let := finite_Z d.radical a'
  let : Finite C := Finite.of_injective (inclusion (show C ≤ Z d.radical a' from inf_le_left))
    (inclusion_injective _)
  have hmul := relIndex_mul_relIndex F C (Z d.radical a') hFC inf_le_left
  rw [hFidx] at hmul
  have hpos : 0 < F.relIndex C := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hidx : F.relIndex C = 1 := by
    by_contra hne
    have hlargeIndex : 2 ≤ F.relIndex C := by omega
    have htwo : C.relIndex (Z d.radical a') ≤ 2 := by nlinarith
    have hidxU : (centralizer (V d.radical a : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a') ≤ 2 := by
      have hh := relIndex_le_of_le_right (H := centralizer (V d.radical a : Set _))
        (DistanceEight.U_le_Z d.radical a') index_ne_zero_of_finite
      have htwo' : (centralizer (V d.radical a : Set (FreeAmalgam d.radical))).relIndex
          (Z d.radical a') ≤ 2 := by
        simpa only [C,inf_relIndex_left] using htwo
      exact hh.trans htwo'
    have hh := moving_small_fixed_index_image s hc p.end_color (V d.radical a) hVG hidxU
    rw [hsat.2] at hh
    omega
  have hCF : C = F := le_antisymm (relIndex_eq_one.mp hidx) hFC
  refine ⟨hCF,?_⟩
  rw [←inf_relIndex_left,show Z d.radical a' ⊓ centralizer
    (V d.radical a : Set (FreeAmalgam d.radical)) = F from hCF]
  exact hFidx

include e hz hn in
/-- On the literal original-radical application, a trapped opposite radius
fills the replacement edge's small mover modulo the base core. The larger
restricted original radical retains index two, and its orbit gives the same
full-kernel fixer. Both moving covers are included in the bound of eight. -/
theorem original_radical_trapped_radius_knownSimple
    (hb : 4 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hfirst : p.walk.getVert 1 = beta d.radical)
    (hmove : ¬ ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical) ≤
      centralizer ((⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ :
        Subgroup (FreeAmalgam d.radical)) : Set _))
    (htrap : V d.radical a' ≤ Q d.radical (p.walk.getVert 2)) :
    let T := ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)
    let K := Z d.radical (alpha d.radical) ⊓ Q d.radical a'
    let F := Z d.radical (alpha d.radical) ⊓
      centralizer (componentOrbit (Z d.radical a') T : Set (FreeAmalgam d.radical))
    let J := SmallMover.join (U d.radical (alpha d.radical))
      (Q d.radical (alpha d.radical)) (Q d.radical (beta d.radical)) 4
    (Q d.radical (beta d.radical)).relIndex T = 2 ∧
      V d.radical a' ⊔ Q d.radical (alpha d.radical) = J ∧
      (Q d.radical (alpha d.radical)).relIndex (V d.radical a') = 4 ∧
      Nat.card (⁅Z d.radical (alpha d.radical),V d.radical a'⁆ :
        Subgroup (FreeAmalgam d.radical)) ≤ 8 ∧
      Z d.radical (alpha d.radical) ⊓ centralizer
        (V d.radical a' : Set (FreeAmalgam d.radical)) = F ∧
      (centralizer (V d.radical a' : Set (FreeAmalgam d.radical))).relIndex
        (Z d.radical (alpha d.radical)) = 4 ∧
      (∀ x ∈ Q d.radical (beta d.radical),
        ⁅K.map (MulAut.conj x).toMonoidHom,V d.radical a'⁆ ≠ ⊥ ∧
        (centralizer (V d.radical a' : Set (FreeAmalgam d.radical))).relIndex
          (K.map (MulAut.conj x).toMonoidHom) = 2 ∧
        K.map (MulAut.conj x).toMonoidHom ⊓
          centralizer (V d.radical a' : Set (FreeAmalgam d.radical)) = F ∧
        ⁅K.map (MulAut.conj x).toMonoidHom,V d.radical a'⁆ ≤ F ⊓ V d.radical a') ∧
      ∃ c t, color d.radical c = false ∧
        (cosetGraph d.radical).dist c a' = 2 ∧
        Adjacent d.radical a' t ∧ Adjacent d.radical c t ∧
        Z d.radical c ≤ Q d.radical (p.walk.getVert 2) ∧
        ⁅K,Z d.radical c⁆ ≠ ⊥ ∧
        ⁅U d.radical (alpha d.radical) ⊓ Q d.radical a',Z d.radical c⁆ = ⁅K,Z d.radical c⁆ ∧
        ⁅U d.radical (alpha d.radical) ⊓ Q d.radical a',Z d.radical c⁆ ≠ ⊥ ∧
        (centralizer (Z d.radical c : Set (FreeAmalgam d.radical))).relIndex K = 2 ∧
        K ⊓ centralizer (Z d.radical c : Set (FreeAmalgam d.radical)) = F ∧
        ⁅K,Z d.radical c⁆ ≤ F ⊓ Z d.radical c := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let r : CriticalPath d.radical (replacementGeometry h d) a' (alpha d.radical) := {
    start_color := p.end_color
    walk := p.walk.reverse
    shortest := by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm]
    critical := critical_reverse_pair s hc p }
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb2
  have hr1 : r.walk.getVert (r.walk.length-1) = p.walk.getVert 1 := by
    change p.walk.reverse.getVert (p.walk.reverse.length-1) = p.walk.getVert 1
    rw [SimpleGraph.Walk.length_reverse,p.walk.getVert_reverse]
    congr 1
    omega
  have hr2 : r.walk.getVert (r.walk.length-2) = p.walk.getVert 2 := by
    change p.walk.reverse.getVert (p.walk.reverse.length-2) = p.walk.getVert 2
    rw [SimpleGraph.Walk.length_reverse,p.walk.getVert_reverse]
    congr 1
    omega
  have hrs : (Q d.radical (alpha d.radical)).relIndex (Z d.radical a') < 4 := by
    rw [(small_critical_indices s hc p hsmall).2]
    decide
  have hN := SylowSmallNormalizer.four_lt_base_edge_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) hb
  have hfix := EightBackwardKernel.critical_line_fixed_iff_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall
  dsimp only at hfix
  rw [hfirst,hN] at hfix
  have hm : ¬ Q d.radical (p.walk.getVert 1) ≤ centralizer
      ((⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ :
        Subgroup (FreeAmalgam d.radical)) : Set _) := by
    rw [hfirst]
    exact fun hh => hmove (hfix.mpr hh)
  have hrm : ¬ Q d.radical (r.walk.getVert (r.walk.length-1)) ≤ centralizer
      ((⁅Z d.radical a',Z d.radical (alpha d.radical)⁆ :
        Subgroup (FreeAmalgam d.radical)) : Set _) := by
    rwa [hr1,commutator_comm (Z d.radical a')]
  have hsat := trapped_radius_saturates_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb r hrs hrm (hr2.symm ▸ htrap)
  have hker := trapped_radius_kernel_centralizers_knownSimple
    (e := e) (hz := hz) (hn := hn) hb r hrs hrm (hr2.symm ▸ htrap)
  have hwhole := trapped_radius_whole_seed_fixer_knownSimple
    (e := e) (hz := hz) (hn := hn) hb r hrs hrm (hr2.symm ▸ htrap)
  have hsel := trapped_radius_selected_seed_knownSimple
    (e := e) (hz := hz) (hn := hn) hb r hrs hrm (hr2.symm ▸ htrap)
  have he := EightBackwardKernel.edge_orbit_kernel_eq_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall hm
  dsimp only at hsat hker hwhole hsel he ⊢
  rw [hr1,hfirst] at hsat hker hwhole
  rw [hr1,hr2,hfirst] at hsel
  rw [hfirst,hN] at he
  rw [he.1] at hker hwhole hsel
  refine ⟨?_,hsat.1,hsat.2,?_,hwhole.1,hwhole.2,hker,hsel⟩
  · rw [Q_beta,relIndex_map_map_of_injective _ _ (embedM_injective d.radical)]
    exact (SylowWholeCore.four_lt_original_sylow_eight_image_knownSimple
      (e := e) (hz := hz) (hn := hn) hb).2.2.1
  · exact small_mover_seed_commutator_card_knownSimple
      (e := e) (hz := hz) (hn := hn) hb p.start_color (base_adjacent d.radical)
      (V d.radical a') (le_sup_left.trans_eq hsat.1)

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightTrappedKernel
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
