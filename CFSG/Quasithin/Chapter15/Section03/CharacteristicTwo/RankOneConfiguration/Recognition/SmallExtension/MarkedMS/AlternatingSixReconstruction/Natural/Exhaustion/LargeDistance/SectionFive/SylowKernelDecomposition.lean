module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowSingleMover
public import Theory.GroupTheory.Commutator.SplitPair
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowSingleMover
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowKernelMovement
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowAdjacent

/-!
# The common critical kernel as a line times its fixed subgroup

In the order-sixteen radical-image branch above distance four, let D be a
small critical line, T the first-edge core, and F the common full kernel of
the endpoint-seed orbit. Suppose T moves D. Quadraticity of that orbit puts
its whole critical-line span in F. Since [F,T] has order at most two and
[D,T] is nontrivial, the two displacements coincide and have order two.

Every element of T moving D therefore moves F through that same line.
Its commutator homomorphism has fixed index two on F. The full seed has
edge-fixed index at most eight, including the central attachment, whereas
F has index four. Comparing these indices shows that the element's fixer
on F is the entire edge-fixed subgroup C. The critical line supplements C
with trivial intersection: F = D C. Thus every subactor A of T satisfies
[F,A] = [D,A].

The actual critical-path application retains both full kernels, their
join, and their intersection, and fixes the first three vertices under
transport. Reversing the walk gives the literal predecessor-core identity.
The original-radical application uses the supplied restriction and
embedding. Both possible moved covers and every central attachment remain.
These statements require small critical index and critical-line movement;
they do not require unequal neighboring small movers. They do not construct
the backward neighbor or complete either distance exclusion.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the kernel comparisons and backward selection in (5.5)--(5.9),
printed pp.915--921. The proof uses the original natural-graph orbit and
common-kernel estimates, without identifying its core with the exceptional
cubic graph's core.
-/

public noncomputable section
open Theory.GroupTheory
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped commutatorElement Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowKernelDecomposition
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include e hz hn in
private theorem edge_fixed_index_bound
    (hb : 4 < replacementDistance h d)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    (centralizer (Q d.radical t : Set (FreeAmalgam d.radical))).relIndex
      (Z d.radical a) ≤ 8 := by
  let T := Q d.radical t
  let := finite_Z d.radical a
  let : Finite (U d.radical a) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical a)) (inclusion_injective _)
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨i,hinj,hir,hiR,_,hiU⟩ := SylowAdjacent.edge_coordinates (h := h) hc ha hat
  have hTS : T ≤ stabilizer d.radical a := fun _ hx => hx.2 a (adjacent_symm d.radical hat)
  have hm : (T.comap i).map i = T := map_comap_eq_self (hTS.trans_eq hir.symm)
  have hTR : T.comap i ≤ d.radical := by
    have hh := comap_mono (f := i) (show T ≤ Q d.radical t from le_rfl)
    rwa [←hiR,comap_map_eq_self_of_injective hinj] at hh
  have hiT : (centralizer (T : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) ≤ 8 := by
    have hidx := SmallMover.centralizer_index_map i hinj (replacementMoved d) (T.comap i)
    rw [hiU,hm] at hidx
    rw [hidx]
    let := replacementMoved_normal h d
    rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim
      (replacementMoved d) s.projection s.surjective
      (s.projection_kernel.trans (moved_centralizer s).symm)]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ 2)
      (SylowKernelMovement.cover_two_group_fixed_bound s _
        ((replacement_radical_isPGroup h d).of_injective (inclusion hTR)
          (inclusion_injective hTR)))
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    cases he : color d.radical t <;> simp_all
  have hedge : Z d.radical t ≤ centralizer (T : Set (FreeAmalgam d.radical)) := by
    intro z hz
    rw [Z,if_neg (by simp [ht])] at hz
    exact (mem_omegaCenter_iff.mp hz).2.2
  let C := Z d.radical a ⊓ centralizer (T : Set (FreeAmalgam d.radical))
  have hCZ : C ≤ Z d.radical a := inf_le_left
  let : Finite C := Finite.of_injective (inclusion hCZ) (inclusion_injective _)
  have hnorm : C ≤ normalizer (U d.radical a : Set (FreeAmalgam d.radical)) :=
    (hCZ.trans (Z_le_stabilizer d.radical a)).trans (U_normalized a)
  have hjoin : U d.radical a ⊔ C = Z d.radical a := by
    apply le_antisymm (sup_le (DistanceEight.U_le_Z d.radical a) hCZ)
    rw [DistanceTwo.CentralLayer.Z_eq_moving_sup_edge_at h e hz d ha hat]
    exact sup_le le_sup_left (le_sup_right.trans' (le_inf
      (adjacent_Z_le d.radical ha hat) hedge))
  have hindex := relIndex_sup_of_normalizes (U d.radical a) C hnorm
  rw [hjoin] at hindex
  change (Z d.radical a ⊓ centralizer (T : Set (FreeAmalgam d.radical))).relIndex
    (Z d.radical a) = C.relIndex (U d.radical a) at hindex
  rw [inf_relIndex_left] at hindex
  have hCU : C ⊓ U d.radical a = centralizer (T : Set (FreeAmalgam d.radical)) ⊓ U d.radical a := by
    ext z
    exact ⟨fun hz => ⟨hz.1.2,hz.2⟩,fun hz => ⟨⟨DistanceEight.U_le_Z d.radical a hz.2,hz.1⟩,hz.2⟩⟩
  rw [hindex,←inf_relIndex_right C,hCU,inf_relIndex_right]
  exact hiT

include e hz hn in
/-- In the moving-line order-sixteen branch the common full kernel and the
critical line have exactly the same nontrivial edge displacement. No
inequality of neighboring small movers is required. -/
theorem sixteen_common_kernel_line_displacement_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hmove : ¬ Q d.radical (p.walk.getVert 1) ≤ centralizer
      ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    let T := Q d.radical (p.walk.getVert 1)
    let D := ⁅Z d.radical a,Z d.radical a'⁆
    let W := componentOrbit D T
    let F := Z d.radical a ⊓ centralizer (componentOrbit (Z d.radical a') T : Set _)
    W ≤ F ∧ ⁅D,T⁆ = ⁅W,T⁆ ∧ ⁅D,T⁆ = ⁅F,T⁆ ∧
      Nat.card (⁅D,T⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
      ⁅D,T⁆ ≤ Z d.radical (p.walk.getVert 1) ∧
      ⁅D,T⁆ ≤ centralizer (T : Set (FreeAmalgam d.radical)) := by
  let T := Q d.radical (p.walk.getVert 1)
  let D := ⁅Z d.radical a,Z d.radical a'⁆
  let W := componentOrbit D T
  let E := componentOrbit (Z d.radical a') T
  let F := Z d.radical a ⊓ centralizer (E : Set (FreeAmalgam d.radical))
  have hl : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
  have hT := SylowLarge.sixteen_edge_relative_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d) hcard p.start_color hat
  have hi := SylowKernelPair.small_seed_orbit_identifications_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p
  have hq := SylowKernelPair.small_seed_orbit_quadratic_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall
  have ho := SylowMovingLine.small_critical_line_orbit_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall
  have hc := SylowCommonKernel.moving_common_kernel_edge_control_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall (hT.symm ▸ hmove)
  dsimp only at hi hq ho hc
  rw [hT] at hi hq ho hc
  have hWE : W ≤ centralizer (E : Set (FreeAmalgam d.radical)) := by
    have hh := commutator_eq_bot_iff_le_centralizer.mp hq.1
    rwa [hi.2.2.1] at hh
  have hWF : W ≤ F := le_inf (ho.1.trans (DistanceEight.U_le_Z d.radical a)) hWE
  have hDF : D ≤ F := (le_componentOrbit D T).trans hWF
  have hle : ⁅D,T⁆ ≤ ⁅F,T⁆ := commutator_mono hDF le_rfl
  let := finite_Z d.radical (p.walk.getVert 1)
  let : Finite (⁅F,T⁆ : Subgroup (FreeAmalgam d.radical)) := Finite.of_injective
    (inclusion hc.2.2.2.1) (inclusion_injective _)
  let : Finite (⁅D,T⁆ : Subgroup (FreeAmalgam d.radical)) := Finite.of_injective
    (inclusion hle) (inclusion_injective _)
  have hnz : ⁅D,T⁆ ≠ ⊥ := by
    intro hh
    exact hmove (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hh))
  have hpos := (one_lt_card_iff_ne_bot (⁅D,T⁆ : Subgroup (FreeAmalgam d.radical))).mpr hnz
  have hbound := card_le_of_le hle
  have hboundF : Nat.card (⁅F,T⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2 := hc.2.2.1
  have hcardD : Nat.card (⁅D,T⁆ : Subgroup (FreeAmalgam d.radical)) = 2 := by omega
  have hDFcomm : ⁅D,T⁆ = ⁅F,T⁆ := eq_of_le_of_card_ge hle (by omega)
  have hDW : ⁅D,T⁆ = ⁅W,T⁆ := le_antisymm
    (commutator_mono (le_componentOrbit D T) le_rfl)
    ((commutator_mono hWF le_rfl).trans_eq hDFcomm.symm)
  exact ⟨hWF,hDW,hDFcomm,hcardD,hDFcomm ▸ hc.2.2.2.1,hDFcomm ▸ hc.2.2.2.2⟩

include e hz hn in
/-- Every edge element moving the small critical line has the same fixer
on the common full kernel as the whole edge core. That kernel is the
internal product of the critical line and the entire fixed subgroup. -/
theorem sixteen_line_mover_common_kernel_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (x : FreeAmalgam d.radical) (hx : x ∈ Q d.radical (p.walk.getVert 1))
    (hxD : x ∉ centralizer ((⁅Z d.radical a,Z d.radical a'⁆ :
      Subgroup (FreeAmalgam d.radical)) : Set _)) :
    let T := Q d.radical (p.walk.getVert 1)
    let D := ⁅Z d.radical a,Z d.radical a'⁆
    let F := Z d.radical a ⊓ centralizer (componentOrbit (Z d.radical a') T : Set _)
    let C := Z d.radical a ⊓ centralizer (T : Set (FreeAmalgam d.radical))
    F = D ⊔ C ∧ D ⊓ C = ⊥ ∧ C.relIndex (Z d.radical a) = 8 ∧
      C.relIndex F = 2 ∧
      F ⊓ centralizer ({x} : Set (FreeAmalgam d.radical)) = C ∧
      ⁅F,zpowers x⁆ = ⁅D,T⁆ := by
  let T := Q d.radical (p.walk.getVert 1)
  let D := ⁅Z d.radical a,Z d.radical a'⁆
  let E := componentOrbit (Z d.radical a') T
  let F := Z d.radical a ⊓ centralizer (E : Set (FreeAmalgam d.radical))
  let C := Z d.radical a ⊓ centralizer (T : Set (FreeAmalgam d.radical))
  have hmove : ¬ T ≤ centralizer (D : Set (FreeAmalgam d.radical)) := fun hh => hxD (hh hx)
  have hd := sixteen_common_kernel_line_displacement_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hmove
  have hDF : D ≤ F := (le_componentOrbit D T).trans hd.1
  have hFZ : F ≤ Z d.radical a := inf_le_left
  have hl : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
  have hT := SylowLarge.sixteen_edge_relative_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d) hcard p.start_color hat
  have hi := SylowKernelPair.small_seed_orbit_identifications_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p
  have hc := SylowCommonKernel.moving_common_kernel_edge_control_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall (hT.symm ▸ hmove)
  dsimp only at hi hc
  rw [hT] at hi hc
  have hTS : T ≤ stabilizer d.radical a := fun _ ht => ht.2 _ (adjacent_symm d.radical hat)
  have hTF : T ≤ normalizer (F : Set (FreeAmalgam d.radical)) :=
    (le_inf (hTS.trans (Z_normalized d.radical a))
      (hi.2.1.trans (normalizer_le_normalizer_centralizer E))).trans
        inf_normalizer_le_normalizer_inf
  let := finite_Z d.radical a
  let : Finite F := Finite.of_injective (inclusion hFZ) (inclusion_injective _)
  let : Finite D := Finite.of_injective (inclusion (hDF.trans hFZ)) (inclusion_injective _)
  let : Finite C := Finite.of_injective
    (inclusion (show C ≤ Z d.radical a from inf_le_left)) (inclusion_injective _)
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a p.start_color
  have hFFT : ⁅F,T⁆ ≤ F := le_normalizer_iff_commutator_le_left.mp hTF
  let : Finite (⁅F,T⁆ : Subgroup (FreeAmalgam d.radical)) := Finite.of_injective
    (inclusion hFFT) (inclusion_injective _)
  have hcardFT : Nat.card (⁅F,T⁆ : Subgroup (FreeAmalgam d.radical)) = 2 :=
    hd.2.2.1 ▸ hd.2.2.2.1
  have hxF : x ∉ centralizer (F : Set (FreeAmalgam d.radical)) :=
    fun hh => hxD (centralizer_le hDF hh)
  have hcentral : ⁅F,T⁆ ≤ centralizer (F : Set (FreeAmalgam d.radical)) :=
    (hFFT.trans hFZ).trans ((le_centralizer (Z d.radical a)).trans (centralizer_le hFZ))
  have hfx := SylowSingleMover.single_mover_fixed_index F ⁅F,T⁆ x
    (commutator_mono le_rfl (zpowers_le.mpr hx)) hcentral hcardFT hxF
  have hCF : C ≤ F := inf_le_inf_left _ (centralizer_le hi.1)
  have hCx : C ≤ F ⊓ centralizer ({x} : Set (FreeAmalgam d.radical)) := by
    refine le_inf hCF ?_
    intro z hz
    exact mem_centralizer_singleton_iff.mpr ((hz.2 x hx).symm)
  have hFindex : F.relIndex (Z d.radical a) = 4 := hc.2.1
  have hbound : C.relIndex (Z d.radical a) ≤ 8 := by
    rw [show C = Z d.radical a ⊓ centralizer (T : Set (FreeAmalgam d.radical)) from rfl,
      inf_relIndex_left]
    exact edge_fixed_index_bound (e := e) (hz := hz) (hn := hn) hb p.start_color hat
  have hmul := relIndex_mul_relIndex C F (Z d.radical a) hCF hFZ
  rw [hFindex] at hmul
  have hupper : C.relIndex F ≤ 2 := by omega
  have hlower : 2 ≤ C.relIndex F := by
    have hh := relIndex_le_of_le_left hCx
      (index_ne_zero_of_finite : C.relIndex F ≠ 0)
    rw [inf_relIndex_left] at hh
    exact hfx ▸ hh
  have hidxC : C.relIndex F = 2 := by omega
  have hfull : C.relIndex (Z d.radical a) = 8 := by omega
  have hmulx := relIndex_mul_relIndex C
    (F ⊓ centralizer ({x} : Set (FreeAmalgam d.radical))) F hCx inf_le_left
  rw [inf_relIndex_left,hfx,hidxC] at hmulx
  have hfixed : F ⊓ centralizer ({x} : Set (FreeAmalgam d.radical)) = C :=
    le_antisymm (relIndex_eq_one.mp (by omega)) hCx
  have hxle : ⁅F,zpowers x⁆ ≤ ⁅F,T⁆ := commutator_mono le_rfl (zpowers_le.mpr hx)
  let : Finite (⁅F,zpowers x⁆ : Subgroup (FreeAmalgam d.radical)) := Finite.of_injective
    (inclusion hxle) (inclusion_injective _)
  have hxne : ⁅F,zpowers x⁆ ≠ ⊥ := by
    intro he
    have hh := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)
    exact hxF (hh (mem_zpowers x))
  have hxpos := (one_lt_card_iff_ne_bot (⁅F,zpowers x⁆ : Subgroup (FreeAmalgam d.radical))).mpr hxne
  have hxeq : ⁅F,zpowers x⁆ = ⁅F,T⁆ := eq_of_le_of_card_ge hxle (by omega)
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hcent := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hcardD : Nat.card D = 2 := small_critical_commutator_card s hcent p hsmall
  have hnotDC : ¬ D ≤ C := by
    intro hh
    exact hxD (le_centralizer_iff.mp (hh.trans inf_le_right) hx)
  let : Finite (D ⊓ C : Subgroup (FreeAmalgam d.radical)) := Finite.of_injective
    (inclusion inf_le_left) (inclusion_injective _)
  have hdisjoint : D ⊓ C = ⊥ := by
    by_contra hh
    have hpos := (one_lt_card_iff_ne_bot (D ⊓ C : Subgroup (FreeAmalgam d.radical))).mpr hh
    have heq : D ⊓ C = D := eq_of_le_of_card_ge inf_le_left (by omega)
    exact hnotDC (heq ▸ (show D ⊓ C ≤ C from inf_le_right))
  have hCD : C ≤ normalizer (D : Set (FreeAmalgam d.radical)) :=
    ((show C ≤ Z d.radical a from inf_le_left).trans
      ((le_centralizer (Z d.radical a)).trans (centralizer_le (hDF.trans hFZ)))).trans
        (Subgroup.centralizer_le_normalizer _)
  have hjoinindex : C.relIndex (D ⊔ C) = 2 := by
    rw [relIndex_sup_of_normalizes D C hCD,←inf_relIndex_right,inf_comm,hdisjoint]
    simpa using hcardD
  have hjoinF : D ⊔ C ≤ F := sup_le hDF hCF
  have hmuljoin := relIndex_mul_relIndex C (D ⊔ C) F le_sup_right hjoinF
  rw [hjoinindex,hidxC] at hmuljoin
  have hjoin : F = D ⊔ C := le_antisymm (relIndex_eq_one.mp (by omega)) hjoinF
  exact ⟨hjoin,hdisjoint,hfull,hidxC,hfixed,hxeq.trans hd.2.2.1.symm⟩



include e hz hn in
/-- Any subactor of the actual edge core has the same displacement on the
common full kernel as on the original critical line. This is the estimate
used after restricting to the predecessor core. -/
theorem sixteen_common_kernel_subactor_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hmove : ¬ Q d.radical (p.walk.getVert 1) ≤ centralizer
      ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _))
    (A : Subgroup (FreeAmalgam d.radical)) (hA : A ≤ Q d.radical (p.walk.getVert 1)) :
    let T := Q d.radical (p.walk.getVert 1)
    let D := ⁅Z d.radical a,Z d.radical a'⁆
    let F := Z d.radical a ⊓ centralizer (componentOrbit (Z d.radical a') T : Set _)
    ⁅F,A⁆ = ⁅D,A⁆ ∧
      Nat.card (⁅F,A⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2 ∧
      ⁅F,A⁆ ≤ Z d.radical (p.walk.getVert 1) ∧
      ⁅F,A⁆ ≤ centralizer (T : Set (FreeAmalgam d.radical)) := by
  classical
  let T := Q d.radical (p.walk.getVert 1)
  let D := ⁅Z d.radical a,Z d.radical a'⁆
  let F := Z d.radical a ⊓ centralizer (componentOrbit (Z d.radical a') T : Set _)
  let C := Z d.radical a ⊓ centralizer (T : Set (FreeAmalgam d.radical))
  obtain ⟨x,hx,hxD⟩ := Set.not_subset.mp hmove
  have hs := sixteen_line_mover_common_kernel_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p hsmall x hx hxD
  have hd := sixteen_common_kernel_line_displacement_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hmove
  have hDF : D ≤ F := (le_componentOrbit D T).trans hd.1
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a p.start_color
  have hDC : D ≤ centralizer (C : Set (FreeAmalgam d.radical)) :=
    (hDF.trans inf_le_left).trans
      ((le_centralizer (Z d.radical a)).trans (centralizer_le inf_le_left))
  have hCA : C ≤ centralizer (A : Set (FreeAmalgam d.radical)) :=
    inf_le_right.trans (centralizer_le hA)
  have hAC : A ≤ normalizer (C : Set (FreeAmalgam d.radical)) :=
    (le_centralizer_iff.mp hCA).trans (Subgroup.centralizer_le_normalizer _)
  have hgen : F = D ⊔ C := hs.1
  have heq : ⁅F,A⁆ = ⁅D,A⁆ := by
    rw [hgen,commutator_sup_of_commuting_factors D C A hDC hAC,
      commutator_eq_bot_iff_le_centralizer.mpr hCA,sup_bot_eq]
  have hle : ⁅F,A⁆ ≤ ⁅D,T⁆ := by
    rw [heq]
    exact commutator_mono le_rfl hA
  let := finite_Z d.radical (p.walk.getVert 1)
  let : Finite (⁅D,T⁆ : Subgroup (FreeAmalgam d.radical)) := Finite.of_injective
    (inclusion hd.2.2.2.2.1) (inclusion_injective _)
  exact ⟨heq,(card_le_of_le hle).trans_eq hd.2.2.2.1,
    hle.trans hd.2.2.2.2.1,hle.trans hd.2.2.2.2.2⟩

include e hz hn in
/-- An actual pair of critical paths with a decomposed common full kernel.
A moving critical line suffices; there is no unequal-neighbor premise. The
transport fixes the first three vertices and keeps both original kernels. -/
theorem sixteen_moving_path_kernel_decomposition_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hmove : ¬ Q d.radical (p.walk.getVert 1) ≤ centralizer
      ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    let T := Q d.radical (p.walk.getVert 1)
    let D := ⁅Z d.radical a,Z d.radical a'⁆
    let C := Z d.radical a ⊓ centralizer (T : Set (FreeAmalgam d.radical))
    ∃ x ∈ T, x ∉ centralizer (D : Set (FreeAmalgam d.radical)) ∧
      ∃ q : CriticalPath d.radical (replacementGeometry h d) a (act d.radical x⁻¹ a'),
        (∀ i, q.walk.getVert i = act d.radical x⁻¹ (p.walk.getVert i)) ∧
        q.walk.getVert 1 = p.walk.getVert 1 ∧ q.walk.getVert 2 = p.walk.getVert 2 ∧
        (Q d.radical (act d.radical x⁻¹ a')).relIndex (Z d.radical a) = 2 ∧
        let K := Z d.radical a ⊓ Q d.radical a'
        let K' := Z d.radical a ⊓ Q d.radical (act d.radical x⁻¹ a')
        K ⊔ K' = Z d.radical a ∧
          K ⊓ K' = D ⊔ C ∧ D ⊓ C = ⊥ ∧ C.relIndex (Z d.radical a) = 8 ∧
          (K ⊓ K') ⊓ centralizer ({x} : Set (FreeAmalgam d.radical)) = C ∧
          ⁅K ⊓ K',zpowers x⁆ = ⁅D,T⁆ ∧
          Nat.card (⁅D,T⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
          ⁅D,T⁆ ≤ Z d.radical (p.walk.getVert 1) ∧
          (Q d.radical a ⊔ Z d.radical a') ⊓
            (Q d.radical a ⊔ Z d.radical (act d.radical x⁻¹ a')) = Q d.radical a := by
  classical
  let T := Q d.radical (p.walk.getVert 1)
  let D := ⁅Z d.radical a,Z d.radical a'⁆
  let F := Z d.radical a ⊓ centralizer (componentOrbit (Z d.radical a') T : Set _)
  obtain ⟨x,hx,hxD⟩ := Set.not_subset.mp hmove
  have hl : 4 < p.walk.length := p.length_eq_b ▸ hb
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hxnorm : x ∈ normalizer (T : Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical a :=
    ⟨T.le_normalizer hx,hx.2 _ (adjacent_symm d.radical hat)⟩
  obtain ⟨q,hq,_,hi,hjoin,hindex,hnorm,hcore⟩ :=
    SylowKernelPair.small_moving_kernel_path_knownSimple
      (e := e) (hz := hz) (hn := hn) hb p hsmall x hxnorm hxD
  have hs := sixteen_line_mover_common_kernel_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p hsmall x hx hxD
  have hd := sixteen_common_kernel_line_displacement_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hmove
  let K := Z d.radical a ⊓ Q d.radical a'
  let K' := Z d.radical a ⊓ Q d.radical (act d.radical x⁻¹ a')
  have hT := SylowLarge.sixteen_edge_relative_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d) hcard p.start_color hat
  have horbit := SylowKernelPair.small_seed_orbit_identifications_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p
  have hpair := SylowKernelPair.small_kernel_pair_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall x hxnorm hxD
  dsimp only at horbit hpair
  rw [hT] at horbit hpair
  have hkm : K.map (MulAut.conj x).toMonoidHom = K' := by
    have hzmap : (Z d.radical a).map (MulAut.conj x).toMonoidHom = Z d.radical a :=
      mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical a hxnorm.2)
    dsimp only [K,K']
    rw [map_inf _ _ _ (MulAut.conj x).injective,hzmap,Q_act,inv_inv]
  have hFpair : F = K ⊓ K' := by
    have hh : F = K ⊓ K.map (MulAut.conj x).toMonoidHom := horbit.2.2.2.trans hpair.1
    rwa [hkm] at hh
  have hfixed : (K ⊓ K') ⊓ centralizer ({x} : Set (FreeAmalgam d.radical)) =
      Z d.radical a ⊓ centralizer (T : Set (FreeAmalgam d.radical)) := by
    rw [←hFpair]
    exact hs.2.2.2.2.1
  have hcomm : ⁅K ⊓ K',zpowers x⁆ = ⁅D,T⁆ := by
    rw [←hFpair]
    exact hs.2.2.2.2.2
  refine ⟨x,hx,hxD,q,hq,?_,?_,hi,hjoin,hFpair.symm.trans hs.1,
    hs.2.1,hs.2.2.1,hfixed,hcomm,hd.2.2.2.1,hd.2.2.2.2.1,hcore⟩
  · rw [hq]
    exact (stabilizer d.radical (p.walk.getVert 1)).inv_mem hx.1
  · rw [hq]
    exact (stabilizer d.radical (p.walk.getVert 2)).inv_mem
      (hx.2 _ (adjacent_symm d.radical hct))

include e hz hn in
/-- At the opposite endpoint the literal predecessor-core displacement of
the common full kernel equals its displacement of the critical line.
Central attachments remain in the common kernel and are fixed. -/
theorem sixteen_common_predecessor_line_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hmove : ¬ Q d.radical (p.walk.getVert (p.walk.length-1)) ≤ centralizer
      ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    let T := Q d.radical (p.walk.getVert (p.walk.length-1))
    let D := ⁅Z d.radical a,Z d.radical a'⁆
    let F := Z d.radical a' ⊓ centralizer (componentOrbit (Z d.radical a) T : Set _)
    let A := Q d.radical (p.walk.getVert (p.walk.length-2))
    ⁅F,A⁆ = ⁅D,A⁆ ∧
      Nat.card (⁅F,A⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2 ∧
      ⁅F,A⁆ ≤ Z d.radical (p.walk.getVert (p.walk.length-1)) ∧
      ⁅F,A⁆ ≤ centralizer (T : Set (FreeAmalgam d.radical)) := by
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
  have hA : Q d.radical (p.walk.getVert (p.walk.length-2)) ≤ Q d.radical (r.walk.getVert 1) := by
    rw [hr]
    exact Q_le_adjacent_h d.radical ht hct
  have hh := sixteen_common_kernel_subactor_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard r hrs hrm _ hA
  dsimp only at hh ⊢
  rwa [hr,commutator_comm (Z d.radical a')] at hh


include e hz hn in
/-- The decomposition and subactor calculation on the literal restricted
original radical, embedded in the chosen replacement. Neither a Sylow
assumption on the original input nor an unequal-mover premise is added. -/
theorem original_sylow_common_kernel_decomposition_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hfirst : p.walk.getVert 1 = beta d.radical)
    (hmove : ¬ ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical) ≤
      centralizer ((⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ :
        Subgroup (FreeAmalgam d.radical)) : Set _)) :
    let T := ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)
    let D := ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆
    let F := Z d.radical (alpha d.radical) ⊓
      centralizer (componentOrbit (Z d.radical a') T : Set (FreeAmalgam d.radical))
    let C := Z d.radical (alpha d.radical) ⊓ centralizer (T : Set (FreeAmalgam d.radical))
    F = D ⊔ C ∧ D ⊓ C = ⊥ ∧ C.relIndex (Z d.radical (alpha d.radical)) = 8 ∧
      C.relIndex F = 2 ∧
      ∀ A : Subgroup (FreeAmalgam d.radical), A ≤ T →
        ⁅F,A⁆ = ⁅D,A⁆ ∧ Nat.card (⁅F,A⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2 ∧
          ⁅F,A⁆ ≤ Z d.radical (beta d.radical) ∧
          ⁅F,A⁆ ≤ centralizer (T : Set (FreeAmalgam d.radical)) := by
  classical
  have hl : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
  have hat : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
  have hT := SylowLarge.sixteen_edge_relative_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d) hcard p.start_color hat
  rw [hfirst,SylowSmallNormalizer.four_lt_base_edge_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) hb] at hT
  have hm : ¬ Q d.radical (p.walk.getVert 1) ≤ centralizer
      ((⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    rwa [hfirst,←hT]
  obtain ⟨x,hx,hxD⟩ := Set.not_subset.mp hm
  have hs := sixteen_line_mover_common_kernel_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p hsmall x hx hxD
  dsimp only at hs ⊢
  rw [hfirst,←hT] at hs
  refine ⟨hs.1,hs.2.1,hs.2.2.1,hs.2.2.2.1,?_⟩
  intro A hA
  have hA' : A ≤ Q d.radical (p.walk.getVert 1) := by rwa [hfirst,←hT]
  have hh := sixteen_common_kernel_subactor_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hm A hA'
  dsimp only at hh
  rwa [hfirst,←hT] at hh

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowKernelDecomposition
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
