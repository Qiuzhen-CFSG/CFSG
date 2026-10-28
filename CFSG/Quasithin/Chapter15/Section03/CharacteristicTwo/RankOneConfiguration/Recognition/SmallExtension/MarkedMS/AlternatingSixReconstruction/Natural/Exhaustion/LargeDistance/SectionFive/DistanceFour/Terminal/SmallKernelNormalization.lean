module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.ElementaryKernelControl
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.RestrictedActor
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.OmegaControl
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowPairedFixer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeFullKernel

/-!
# The full small-critical kernel and its failure line

At critical distance four, put K = Z_c intersect Q_v, where v is the
midpoint of a small critical path a--z and c is within distance two of a.
The local core normalizes K. Full omega displacement control therefore
makes Z_z normalize K joined with Z_a unless full X is centrally generated
at every component vertex.

If normalization fails, the opposite full kernel Z_z intersect Q_a moves K
in an actual line. The elementary kernel estimate places this line in the
original critical commutator joined with the whole endpoint center. The
radius bound and central generation then put the line in all three seeds
Z_c, Z_v and Z_z. No central attachment is discarded.

These are the full-seed preliminary reductions for MS93 (5.12)(1), printed
pp.924--925. The compatible mover argument eliminating the line is a
separate step. SmallKernelNormalizationSelection applies the reductions to
the literal image-eight backward selector.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include s in
theorem small_backward_kernel_normalized_or_centrally_generated
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    {a z c : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (hcCol : color d.radical c = false)
    (hca : (cosetGraph d.radical).dist c a ≤ 2) :
    Z d.radical z ≤ normalizer (((Z d.radical c ⊓ Q d.radical (p.walk.getVert 2)) ⊔
      Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) ∨
      (∀ v : Vertex d.radical, color d.radical v = false →
        X d.radical v = U d.radical v ⊔
          (X d.radical v ⊓ centralizer (stabilizer d.radical v : Set (FreeAmalgam d.radical)))) := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  let v := p.walk.getVert 2
  let K := Z d.radical c ⊓ Q d.radical v
  have hv : color d.radical v = false := (p.vertex_color (by omega)).mpr (by decide)
  have hav : (cosetGraph d.radical).dist a v = 2 := p.dist_start (by omega)
  have hvz : (cosetGraph d.radical).dist v z = 2 := by
    rw [p.dist_end,hl]
  have hQaGc : Q d.radical a ≤ stabilizer d.radical c :=
    Q_le_stabilizer_of_dist_le_two a c p.start_color hcCol (by rwa [SimpleGraph.dist_comm])
  have hQaGv : Q d.radical a ≤ stabilizer d.radical v :=
    Q_le_stabilizer_of_dist_le_two a v p.start_color hv hav.le
  have hQvGz : Q d.radical v ≤ stabilizer d.radical z :=
    Q_le_stabilizer_of_dist_le_two v z hv p.end_color hvz.le
  have hKQa : K ≤ Q d.radical a := by
    apply inf_le_left.trans
    apply Z_le_Q_of_dist_lt d.radical c ((replacementGeometry h d).exists_critical c hcCol)
    rw [(replacementGeometry h d).distance_constant c hcCol]
    exact hca.trans_lt hb2
  have hNK : Q d.radical a ≤ normalizer (K : Set (FreeAmalgam d.radical)) :=
    (le_inf (hQaGc.trans (Z_normalized d.radical c))
      (hQaGv.trans (Q_normalized d.radical v))).trans
        inf_normalizer_le_normalizer_inf
  rcases critical_X_generation_or_normalization s hc p hsmall K
    (inf_le_right.trans hQvGz) hKQa (inf_le_right.trans hNK) with hgen | hnorm
  · exact Or.inr (X_central_generation_all p.end_color hgen)
  · left
    apply le_trans _ hnorm
    apply (replacementGeometry h d).omega_bound z p.end_color
    rw [(replacementGeometry h d).distance_constant z p.end_color]
    exact replacementDistance_pos h d





include s in
/-- If the source endpoint fails to normalize the full backward-kernel join,
its full opposite kernel moves that backward kernel in an actual line.
The line lies in both full seeds and is aligned with the original critical
commutator, including the entire central attachment. -/
theorem small_backward_kernel_nonnormal_line
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    {a z c : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (hcCol : color d.radical c = false)
    (hca : (cosetGraph d.radical).dist c a ≤ 2)
    (hnorm : ¬ Z d.radical z ≤ normalizer
      (((Z d.radical c ⊓ Q d.radical (p.walk.getVert 2)) ⊔
        Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    let K := Z d.radical c ⊓ Q d.radical (p.walk.getVert 2)
    let F := Z d.radical z ⊓ Q d.radical a
    Nat.card (⁅K,F⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
      ⁅K,F⁆ ≤ Z d.radical c ⊓ Z d.radical z ∧
      ⁅K,F⁆ ≤ ⁅Z d.radical a,Z d.radical z⁆ ⊔
        (Z d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))) := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  let v := p.walk.getVert 2
  let K := Z d.radical c ⊓ Q d.radical v
  let F := Z d.radical z ⊓ Q d.radical a
  let P := K ⊔ Z d.radical a
  let H := ⁅K,F⁆
  have hv : color d.radical v = false := (p.vertex_color (by omega)).mpr (by decide)
  have hav : (cosetGraph d.radical).dist a v = 2 := p.dist_start (by omega)
  have hvz : (cosetGraph d.radical).dist v z = 2 := by rw [p.dist_end,hl]
  have hQaGc : Q d.radical a ≤ stabilizer d.radical c :=
    Q_le_stabilizer_of_dist_le_two a c p.start_color hcCol (by rwa [SimpleGraph.dist_comm])
  have hQaGv : Q d.radical a ≤ stabilizer d.radical v :=
    Q_le_stabilizer_of_dist_le_two a v p.start_color hv hav.le
  have hQvGz : Q d.radical v ≤ stabilizer d.radical z :=
    Q_le_stabilizer_of_dist_le_two v z hv p.end_color hvz.le
  have hKQa : K ≤ Q d.radical a := by
    apply inf_le_left.trans
    apply Z_le_Q_of_dist_lt d.radical c ((replacementGeometry h d).exists_critical c hcCol)
    rw [(replacementGeometry h d).distance_constant c hcCol]
    exact hca.trans_lt hb2
  have hKGz : K ≤ stabilizer d.radical z := inf_le_right.trans hQvGz
  have hKGa : K ≤ stabilizer d.radical a := hKQa.trans (fun _ hx => hx.1)
  have hQaNK : Q d.radical a ≤ normalizer (K : Set (FreeAmalgam d.radical)) :=
    (le_inf (hQaGc.trans (Z_normalized d.radical c))
      (hQaGv.trans (Q_normalized d.radical v))).trans inf_normalizer_le_normalizer_inf
  have hKNF : K ≤ normalizer (F : Set (FreeAmalgam d.radical)) :=
    (le_inf (hKGz.trans (Z_normalized d.radical z))
      (hKQa.trans (Q d.radical a).le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hFNP : F ≤ normalizer (P : Set (FreeAmalgam d.radical)) :=
    (le_inf (inf_le_right.trans hQaNK)
      (inf_le_right.trans ((show Q d.radical a ≤ stabilizer d.radical a from fun _ hx => hx.1).trans
        (Z_normalized d.radical a)))).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hZFC : Z d.radical a ≤ centralizer (F : Set (FreeAmalgam d.radical)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a p.start_color)).trans
      (centralizer_le inf_le_right)
  have hHwhole : ⁅F,P⁆ = H := by
    rw [←commutator_eq_of_centralizing_sup (sup_comm (Z d.radical a) K) hZFC hKNF,
      commutator_comm]
  have hHP : H ≤ P := hHwhole ▸ le_normalizer_iff_commutator_le_right.mp hFNP
  have hHK : H ≤ K := le_normalizer_iff_commutator_le_left.mp (inf_le_right.trans hQaNK)
  have hHZ : H ≤ Z d.radical z :=
    (le_normalizer_iff_commutator_le_right.mp hKNF).trans inf_le_left
  have hcrit : ⁅Z d.radical z,Z d.radical a⁆ ≤ Z d.radical a := by
    rw [commutator_comm]
    exact ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans
      (DistanceEight.U_le_Z d.radical a)
  have hfixed : Z d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) = F := by
    apply le_antisymm
    · apply le_inf inf_le_left
      rw [←C_eq_Q s hc a p.start_color]
      exact le_inf (inf_le_left.trans (critical_Z_le_stabilizer d.radical
        (replacementGeometry h d) a p.start_color (by
          rw [(replacementGeometry h d).distance_constant a p.start_color]
          exact replacementDistance_pos h d) p.critical)) inf_le_right
    · exact inf_le_inf_left _ (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a p.start_color)))
  have hfail : ¬ ⁅Z d.radical z,P⁆ ≤
      ⁅Z d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)),P⁆ ⊔
        ⁅Z d.radical z,Z d.radical a⁆ := by
    rw [hfixed,hHwhole]
    intro hh
    apply hnorm
    apply le_normalizer_iff_commutator_le_right.mpr
    exact hh.trans (sup_le hHP (hcrit.trans le_sup_right))
  have hzt : Adjacent d.radical z (p.walk.getVert 3) := by
    have hh := p.walk.adj_getVert_succ (i := 3) (by omega)
    rw [show 3+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have hAlast : Z d.radical a ≤ Q d.radical (p.walk.getVert 3) := by
    apply Z_le_Q_of_dist_lt d.radical a ((replacementGeometry h d).exists_critical a p.start_color)
    rw [(replacementGeometry h d).distance_constant a p.start_color,p.dist_start (by omega)]
    exact show 3 < replacementDistance h d by omega
  have hlast : color d.radical (p.walk.getVert 3) = true := by
    have hh := (p.vertex_color (i := 3) (by omega))
    cases he : color d.radical (p.walk.getVert 3)
    · have := hh.mp he
      norm_num at this
    · rfl
  have hKlast : K ≤ Q d.radical (p.walk.getVert 3) :=
    inf_le_right.trans (Q_le_adjacent_h d.radical hlast
      ((cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))))
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a p.start_color
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) c hcCol
  let : IsElementaryAbelian 2 K := IsElementaryAbelian.of_le inf_le_left
  have hPelem : IsElementaryAbelian 2 P :=
    IsElementaryAbelian.sup_of_le_centralizer
      ((commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a p.start_color)).trans
        (centralizer_le hKQa))
  let := finite_Z d.radical z
  let : Finite (U d.radical z) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical z)) (inclusion_injective _)
  have hindex : (centralizer (Z d.radical a : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical z) ≤ 2 := by
    have hQC := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a p.start_color))
    exact ((relIndex_le_of_le_left hQC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical z) index_ne_zero_of_finite)).trans_eq
        (small_critical_indices s hc p hsmall).2
  have hbounds := elementary_edge_kernel_small_aligned s hc p.end_color hzt
    (Z d.radical a) P hAlast (sup_le hKlast hAlast) le_sup_right hPelem
    p.critical.2 hindex hfail
  rw [hfixed,hHwhole] at hbounds
  have hne : H ≠ ⊥ := by
    intro hzero
    have hmove := small_critical_kernel_commutator s hc p hsmall K hKGz
      (commutator_eq_bot_iff_le_centralizer.mp hzero)
    have hbound := commutator_sup_le_of_relative_normal (stabilizer d.radical a)
      K (Z d.radical a) (Z d.radical z) (Z d.radical a)
      (Z_normalized d.radical a) hKGa (Z_le_stabilizer d.radical a)
      (hmove.trans (by rwa [commutator_comm] at hcrit)) (by rwa [commutator_comm] at hcrit)
    exact hnorm (le_normalizer_iff_commutator_le_left.mpr (hbound.trans le_sup_right))
  let : Finite H := Finite.of_injective (inclusion hHZ) (inclusion_injective _)
  have hlo := (one_lt_card_iff_ne_bot H).mpr hne
  refine ⟨by change Nat.card H = 2; omega,le_inf (hHK.trans inf_le_left) hHZ,?_⟩
  simpa only [commutator_comm (Z d.radical z) (Z d.radical a)] using hbounds.2


include s in
/-- Failure of the full-kernel normalization produces the source line in
all three full seeds, and forces full omega central generation everywhere. -/
theorem small_backward_kernel_nonnormal_three_seed_line
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    {a z c : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (hcCol : color d.radical c = false)
    (hca : (cosetGraph d.radical).dist c a ≤ 2)
    (hnorm : ¬ Z d.radical z ≤ normalizer
      (((Z d.radical c ⊓ Q d.radical (p.walk.getVert 2)) ⊔
        Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    let K := Z d.radical c ⊓ Q d.radical (p.walk.getVert 2)
    let F := Z d.radical z ⊓ Q d.radical a
    (∀ w : Vertex d.radical, color d.radical w = false →
      X d.radical w = U d.radical w ⊔
        (X d.radical w ⊓ centralizer (stabilizer d.radical w : Set (FreeAmalgam d.radical)))) ∧
    Nat.card (⁅K,F⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
      ⁅K,F⁆ ≤ Z d.radical c ⊓ Z d.radical (p.walk.getVert 2) ⊓ Z d.radical z := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  let v := p.walk.getVert 2
  let t := p.walk.getVert 3
  have hv : color d.radical v = false := (p.vertex_color (by omega)).mpr (by decide)
  have hav : (cosetGraph d.radical).dist a v = 2 := p.dist_start (by omega)
  have hvz : (cosetGraph d.radical).dist v z = 2 := by rw [p.dist_end,hl]
  have hvt : Adjacent d.radical v t :=
    (cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have hzt : Adjacent d.radical z t := by
    have hh := p.walk.adj_getVert_succ (i := 3) (by omega)
    rw [show 3+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hvt
    rw [hv] at hh
    cases ht : color d.radical t <;> simp_all
  have hgen := (small_backward_kernel_normalized_or_centrally_generated s hc hb p
    hsmall hcCol hca).resolve_left hnorm
  obtain ⟨hcard,hseed,halign⟩ :=
    small_backward_kernel_nonnormal_line s hc hb p hsmall hcCol hca hnorm
  have hXa := SylowPairedFixer.central_generation_eq_seed (h := h) hv hvt (hgen v hv)
  have hZaV : Z d.radical a ≤ V d.radical v :=
    (Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hav.le)
  have hZzV : Z d.radical z ≤ V d.radical v :=
    (Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical (by rw [SimpleGraph.dist_comm]; exact hvz.le))
  have hcomm : ⁅Z d.radical a,Z d.radical z⁆ ≤ Z d.radical v :=
    (commutator_mono hZaV hZzV).trans ((radius_bounds_general s hc hb2 hv a z).2.1.trans_eq hXa)
  have hcent : Z d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical)) ≤
      Z d.radical v := by
    apply le_trans _ (adjacent_Z_le d.radical hv hvt)
    intro x hx
    rw [Z,if_neg (by simp [ht])]
    have hZzX : Z d.radical z ≤ X d.radical z := by
      apply (replacementGeometry h d).omega_bound z p.end_color
      rw [(replacementGeometry h d).distance_constant z p.end_color]
      exact replacementDistance_pos h d
    obtain ⟨hxQ,hx2,_⟩ := mem_omegaCenter_iff.mp (hZzX hx.1)
    exact mem_omegaCenter_iff.mpr ⟨Q_le_adjacent_h d.radical ht hzt hxQ,hx2,
      fun y hy => hx.2 y (hy.2 z (adjacent_symm d.radical hzt))⟩
  exact ⟨hgen,hcard,le_inf (le_inf (hseed.trans inf_le_left)
    (halign.trans (sup_le hcomm hcent))) (hseed.trans inf_le_right)⟩




end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

