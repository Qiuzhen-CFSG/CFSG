module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeKernelChoice

/-!
# The actual shifted-span comparisons in the three-pair branch

The selected order-two seed-kernel commutator cannot contain the kernel
movement of an escaping normal local span. Pulling the kernel back through
that same selected conjugator gives an actor outside the shifted vertex's
two-core. A displacement bound in its seed would put the normal span in the
Baumann subgroup, a contradiction. The established order-four bound for the
whole predecessor-kernel commutator is consequently attained. Joining the
selected line with either actual Y/W displacement gives that full commutator.

The aligned-line uniqueness theorem then excludes the alignment alternative
for each span. The remaining alternative gives the literal full-endpoint
commutator bounds of MS93 (5.9). The centralizing supplement contains the
starting core, and its join with the endpoint seed is the whole starting
stabilizer; these bounds therefore make W invariant under that whole group.
This conclusion concerns W. Centrality of R₃ under that stabilizer is not
inferred from its order or its independence among admissible choices.

The same selected x places R₃ and the retained forward line in one shifted
edge seed. Reselecting Y by x preserves its P-conjugate span W. The consumer
retains the original y, both paths and their overlap, all supplements,
full-X and full-kernel identities, and every previous admissible-choice
comparison. It preserves both moved covers and all central attachments.
The span-collapse step W = Y, strict forward-slice contradiction, terminal,
Sylow and distance-four branches, and unconditional distance bound remain
with the large-distance assembly owner.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.3) and (5.9), printed pp.866--867,920--922. All groups and maps
are those of the original natural minimum characteristic replacement.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped commutatorElement IsMulCommutative Pointwise
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u

variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)


include s in
/-- A nonzero selected seed-kernel line and its escaping normal local span
force the entire predecessor-kernel commutator to have order four. The span's
kernel displacement is not confined to the selected line. -/
theorem cube_predecessor_kernel_saturated
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hR : d.radical.map s.projection ≤ (CFSG.Quasithin.ChapterB.Offenders.D 6).map
      (MulAut.conj u).toMonoidHom)
    {c z a : Vertex d.radical}
    (q : CriticalPath d.radical (replacementGeometry h d) c z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical c) < 4)
    (ha : color d.radical a = false) (hca : (cosetGraph d.radical).dist c a ≤ 2)
    (Y : Subgroup (FreeAmalgam d.radical)) (hYV : Y ≤ V d.radical a)
    (hYN : stabilizer d.radical a ≤ normalizer (Y : Set (FreeAmalgam d.radical)))
    (hYB : ¬ Y ≤ B d.radical a ((replacementGeometry h d).Z_normal _))
    (x : FreeAmalgam d.radical) (hx : x ∈ stabilizer d.radical c)
    (hZpre : (Z d.radical a).map (MulAut.conj x).toMonoidHom ≤
      Q d.radical (q.walk.getVert (q.walk.length-2)))
    (hYpre : Y.map (MulAut.conj x).toMonoidHom ≤
      Q d.radical (q.walk.getVert (q.walk.length-2)))
    (hcard : Nat.card (⁅(Z d.radical a).map (MulAut.conj x).toMonoidHom,
      Z d.radical z ⊓ Q d.radical c⁆ : Subgroup (FreeAmalgam d.radical)) = 2) :
    let K := Z d.radical z ⊓ Q d.radical c
    let J := ⁅(Z d.radical a).map (MulAut.conj x).toMonoidHom,K⁆
    let N := ⁅K,Q d.radical (q.walk.getVert (q.walk.length-2))⁆
    Nat.card N = 4 ∧
      ¬ ⁅Y.map (MulAut.conj x).toMonoidHom,K⁆ ≤ J ∧
      J ⊔ ⁅Y.map (MulAut.conj x).toMonoidHom,K⁆ = N := by
  let K := Z d.radical z ⊓ Q d.radical c
  let f := (MulAut.conj x).toMonoidHom
  let fi := (MulAut.conj x⁻¹).toMonoidHom
  let A := K.map fi
  let J := ⁅(Z d.radical a).map f,K⁆
  let N := ⁅K,Q d.radical (q.walk.getVert (q.walk.length-2))⁆
  have hAf : A.map f = K := by
    rw [map_map]
    have he : f.comp fi = MonoidHom.id (FreeAmalgam d.radical) := by
      apply MonoidHom.ext
      intro v
      change x*(x⁻¹*v*(x⁻¹)⁻¹)*x⁻¹ = v
      group
    rw [he,map_id]
  have hAQ : A ≤ Q d.radical c :=
    (map_mono (show K ≤ Q d.radical c from inf_le_right)).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp
        ((Q_normalized d.radical c) ((stabilizer d.radical c).inv_mem hx)))
  have hAG : A ≤ stabilizer d.radical a := hAQ.trans
    (Q_le_stabilizer_of_dist_le_two c a q.start_color ha hca)
  have hZA : ⁅Z d.radical a,A⁆ ≤ Z d.radical a :=
    le_normalizer_iff_commutator_le_left.mp (hAG.trans (Z_normalized d.radical a))
  have hZAmap : (⁅Z d.radical a,A⁆ : Subgroup (FreeAmalgam d.radical)).map f = J := by
    rw [map_commutator,hAf]
  have hne : ¬ A ≤ Q d.radical a := by
    intro hAcore
    have hzero : ⁅Z d.radical a,A⁆ = ⊥ := le_bot_iff.mp
      ((commutator_mono le_rfl hAcore).trans_eq (Z_centralizes_Q d.radical a ha))
    rw [hzero,Subgroup.map_bot] at hZAmap
    change Nat.card J = 2 at hcard
    rw [←hZAmap,card_bot] at hcard
    omega
  have hnot : ¬ ⁅Y.map f,K⁆ ≤ J := by
    intro hle
    have hYA : ⁅Y,A⁆ ≤ Z d.radical a := by
      apply le_trans _ hZA
      apply (map_le_map_iff_of_injective (f := f) (MulAut.conj x).injective).mp
      rwa [hZAmap,map_commutator,hAf]
    exact hYB (normalized_radius_le_slice_of_actor_at s hb ha Y A hYV hYN hAG hne hYA)
  have hcardN : Nat.card N ≤ 4 := cube_small_critical_kernel_predecessor_card s hc hb u hR q hsmall
  have hJN : J ≤ N := by
    dsimp only [J,N]
    rw [commutator_comm ((Z d.radical a).map f)]
    exact commutator_mono le_rfl hZpre
  have hYN' : ⁅Y.map f,K⁆ ≤ N := by
    rw [commutator_comm]
    exact commutator_mono le_rfl hYpre
  let v := q.walk.getVert (q.walk.length-2)
  have hvcol : color d.radical v = false := by
    apply (q.vertex_color (Nat.sub_le _ _)).mpr
    have he := replacementDistance_even h d
    rw [Nat.even_iff] at he ⊢
    have hl : q.walk.length = replacementDistance h d := q.length_eq_b
    omega
  have hvz : (cosetGraph d.radical).dist v z = 2 := by
    rw [q.dist_end]
    have hl : q.walk.length = replacementDistance h d := q.length_eq_b
    omega
  have hNZ : N ≤ Z d.radical z :=
    (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp
        ((Q_le_stabilizer_of_dist_two d.radical v z hvcol hvz).trans (Z_normalized d.radical z)))
  let := finite_Z d.radical z
  let : Finite N := Finite.of_injective (inclusion hNZ) (inclusion_injective _)
  have hlarge : 2 < Nat.card N := by
    by_contra! hsmallN
    have heq : J = N := eq_of_le_of_card_ge hJN (by change Nat.card J = 2 at hcard; omega)
    exact hnot (hYN'.trans_eq heq.symm)
  have heven : 2 ∣ Nat.card N := by
    have hd := card_dvd_of_le hJN
    change Nat.card J = 2 at hcard
    rwa [hcard] at hd
  have hNcard : Nat.card N = 4 := by omega
  let E := J ⊔ ⁅Y.map f,K⁆
  have hEN : E ≤ N := sup_le hJN hYN'
  let : Finite E := Finite.of_injective (inclusion hEN) (inclusion_injective _)
  have hJE : J ≤ E := le_sup_left
  have hElarge : 2 < Nat.card E := by
    by_contra! hsmallE
    have heq : J = E := eq_of_le_of_card_ge hJE (by change Nat.card J = 2 at hcard; omega)
    exact hnot ((show ⁅Y.map f,K⁆ ≤ E from le_sup_right).trans_eq heq.symm)
  have hEeven : 2 ∣ Nat.card E := by
    have hd := card_dvd_of_le hJE
    change Nat.card J = 2 at hcard
    rwa [hcard] at hd
  have hEcard : Nat.card E ≤ Nat.card N := card_le_of_le hEN
  have hENeq : E = N := eq_of_le_of_card_ge hEN (by omega)
  exact ⟨hNcard,hnot,hENeq⟩


include s in
/-- A kernel displacement escaping the retained aligned line forces the
full endpoint displacement into the source control alternative. -/
theorem cube_edge_control_of_kernel_escape
    (hc : DistanceTwo.CentralLayer d) (u : Equiv.Perm (Fin 6))
    (hR : d.radical.map s.projection ≤ (CFSG.Quasithin.ChapterB.Offenders.D 6).map
      (MulAut.conj u).toMonoidHom)
    {c z t : Vertex d.radical}
    (q : CriticalPath d.radical (replacementGeometry h d) c z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical c) < 4)
    (hzt : Adjacent d.radical z t) (hct : Z d.radical c ≤ Q d.radical t)
    (D P : Subgroup (FreeAmalgam d.radical))
    (hDt : D ≤ Q d.radical t) (hPt : P ≤ Q d.radical t)
    (hne : ⁅D,Z d.radical z ⊓ Q d.radical c⁆ ≠ ⊥)
    (halign : ⁅D,Z d.radical z ⊓ Q d.radical c⁆ ≤
      ⁅Z d.radical c,Z d.radical z⁆ ⊔
        (stabilizer d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))))
    (hnot : ¬ ⁅P,Z d.radical z ⊓ Q d.radical c⁆ ≤ ⁅D,Z d.radical z ⊓ Q d.radical c⁆) :
    ⁅P,Z d.radical z⁆ ≤ ⁅P,Z d.radical z ⊓ Q d.radical c⁆ ⊔
      ⁅Z d.radical c,Z d.radical z⁆ := by
  let K := Z d.radical z ⊓ Q d.radical c
  have hZG : Z d.radical z ≤ stabilizer d.radical c :=
    critical_Z_le_stabilizer d.radical (replacementGeometry h d) c q.start_color (by
      rw [(replacementGeometry h d).distance_constant c q.start_color]
      exact replacementDistance_pos h d) q.critical
  have hfixed : K = Z d.radical z ⊓ centralizer (Z d.radical c : Set (FreeAmalgam d.radical)) := by
    dsimp only [K]
    rw [←C_eq_Q s hc c q.start_color]
    apply le_antisymm (inf_le_inf_left _ inf_le_right)
    exact le_inf inf_le_left (le_inf (inf_le_left.trans hZG) inf_le_right)
  let := finite_Z d.radical z
  let : Finite (U d.radical z) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical z)) (inclusion_injective _)
  have hQC : Q d.radical c ≤ centralizer (Z d.radical c : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical c q.start_color))
  have hindex : (centralizer (Z d.radical c : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical z) ≤ 2 :=
    ((relIndex_le_of_le_left hQC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical z) index_ne_zero_of_finite)).trans_eq
        (small_critical_indices s hc q hsmall).2
  rcases cube_edge_alignment_or_control s hc u hR q.end_color hzt
    (Z d.radical c) P hct hPt q.critical.2 hindex with hA | hC
  · have hPe : ⁅K,P⁆ ≠ ⊥ := by
      intro he
      apply hnot
      rw [commutator_comm]
      exact he ▸ bot_le
    have hDe : ⁅K,D⁆ ≠ ⊥ := by rwa [commutator_comm]
    have hDalign : ⁅K,D⁆ ≤ ⁅Z d.radical c,Z d.radical z⁆ ⊔
        (stabilizer d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))) := by
      rwa [commutator_comm]
    have heq := cube_aligned_kernel_line_unique s hc u hR q hsmall hzt hct
      D P hDt hPt hDe hPe hDalign (by
        simpa only [←hfixed,commutator_comm (Z d.radical z) (Z d.radical c)] using hA)
    exact False.elim (hnot (by rw [commutator_comm P,commutator_comm D]; exact heq.symm.le))
  · simpa only [←hfixed,commutator_comm (Z d.radical z) P,commutator_comm K P,
      commutator_comm (Z d.radical z) (Z d.radical c)] using hC

/-- The literal nonsylow configuration saturates its opposite kernel and
separates the actual Y/W displacements from R₃. The same selected conjugator
places both retained lines in one edge seed, and reselection preserves W. -/
theorem nonsylow_small_shifted_span_control_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2)
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4) :
    let c := p.walk.getVert 2
    let T := Q d.radical (alpha d.radical) ⊓ centralizer
      (U d.radical c ⊓ B d.radical (alpha d.radical)
        ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
    let H := ⁅U d.radical c,T⁆
    ∃ z, ∃ q : CriticalPath d.radical (replacementGeometry h d) c z,
      (cosetGraph d.radical).dist a' z = 2 ∧
      (∀ i ≤ p.walk.length-2, q.walk.getVert i = p.walk.getVert (i+2)) ∧
      q.walk.getVert (q.walk.length-2) = a' ∧
      (Q d.radical z).relIndex (Z d.radical c) = 2 ∧
      ∃ y ∈ Ltilde d.radical c,
        let a := act d.radical y⁻¹ (alpha d.radical)
        let T₂ := T.map (MulAut.conj y).toMonoidHom
        let H₂ := H.map (MulAut.conj y).toMonoidHom
        let Y := (localZSpan d.radical c (alpha d.radical)).map (MulAut.conj y).toMonoidHom
        let P := stabilizer d.radical c ⊓ centralizer (H₂ : Set (FreeAmalgam d.radical))
        P ⊔ Z d.radical z = stabilizer d.radical c ∧
        ¬ H₂ ≤ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) ∧
        T₂ = Q d.radical a ⊓ centralizer
          (U d.radical c ⊓ B d.radical a ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical)) ∧
        Z d.radical c ≤ Y ∧ Y ≤ V d.radical a ∧
        stabilizer d.radical a ≤ normalizer (Y : Set (FreeAmalgam d.radical)) ∧
        ¬ Y ≤ B d.radical a ((replacementGeometry h d).Z_normal _) ∧
        H₂ ≤ Z d.radical a ∧ Nat.card H₂ = 2 ∧
        H₂ ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) ∧
        ⁅Y,T₂⁆ ≤ H₂ ∧ Z d.radical a ≤ Q d.radical a' ∧ Y ≤ Q d.radical a' ∧
        conjugateSpanBy (Z d.radical a) P ≤ Q d.radical a' ∧
        conjugateSpanBy Y P ≤ Q d.radical a' ∧
        Z d.radical a ≤ V d.radical c ∧
        ¬ Z d.radical a ≤ B d.radical c ((replacementGeometry h d).Z_normal _) ∧
        let J := ⁅conjugateSpanBy (Z d.radical a) P,Z d.radical z ⊓ Q d.radical c⁆
        Nat.card J = 2 ∧ J ≤ Z d.radical c ⊓ Z d.radical z ∧
        J ≤ Z d.radical (q.walk.getVert (q.walk.length-1)) ∧ J ≠ H₂ ∧
        let D := conjugateSpanBy (Z d.radical a) P
        let A₀ := X d.radical z ⊓ Q d.radical c
        let R₃ := ⁅D,A₀⁆
        (∀ v : Vertex d.radical, color d.radical v = false →
          X d.radical v = U d.radical v ⊔
            (X d.radical v ⊓ centralizer (stabilizer d.radical v : Set (FreeAmalgam d.radical)))) ∧
        A₀ = (Z d.radical z ⊓ Q d.radical c) ⊔
          (X d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))) ∧
        R₃ = J ∧ R₃ ≤ D ⊓ A₀ ∧
        (∃ x ∈ P,
          let w := act d.radical x⁻¹ a
          let t := act d.radical x⁻¹ (act d.radical y⁻¹ (p.walk.getVert 1))
          ⁅(Z d.radical a).map (MulAut.conj x).toMonoidHom,A₀⁆ = R₃ ∧
          Adjacent d.radical w t ∧ Adjacent d.radical c t ∧
          SmallMover.join (U d.radical w) (Q d.radical w) (Q d.radical t) 4 = Q d.radical t ∧
          SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 = Q d.radical t ∧
          A₀ ≤ SmallMover.join (U d.radical w) (Q d.radical w) (Q d.radical t) 4 ∧
          R₃ ≤ Z d.radical t ∧
          H₂ ≤ Z d.radical t ∧ R₃ ≤ Z d.radical w ∧
          conjugateSpanBy (Y.map (MulAut.conj x).toMonoidHom) P = conjugateSpanBy Y P ∧
          ¬ ⁅Y.map (MulAut.conj x).toMonoidHom,A₀⁆ ≤ R₃ ∧
          ⁅Y.map (MulAut.conj x).toMonoidHom,Z d.radical z⁆ ≤
            ⁅Y.map (MulAut.conj x).toMonoidHom,A₀⁆ ⊔ ⁅Z d.radical c,Z d.radical z⁆ ∧
          R₃ ⊔ ⁅Y.map (MulAut.conj x).toMonoidHom,A₀⁆ =
            ⁅Z d.radical z ⊓ Q d.radical c,Q d.radical a'⁆ ∧
          R₃ ≤ centralizer
            ((SmallMover.join (U d.radical w) (Q d.radical w) (Q d.radical t) 4 ⊔
              SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 :
                Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))) ∧
        ⁅D,X d.radical z⁆ = ⁅D,Z d.radical z⁆ ∧
        ¬ ⁅D,X d.radical z⁆ ≤ R₃ ⊔ ⁅Z d.radical c,Z d.radical z⁆ ∧
        R₃ ≤ ⁅Z d.radical c,Z d.radical z⁆ ⊔
          (stabilizer d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))) ∧
        ⁅Y,X d.radical z⁆ = ⁅Y,Z d.radical z⁆ ∧
        ⁅Y,A₀⁆ = ⁅Y,Z d.radical z ⊓ Q d.radical c⁆ ∧
        ⁅conjugateSpanBy Y P,X d.radical z⁆ = ⁅conjugateSpanBy Y P,Z d.radical z⁆ ∧
        ⁅conjugateSpanBy Y P,A₀⁆ = ⁅conjugateSpanBy Y P,Z d.radical z ⊓ Q d.radical c⁆ ∧
        Nat.card (⁅Z d.radical z ⊓ Q d.radical c,Q d.radical a'⁆ :
          Subgroup (FreeAmalgam d.radical)) = 4 ∧
        ¬ ⁅conjugateSpanBy Y P,A₀⁆ ≤ R₃ ∧
        R₃ ⊔ ⁅conjugateSpanBy Y P,A₀⁆ = ⁅Z d.radical z ⊓ Q d.radical c,Q d.radical a'⁆ ∧
        ⁅conjugateSpanBy Y P,Z d.radical z⁆ ≤
          ⁅conjugateSpanBy Y P,A₀⁆ ⊔ ⁅Z d.radical c,Z d.radical z⁆ ∧
        stabilizer d.radical c ≤ normalizer (conjugateSpanBy Y P : Set (FreeAmalgam d.radical)) ∧
        ∀ y' ∈ stabilizer d.radical c,
          let H' := H.map (MulAut.conj y').toMonoidHom
          let P' := stabilizer d.radical c ⊓ centralizer (H' : Set (FreeAmalgam d.radical))
          P' ⊔ Z d.radical z = stabilizer d.radical c →
          (¬ H' ≤ centralizer (Z d.radical z : Set (FreeAmalgam d.radical))) →
          ⁅conjugateSpanBy (Z d.radical (act d.radical y'⁻¹ (alpha d.radical))) P',A₀⁆ = R₃ := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨z,q,hd,hover,hpre,hi,y,hy,hgen,hmove,hT,hZcY,hYV,hYN,hYB,hHZa,hcard,hHCa,
    hcomm,hZaQ,hYQ,hDQ,hWQ,hZaV,hZaB,hJcard,hJseed,hJedge,hJne,
    hXall,hA₀,hR₃,hRDA,⟨x,hx,hline,hwt,hct,hJw,hJc,hAedge,hRedge,hRfix⟩,
    hfull,hnot,halign,hYdisp,hYker,hWdisp,hWker,hchoices⟩ :=
    nonsylow_small_shifted_kernel_independence_knownSimple (e := e) (hz := hz) (hn := hn)
      hb hns p hslice hsmall
  let c := p.walk.getVert 2
  let a := act d.radical y⁻¹ (alpha d.radical)
  let T := Q d.radical (alpha d.radical) ⊓ centralizer
    (U d.radical c ⊓ B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
  let H₂ := (⁅U d.radical c,T⁆ : Subgroup (FreeAmalgam d.radical)).map (MulAut.conj y).toMonoidHom
  let Y := (localZSpan d.radical c (alpha d.radical)).map (MulAut.conj y).toMonoidHom
  let P := stabilizer d.radical c ⊓ centralizer (H₂ : Set (FreeAmalgam d.radical))
  let D := conjugateSpanBy (Z d.radical a) P
  let A₀ := X d.radical z ⊓ Q d.radical c
  let R₃ := ⁅D,A₀⁆
  let f := (MulAut.conj x).toMonoidHom
  have hxP : x ∈ P := hx
  have hZxD : (Z d.radical a).map f ≤ D := by
    dsimp only [D]
    rw [conjugateSpanBy_eq_iSup_conj]
    exact le_iSup (fun k : P => (Z d.radical a).map
      (MulAut.conj (k : FreeAmalgam d.radical)).toMonoidHom) ⟨x,hxP⟩
  have hYxW : Y.map f ≤ conjugateSpanBy Y P := by
    rw [conjugateSpanBy_eq_iSup_conj]
    exact le_iSup (fun k : P => Y.map
      (MulAut.conj (k : FreeAmalgam d.radical)).toMonoidHom) ⟨x,hxP⟩
  have ha : color d.radical a = false := by
    rw [action_preserves_color]
    rfl
  have hca : (cosetGraph d.radical).dist c a = 2 := by
    have hfix : act d.radical y⁻¹ c = c :=
      (stabilizer d.radical c).inv_mem (Ltilde_le_stabilizer c hy)
    have hh := dist_act d.radical y⁻¹ c (alpha d.radical)
    rw [hfix,SimpleGraph.dist_comm (u := c) (v := alpha d.radical)] at hh
    exact hh.trans (p.dist_start (by
      have hl : p.walk.length = replacementDistance h d := p.length_eq_b
      omega))
  have hpreG : Q d.radical a' ≤ stabilizer d.radical z :=
    Q_le_stabilizer_of_dist_le_two a' z p.end_color q.end_color hd.le
  have hZxdisp := critical_X_displacements_of_central_generation s hc q
    (hXall z q.end_color) _ ((hZxD.trans hDQ).trans hpreG)
  have hYxdisp := critical_X_displacements_of_central_generation s hc q
    (hXall z q.end_color) _ ((hYxW.trans hWQ).trans hpreG)
  have hZxcard : Nat.card (⁅(Z d.radical a).map f,
      Z d.radical z ⊓ Q d.radical c⁆ : Subgroup (FreeAmalgam d.radical)) = 2 := by
    rw [←hZxdisp.2,hline,hR₃]
    exact hJcard
  obtain ⟨u,hu⟩ := nonsylow_four_lt_radical_image_cube_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns
  have hR : d.radical.map s.projection ≤ (CFSG.Quasithin.ChapterB.Offenders.D 6).map
      (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,hu]
  have hsaturated := cube_predecessor_kernel_saturated s hc hb2 u hR q
    (by rw [hi]; decide) ha hca.le Y hYV hYN hYB x hxP.1
    (by rw [hpre]; exact hZxD.trans hDQ)
    (by rw [hpre]; exact hYxW.trans hWQ) hZxcard
  have hYnot : ¬ ⁅Y.map f,A₀⁆ ≤ R₃ := by
    intro hle
    apply hsaturated.2.1
    rw [←hYxdisp.2,←hZxdisp.2,hline]
    exact hle
  have hWnot : ¬ ⁅conjugateSpanBy Y P,A₀⁆ ≤ R₃ :=
    fun hle => hYnot ((commutator_mono hYxW le_rfl).trans hle)
  have hYspan : R₃ ⊔ ⁅Y.map f,A₀⁆ = ⁅Z d.radical z ⊓ Q d.radical c,Q d.radical a'⁆ := by
    have hh := hsaturated.2.2
    rw [←hYxdisp.2,←hZxdisp.2,hline,hpre] at hh
    exact hh
  have hWspan : R₃ ⊔ ⁅conjugateSpanBy Y P,A₀⁆ =
      ⁅Z d.radical z ⊓ Q d.radical c,Q d.radical a'⁆ := by
    have hRN : R₃ ≤ ⁅Z d.radical z ⊓ Q d.radical c,Q d.radical a'⁆ :=
      (show R₃ ≤ R₃ ⊔ ⁅Y.map f,A₀⁆ from le_sup_left).trans_eq hYspan
    have hWN : ⁅conjugateSpanBy Y P,A₀⁆ ≤
        ⁅Z d.radical z ⊓ Q d.radical c,Q d.radical a'⁆ := by
      rw [hWker,commutator_comm]
      exact commutator_mono le_rfl hWQ
    exact le_antisymm (sup_le hRN hWN)
      (hYspan.symm.le.trans (sup_le_sup_left (commutator_mono hYxW le_rfl) _))
  have hspan : conjugateSpanBy (Y.map f) P = conjugateSpanBy Y P := by
    have hPm := mem_normalizer_iff_map_conj_eq.mp (P.le_normalizer hxP)
    have hWm := mem_normalizer_iff_map_conj_eq.mp ((le_normalizer_conjugateSpanBy Y P) hxP)
    rw [map_conjugateSpanBy,hPm] at hWm
    exact hWm
  have hHedge : H₂ ≤ Z d.radical
      (act d.radical x⁻¹ (act d.radical y⁻¹ (p.walk.getVert 1))) := by
    have hline₀ := (selected_forward_kernel_line s hc hb2 p hslice).2
    have hh := map_mono (f := f) (map_mono (f := (MulAut.conj y).toMonoidHom) hline₀)
    have hHm : H₂.map f = H₂ := mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.centralizer_le_normalizer _) hxP.2)
    change H₂.map f ≤ _ at hh
    rw [hHm] at hh
    simpa only [Z_act,inv_inv] using hh
  have hRw : R₃ ≤ Z d.radical (act d.radical x⁻¹ a) :=
    hRedge.trans (adjacent_Z_le d.radical
      (by simpa only [action_preserves_color] using ha) hwt)
  have hlen : 2 < q.walk.length := q.length_eq_b ▸ hb2
  let last := q.walk.getVert (q.walk.length-1)
  have hzlast : Adjacent d.radical z last := by
    have hh := q.walk.adj_getVert_succ (i := q.walk.length-1) (by omega)
    rw [show q.walk.length-1+1=q.walk.length by omega,q.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have hlastcol : color d.radical last = true := by
    cases he : color d.radical last
    · exact False.elim ((adjacent_color_ne d.radical hzlast) (q.end_color.trans he.symm))
    · rfl
  have hprelast : Adjacent d.radical a' last := by
    have hh := q.walk.adj_getVert_succ (i := q.walk.length-2) (by omega)
    rw [show q.walk.length-2+1=q.walk.length-1 by omega,hpre] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have hQlast : Q d.radical a' ≤ Q d.radical last := Q_le_adjacent_h d.radical hlastcol hprelast
  have hZlast : Z d.radical c ≤ Q d.radical last := by
    apply Z_le_Q_of_dist_lt d.radical c ((replacementGeometry h d).exists_critical c q.start_color)
    rw [q.dist_start (Nat.sub_le _ _),(replacementGeometry h d).distance_constant c q.start_color]
    change q.walk.length-1 < replacementDistance h d
    have he : q.walk.length = replacementDistance h d := q.length_eq_b
    omega
  have hZxne : ⁅(Z d.radical a).map f,Z d.radical z ⊓ Q d.radical c⁆ ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hZxcard
    omega
  have hZxalign : ⁅(Z d.radical a).map f,Z d.radical z ⊓ Q d.radical c⁆ ≤
      ⁅Z d.radical c,Z d.radical z⁆ ⊔
        (stabilizer d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))) := by
    rw [←hZxdisp.2,hline]
    exact halign
  have hcontrols (E : Subgroup (FreeAmalgam d.radical)) (hEQ : E ≤ Q d.radical a')
      (hescape : ¬ ⁅E,A₀⁆ ≤ R₃) :
      ⁅E,Z d.radical z⁆ ≤ ⁅E,A₀⁆ ⊔ ⁅Z d.radical c,Z d.radical z⁆ := by
    have hEd := critical_X_displacements_of_central_generation s hc q
      (hXall z q.end_color) E (hEQ.trans hpreG)
    rw [hEd.2]
    apply cube_edge_control_of_kernel_escape s hc u hR q (by rw [hi]; decide)
      hzlast hZlast ((Z d.radical a).map f) E ((hZxD.trans hDQ).trans hQlast)
      (hEQ.trans hQlast) hZxne hZxalign
    rw [←hEd.2,←hZxdisp.2,hline]
    exact hescape
  have hYcontrol := hcontrols (Y.map f) (hYxW.trans hWQ) hYnot
  have hWcontrol := hcontrols (conjugateSpanBy Y P) hWQ hWnot
  have hHc : H₂ ≤ Z d.radical c := hHedge.trans (adjacent_Z_le d.radical q.start_color hct)
  have hQcP : Q d.radical c ≤ P :=
    le_inf (fun _ hx => hx.1)
      ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical c q.start_color))).trans (centralizer_le hHc))
  have hZG : Z d.radical z ≤ stabilizer d.radical c :=
    critical_Z_le_stabilizer d.radical (replacementGeometry h d) c q.start_color (by
      rw [(replacementGeometry h d).distance_constant c q.start_color]
      exact replacementDistance_pos h d) q.critical
  have hcrit : ⁅Z d.radical c,Z d.radical z⁆ ≤ Z d.radical c :=
    le_normalizer_iff_commutator_le_left.mp (hZG.trans (Z_normalized d.radical c))
  have hWN : stabilizer d.radical c ≤ normalizer (conjugateSpanBy Y P : Set (FreeAmalgam d.radical)) := by
    rw [←hgen]
    refine sup_le (le_normalizer_conjugateSpanBy _ _) ?_
    apply le_normalizer_iff_commutator_le_left.mpr
    exact hWcontrol.trans (sup_le
      (le_normalizer_iff_commutator_le_left.mp
        ((inf_le_right.trans hQcP).trans (le_normalizer_conjugateSpanBy _ _)))
      (hcrit.trans (hZcY.trans (le_conjugateSpanBy _ _))))
  refine ⟨z,q,hd,hover,hpre,hi,y,hy,hgen,hmove,hT,hZcY,hYV,hYN,hYB,hHZa,hcard,hHCa,
    hcomm,hZaQ,hYQ,hDQ,hWQ,hZaV,hZaB,hJcard,hJseed,hJedge,hJne,
    hXall,hA₀,hR₃,hRDA,⟨x,hx,hline,hwt,hct,hJw,hJc,hAedge,hRedge,
      hHedge,hRw,hspan,hYnot,hYcontrol,hYspan,hRfix⟩,hfull,hnot,halign,hYdisp,hYker,hWdisp,hWker,
    ?_,hWnot,hWspan,hWcontrol,hWN,hchoices⟩
  simpa only [hpre] using hsaturated.1

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
