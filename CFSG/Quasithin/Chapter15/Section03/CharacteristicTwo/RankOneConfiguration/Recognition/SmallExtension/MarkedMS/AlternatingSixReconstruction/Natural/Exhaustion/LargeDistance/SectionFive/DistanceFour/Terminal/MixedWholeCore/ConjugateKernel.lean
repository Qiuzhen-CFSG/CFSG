module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore.Source
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Normalization transfer between the full mixed backward kernels

The full backward kernel is the intersection of its seed with the
centralizer of the selected orbit span. The starting seed centralizes this
span as well. Consequently, intersecting any larger backward-kernel join
with that centralizer recovers the original join, including its entire
central attachment. An actor in the starting stabilizer normalizes the
centralizer, so normalization of the larger join implies normalization of
the original join. This argument does not identify the two kernels.

Apply the identity to the conjugate midpoint core supplied by the same
paired generator. The original paired obstruction now forces a source
normalization failure in one of the two literal endpoint orientations.
The alpha-based consumer constructs its order-two failure line in the
corresponding three full seeds, retaining both generation identities,
the original backward shift and the common conjugator.

This resolves the kernel comparison needed to form the conjugate source
failure line. Fixation of that second line and the two estimates for the
whole residual core `[Q_v,Ltilde_v]` remain unproved. These normalization
calculations do not assert the mixed terminal exclusion.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the full-kernel normalizations in (5.12)(1),(3), pp.924--927.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}


private theorem joined_intersection {F : Type*} [Group F]
    (T Z D : Subgroup F) (hZT : Z ≤ normalizer (T : Set F)) (hZD : Z ≤ D) :
    (T ⊔ Z) ⊓ D = (T ⊓ D) ⊔ Z := by
  apply le_antisymm
  · rintro x ⟨hx,hD⟩
    have hx' : x ∈ (T : Set F) * (Z : Set F) := by
      rw [←coe_mul_of_right_le_normalizer_left T Z hZT]
      exact hx
    obtain ⟨t,ht,z,hz,rfl⟩ := hx'
    have htD : t ∈ D := (D.mul_mem_cancel_right (hZD hz)).mp hD
    exact mul_mem_sup ⟨ht,htD⟩ hz
  · exact sup_le (le_inf (inf_le_left.trans le_sup_left) inf_le_right)
      (le_inf le_sup_right hZD)

/-- The original full kernel join is recovered by intersecting any larger
backward kernel join with the centralizer of the same orbit span. -/
theorem backward_kernel_join_intersection_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (q : MixedBackwardShift (h := h) p)
    (T : Subgroup (FreeAmalgam d.radical))
    (hKT : Z d.radical q.start ⊓ Q d.radical (p.walk.getVert 2) ≤ T)
    (hTZ : T ≤ Z d.radical q.start) :
    (T ⊔ Z d.radical a) ⊓
        centralizer (localZSpan d.radical (p.walk.getVert 2) a : Set (FreeAmalgam d.radical)) =
      (Z d.radical q.start ⊓ Q d.radical (p.walk.getVert 2)) ⊔ Z d.radical a := by
  let P := localZSpan d.radical (p.walk.getVert 2) a
  let C := centralizer (P : Set (FreeAmalgam d.radical))
  let K := Z d.radical q.start ⊓ Q d.radical (p.walk.getVert 2)
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hPQ : P ≤ Q d.radical a := (localZSpan_le_V d.radical
    (by rw [SimpleGraph.dist_comm,p.dist_start (by omega)])).trans
      (V_le_Q d.radical p.start_color hb2)
  obtain ⟨hZP,hcenter,_,_⟩ := mixed_backward_kernel_center_data_knownSimple hb u him p q
  have hKC : K ≤ C := mixed_backward_kernel_centralizes_span_knownSimple hb u him p q
  have hZC : Z d.radical q.start ⊓ C = K := by
    apply le_antisymm
    · rintro y ⟨hy,hc⟩
      apply hcenter.ge
      refine ⟨hy,⟨⟨y,hZP hy⟩,mem_center_iff.mpr ?_,rfl⟩⟩
      intro v
      exact Subtype.ext (hc v v.property)
    · exact le_inf inf_le_left hKC
  have hTC : T ⊓ C = K := le_antisymm
    ((inf_le_inf_right C hTZ).trans_eq hZC) (le_inf hKT hKC)
  have hZaC : Z d.radical a ≤ C :=
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a p.start_color)).trans
      (centralizer_le hPQ)
  have hZaT : Z d.radical a ≤ normalizer (T : Set (FreeAmalgam d.radical)) :=
    (hZaC.trans (centralizer_le (hTZ.trans hZP))).trans (Subgroup.centralizer_le_normalizer _)
  change (T ⊔ Z d.radical a) ⊓ C = K ⊔ Z d.radical a
  rw [joined_intersection T (Z d.radical a) C hZaT hZaC,hTC]

/-- Normalizing an enlarged full backward kernel join suffices to normalize
the original join; the comparison uses the span centralizer, not kernel equality. -/
theorem backward_kernel_normalization_transfer_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (q : MixedBackwardShift (h := h) p)
    (T A : Subgroup (FreeAmalgam d.radical))
    (hKT : Z d.radical q.start ⊓ Q d.radical (p.walk.getVert 2) ≤ T)
    (hTZ : T ≤ Z d.radical q.start) (hAG : A ≤ stabilizer d.radical a)
    (hAN : A ≤ normalizer ((T ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    A ≤ normalizer (((Z d.radical q.start ⊓ Q d.radical (p.walk.getVert 2)) ⊔
      Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
  rw [←backward_kernel_join_intersection_knownSimple hb u him p q T hKT hTZ]
  exact (le_inf hAN
    ((hAG.trans (localZSpan_normalized d.radical (p.walk.getVert 2) a)).trans
      (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf

/-- With the same paired conjugator, a failure at the conjugate endpoint
also occurs for the full kernel cut out by the conjugate midpoint core. -/
theorem strict_conjugate_kernel_failure_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))) :
    ∃ q : MixedBackwardShift (h := h) p,
      ∃ x ∈ stabilizer d.radical a,
        Q d.radical q.edge ⊔ Q d.radical (act d.radical x⁻¹ q.edge) = stabilizer d.radical a ∧
        Q d.radical q.edge ⊔ Z d.radical z ⊔ Z d.radical (act d.radical x z) =
          stabilizer d.radical a ∧
        Z d.radical q.start ⊓ Q d.radical (p.walk.getVert 2) ≤
          Q d.radical (act d.radical x (p.walk.getVert 2)) ∧
        (¬ Z d.radical z ≤ normalizer
          (((Z d.radical q.start ⊓ Q d.radical (p.walk.getVert 2)) ⊔
            Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) ∨
         ¬ Z d.radical (act d.radical x z) ≤ normalizer
          (((Z d.radical q.start ⊓ Q d.radical (act d.radical x (p.walk.getVert 2))) ⊔
            Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)) := by
  obtain ⟨q,x,hx,hpair,hend,hkernel,hbad⟩ :=
    strict_paired_failure_knownSimple hb u him p hstrict
  refine ⟨q,x,hx,hpair,hend,hkernel,?_⟩
  rcases hbad with hbad | hbad
  · exact Or.inl hbad
  · refine Or.inr (fun hnorm => hbad ?_)
    exact backward_kernel_normalization_transfer_knownSimple hb u him p q
      (Z d.radical q.start ⊓ Q d.radical (act d.radical x (p.walk.getVert 2)))
      (Z d.radical (act d.radical x z)) (le_inf inf_le_left hkernel) inf_le_left
      (le_sup_right.trans_eq hend) hnorm

/-- The literal alpha-based strict mixed branch supplies an order-two source
failure line in either endpoint orientation. The second line uses the full
kernel of the conjugate midpoint and the same paired conjugator throughout. -/
theorem strict_source_conjugate_kernel_lines_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))) :
    ∃ q : MixedBackwardShift (h := h) p,
      ∃ x ∈ stabilizer d.radical (alpha d.radical),
        Q d.radical q.edge ⊔ Q d.radical (act d.radical x⁻¹ q.edge) =
          stabilizer d.radical (alpha d.radical) ∧
        Q d.radical q.edge ⊔ Z d.radical z ⊔ Z d.radical (act d.radical x z) =
          stabilizer d.radical (alpha d.radical) ∧
        Z d.radical q.start ⊓ Q d.radical (p.walk.getVert 2) ≤
          Q d.radical (act d.radical x (p.walk.getVert 2)) ∧
        ((let H := ⁅Z d.radical q.start ⊓ Q d.radical (p.walk.getVert 2),
            Z d.radical z ⊓ Q d.radical (alpha d.radical)⁆;
          Nat.card H = 2 ∧ H ≤ Z d.radical q.start ⊓ Z d.radical (p.walk.getVert 2) ⊓
            Z d.radical z ∧
          H ≤ centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical))) ∨
         (let H := ⁅Z d.radical q.start ⊓ Q d.radical (act d.radical x (p.walk.getVert 2)),
            Z d.radical (act d.radical x z) ⊓ Q d.radical (alpha d.radical)⁆;
          Nat.card H = 2 ∧ H ≤ Z d.radical q.start ⊓
            Z d.radical (act d.radical x (p.walk.getVert 2)) ⊓ Z d.radical (act d.radical x z))) := by
  obtain ⟨q,x,hx,hpair,hend,hkernel,hbad⟩ :=
    strict_conjugate_kernel_failure_knownSimple hb u him p hstrict
  refine ⟨q,x,hx,hpair,hend,hkernel,?_⟩
  rcases hbad with hbad | hbad
  · obtain ⟨hcard,_,hfix,hseeds⟩ :=
      mixed_backward_failure_line_knownSimple hb u him p q hstrict hbad
    exact Or.inl ⟨hcard,hseeds,hfix⟩
  · have hl : p.walk.length = 4 := p.length_eq_b.trans hb
    have hq2 : q.path.walk.getVert 2 = alpha d.radical := by
      simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using q.overlap 0 (Nat.zero_le _)
    have hql : q.path.walk.length = 4 := q.path.length_eq_b.trans hb
    have hnear : (cosetGraph d.radical).dist q.start (alpha d.radical) ≤ 2 := by
      simpa only [hq2] using (q.path.dist_start (i := 2) (by omega)).le
    have hxa : act d.radical x (alpha d.radical) = alpha d.radical := hx
    let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
    have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
    have hsmall := critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb (p.act x)
    have hnearx : (cosetGraph d.radical).dist q.start (act d.radical x (alpha d.radical)) ≤ 2 := by
      rwa [hxa]
    have hh := small_backward_kernel_nonnormal_three_seed_line s hc hb (p.act x) hsmall
      q.path.start_color hnearx
    simp only [CriticalPath.act,actWalk_getVert,hxa] at hh
    obtain ⟨_,hcard,hseeds⟩ := hh hbad
    exact Or.inr ⟨hcard,hseeds⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
