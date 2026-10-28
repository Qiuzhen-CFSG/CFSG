module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTerminal
public import Theory.GroupTheory.CentralLineCentralizer
public import Theory.GroupTheory.ConjugateOrbitIndexTwo
public import Theory.GroupTheory.Commutator.ElementaryIndexTwoQuadratic
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.NonsylowImage
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowRestriction
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowNormalizer

/-!
# Normalizers and small critical kernels in the large-distance Sylow branch

Beyond distance four, the actual replacement radical has a non-elementary
image. Its image normalizer is a two-group, so the literal radical normalizer
is exactly the restriction of the original Sylow subgroup. This identifies
the actual relative edge normalizer at the base edge. For a small critical
endpoint, the order-two line commutator in the symmetric-six Sylow image gives
index at most two for the normalizer of the full critical seed kernel. The
proof retains the actual quotient maps and central attachment.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.5)--(5.8), pp.917--920, and the order-two Sylow image calculation
used with (5.11), pp.923--924. These local bounds do not exclude all
non-elementary branches or prove the distance-four case.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowSmallNormalizer
local notation "S" => Equiv.Perm (Fin 6)

private abbrev z : S := kleinFirst 6 (by decide)

private theorem sylow_commutator_line :
    ⁅sylowCarrier,sylowCarrier⁆ ≤ zpowers z ∧
      zpowers z ≤ centralizer (sylowCarrier : Set S) ∧
      Nat.card (zpowers z) = 2 := by
  refine ⟨?_,?_,?_⟩
  · apply commutator_le.mpr
    intro x hx y hy
    obtain ⟨i,rfl⟩ := (mem_sylowCarrier_iff x).mp hx
    obtain ⟨j,rfl⟩ := (mem_sylowCarrier_iff y).mp hy
    have ht : ∀ i j : Fin 16,
        ⁅sylowWords i,sylowWords j⁆ = 1 ∨ ⁅sylowWords i,sylowWords j⁆ = z := by
      decide +kernel
    rcases ht i j with he | he
    · rw [he]; exact one_mem _
    · rw [he]; exact mem_zpowers z
  · apply zpowers_le.mpr
    intro x hx
    obtain ⟨i,rfl⟩ := (mem_sylowCarrier_iff x).mp hx
    exact (by decide +kernel : ∀ i : Fin 16, sylowWords i*z=z*sylowWords i) i
  · rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by decide : z^2=1) (by decide : z ≠ 1)

private theorem sylow_line_centralizer_bound (P : Sylow 2 S)
    (A : Subgroup S) (hA : A ≤ (P : Subgroup S)) (hcard : Nat.card A = 2) :
    (centralizer (A : Set S)).relIndex (P : Subgroup S) ≤ 2 := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq S P sylow
  let f := (MulAut.conj g).toMonoidHom
  have hP : (P : Subgroup S).map f = sylowCarrier := congrArg (fun P : Sylow 2 S => (P : Subgroup S)) hg
  have hAc : Nat.card (A.map f) = 2 := by
    rw [card_map_of_injective (MulAut.conj g).injective,hcard]
  have hAS : A.map f ≤ sylowCarrier := (map_mono hA).trans_eq hP
  obtain ⟨hder,hcen,hz⟩ := sylow_commutator_line
  have hi := line_centralizer_index_le_two sylowCarrier (zpowers z) (A.map f)
    hz hAc hAS ((commutator_mono le_rfl hAS).trans hder) hcen
  have hC : (centralizer (A.map f : Set S)).comap f = centralizer (A : Set S) := by
    ext x
    constructor
    · intro hx a ha
      apply (show Function.Injective f from (MulAut.conj g).injective)
      simpa only [map_mul] using hx (f a) (mem_map_of_mem f ha)
    · intro hx a ha
      obtain ⟨a,ha,rfl⟩ := ha
      simpa only [map_mul] using congrArg f (hx a ha)
  rw [inf_relIndex_left,←hP,←relIndex_comap,hC] at hi
  exact hi

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}
local notation "M" => (L ⊔ R : Subgroup G)
local notation "T" => R.subgroupOf (L ⊔ R)

include e hz hn in
theorem four_lt_radical_normalizer_knownSimple
    (hb : 4 < replacementDistance h d) :
    normalizer (d.radical : Set d.overgroup) = (T).subgroupOf d.overgroup ∧
      (∃ W : Sylow 2 d.overgroup, (W : Subgroup d.overgroup) =
        normalizer (d.radical : Set d.overgroup)) ∧
      (d.radical.relIndex (normalizer (d.radical : Set d.overgroup)) = 1 ∨
        d.radical.relIndex (normalizer (d.radical : Set d.overgroup)) = 2) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  obtain ⟨⟨P,hP⟩,hne,hcases⟩ := SylowTerminal.four_lt_original_sylow_non_elementary_image_knownSimple
    (e := e) (hz := hz) (hn := hn) hb
  have hne' : ¬ IsElementaryAbelian 2 (d.radical.map s.projection) := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have hnp := NonsylowImage.nonelementary_normalizer_isPGroup
    (d.radical.map s.projection) ((replacement_radical_isPGroup h d).map s.projection) hne'
  have hp : IsPGroup 2 (normalizer (d.radical : Set d.overgroup)) := by
    have hp := hnp.comap_of_ker_isPGroup s.projection (by
      rw [s.projection_kernel]; exact pCore_isPGroup)
    rwa [comap_normalizer_eq_of_surjective _ s.surjective,comap_map_eq,
      s.projection_kernel,sup_eq_left.mpr (replacement_core_le_radical h d)] at hp
  obtain ⟨W,hW⟩ := SylowRestriction.restricted_sylow s P hP
  have hle := SylowRestriction.restricted_normalizes_radical (d := d)
  have he : normalizer (d.radical : Set d.overgroup) = (T).subgroupOf d.overgroup := by
    exact (W.is_maximal' hp (hW.symm ▸ hle)).trans hW
  refine ⟨he,⟨W,hW.trans he.symm⟩,?_⟩
  rw [he]
  exact hcases.elim (fun hc => Or.inl hc.1) (fun hc => Or.inr hc.1)

include e hz hn in
/-- The literal relative edge normalizer, inside the starting stabilizer,
is the embedded restricted original Sylow subgroup. -/
theorem four_lt_base_edge_normalizer_knownSimple
    (hb : 4 < replacementDistance h d) :
    normalizer (Q d.radical (beta d.radical) : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical (alpha d.radical) =
      ((T).subgroupOf d.overgroup).map (embedM d.radical) := by
  rw [Q_beta,←SylowNormalizer.normalizer_embed,
    (four_lt_radical_normalizer_knownSimple (e := e) (hz := hz) (hn := hn) hb).1]

include e hz hn in
theorem small_base_kernel_relative_index_knownSimple
    (hb : 4 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hfirst : p.walk.getVert 1 = beta d.radical) :
    (normalizer ((Z d.radical (alpha d.radical) ⊓ Q d.radical a' :
      Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))).relIndex
      (normalizer (Q d.radical (beta d.radical) : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical (alpha d.radical)) ≤ 2 := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let f := embedM d.radical
  let A := (Z d.radical a').comap f
  let Z₀ := (Z d.radical (alpha d.radical)).comap f
  let N := normalizer (d.radical : Set d.overgroup)
  have hAG : Z d.radical a' ≤ stabilizer d.radical (alpha d.radical) :=
    critical_Z_le_stabilizer d.radical (replacementGeometry h d) _ rfl
      (replacementDistance_pos h d) p.critical
  have hAm : A.map f = Z d.radical a' :=
    map_comap_eq_self (hAG.trans_eq (stabilizer_m_base d.radical))
  have hZm : Z₀.map f = Z d.radical (alpha d.radical) :=
    map_comap_eq_self ((Z_le_stabilizer d.radical _).trans_eq (stabilizer_m_base d.radical))
  have hAr : A ≤ d.radical := by
    have hAt : Z d.radical a' ≤ Q d.radical (p.walk.getVert 1) := by
      apply Z_le_Q_of_dist_lt d.radical a' ((replacementGeometry h d).exists_critical a' p.end_color)
      rw [(replacementGeometry h d).distance_constant a' p.end_color,SimpleGraph.dist_comm,p.dist_end]
      have hl : p.walk.length=replacementDistance h d := p.length_eq_b
      change p.walk.length-1 < replacementDistance h d
      omega
    rw [hfirst,Q_beta] at hAt
    have hh := comap_mono (f := f) hAt
    rwa [comap_map_eq_self_of_injective (embedM_injective d.radical)] at hh
  obtain ⟨_,⟨W,hW⟩,_⟩ := four_lt_radical_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) hb
  let W' := W.mapSurjective s.surjective
  have hW' : (W' : Subgroup S) = N.map s.projection := congrArg (Subgroup.map s.projection) hW
  have hAcard : Nat.card (A.map s.projection)=2 := by
    change Nat.card (graphImage s (Z d.radical a'))=2
    rw [graphImage_card s _ hAG]
    exact (small_critical_indices s hc p hsmall).2
  have hi := sylow_line_centralizer_bound W' (A.map s.projection)
    ((map_mono (hAr.trans d.radical.le_normalizer)).trans_eq hW'.symm) hAcard
  rw [hW',←relIndex_comap] at hi
  let C := (centralizer (A.map s.projection : Set S)).comap s.projection
  have hCZ : C ≤ normalizer (Z₀ : Set d.overgroup) := by
    intro x hx
    have he : f x ∈ normalizer (Z d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) :=
      Z_normalized d.radical _ ((stabilizer_m_base d.radical).symm ▸ ⟨x,rfl⟩)
    exact le_normalizer_comap f he
  have hAZ : A ≤ normalizer (Z₀ : Set d.overgroup) := by
    intro x hx
    have he := Z_normalized d.radical (alpha d.radical) (hAG hx)
    exact le_normalizer_comap f he
  have hcomm : ⁅C,A⁆ ≤ s.projection.ker := by
    rw [←Subgroup.map_eq_bot_iff,map_commutator]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact map_comap_le _ _
  have hkerZ : s.projection.ker ≤ centralizer (Z₀ : Set d.overgroup) := by
    intro x hx v hv
    apply embedM_injective d.radical
    rw [map_mul,map_mul]
    have hxQ : f x ∈ Q d.radical (alpha d.radical) := by
      rw [Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)]
      exact mem_map_of_mem f (s.projection_kernel ▸ hx)
    exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical (alpha d.radical) rfl)) hxQ) (f v) hv
  have hCn : C ≤ normalizer ((⁅Z₀,A⁆ : Subgroup d.overgroup) : Set d.overgroup) := by
    rw [commutator_comm Z₀]
    exact SylowNormalizer.fixed_mod_central_normalizes A Z₀ C hAZ hCZ (hcomm.trans hkerZ)
  have hcard : Nat.card (⁅Z₀,A⁆ : Subgroup d.overgroup)=2 := by
    rw [←card_map_of_injective (f := f) (embedM_injective d.radical),map_commutator,hZm,hAm]
    exact small_critical_commutator_card s hc p hsmall
  have hCc := hCn.trans (normalizer_le_centralizer_of_card_two _ hcard)
  have hDm : C.map f ≤ centralizer
      ((⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) :
        Set (FreeAmalgam d.radical)) := by
    rw [←hZm,←hAm,←map_commutator]
    exact (map_mono hCc).trans (map_centralizer_le_centralizer_image _ f)
  have hCG : C.map f ≤ stabilizer d.radical (alpha d.radical) :=
    (map_le_range f C).trans_eq (stabilizer_m_base d.radical).symm
  have hCK : C.map f ≤ normalizer
      ((Z d.radical (alpha d.radical) ⊓ Q d.radical a' : Subgroup (FreeAmalgam d.radical)) :
        Set (FreeAmalgam d.radical)) := by
    have hh := le_inf hCG hDm
    rw [←small_critical_kernel_normalizer_eq_line_centralizer s hc p hsmall] at hh
    exact hh.trans inf_le_right
  rw [Q_beta,←SylowNormalizer.normalizer_embed]
  let : Finite (N.map f) := Finite.of_injective
    (N.equivMapOfInjective f (embedM_injective d.radical)).symm
    (N.equivMapOfInjective f (embedM_injective d.radical)).symm.injective
  exact (relIndex_le_of_le_left hCK index_ne_zero_of_finite).trans
    ((relIndex_map_map_of_injective C N (embedM_injective d.radical)).le.trans hi)

include e hz hn in
/-- At any original component vertex, a small critical seed kernel has at
most two conjugates under the actual first-edge relative normalizer. -/
theorem small_kernel_relative_index_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4) :
    (normalizer ((Z d.radical a ⊓ Q d.radical a' :
      Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))).relIndex
      (normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical a) ≤ 2 := by
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  obtain ⟨g, hg | hg⟩ :=
    (adjacent_iff_exists_common d.radical a (p.walk.getVert 1)).mp hat
  · have hbase : act d.radical g⁻¹ a = alpha d.radical := by
      rw [hg.1, act_mVertex, mul_inv_cancel]
      rfl
    have hfirst : act d.radical g⁻¹ (p.walk.getVert 1) = beta d.radical := by
      rw [hg.2, act_hVertex, mul_inv_cancel]
      rfl
    have hrestore (v : Vertex d.radical) :
        act d.radical g (act d.radical g⁻¹ v) = v := by
      rw [← act_mul, inv_mul_cancel, act_one]
    have hq : ∃ q : CriticalPath d.radical (replacementGeometry h d)
        (act d.radical g⁻¹ a) (act d.radical g⁻¹ a'),
        ∀ i, q.walk.getVert i = act d.radical g⁻¹ (p.walk.getVert i) :=
      ⟨p.act g⁻¹, fun i => by simp only [CriticalPath.act, actWalk_getVert]⟩
    rw [hbase] at hq
    obtain ⟨q, hq⟩ := hq
    have hqfirst : q.walk.getVert 1 = beta d.radical := (hq 1).trans hfirst
    have hs : (Q d.radical (act d.radical g⁻¹ a')).relIndex
        (Z d.radical (act d.radical g⁻¹ a)) < 4 := by
      rw [Q_act, Z_act, inv_inv,
        relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
      exact hsmall
    rw [hbase] at hs
    have hi := small_base_kernel_relative_index_knownSimple
      (e := e) (hz := hz) (hn := hn) hb q hs hqfirst
    have he := relIndex_map_map_of_injective
      (f := (MulAut.conj g⁻¹).toMonoidHom)
      (normalizer ((Z d.radical (alpha d.radical) ⊓
        Q d.radical (act d.radical g⁻¹ a') :
          Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)))
      (normalizer (Q d.radical (beta d.radical) : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical (alpha d.radical)) (MulAut.conj g⁻¹).injective
    rw [map_normalizer_eq_of_bijective _ (MulAut.conj g⁻¹).bijective,
      Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective,
      Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective,
      map_normalizer_eq_of_bijective _ (MulAut.conj g⁻¹).bijective,
      ← Z_act, ← Q_act, ← Q_act, ← stabilizer_act, ← hbase, ← hfirst,
      hrestore, hrestore, hrestore] at he
    exact he.symm ▸ (by simpa only [hbase, hfirst] using hi)
  · have ha := p.start_color
    rw [hg.1] at ha
    cases ha

include e hz hn in
/-- Equivalently, the whole critical line has centralizer index at most two
in the same literal relative normalizer. -/
theorem small_line_relative_centralizer_index_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4) :
    (centralizer ((⁅Z d.radical a, Z d.radical a'⁆ :
      Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))).relIndex
      (normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical a) ≤ 2 := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hi := small_kernel_relative_index_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall
  let N := normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
    stabilizer d.radical a
  have he := small_critical_kernel_normalizer_eq_line_centralizer s hc p hsmall
  have hn : N ≤ stabilizer d.radical a := inf_le_right
  have he' := congrArg (fun H : Subgroup (FreeAmalgam d.radical) => N ⊓ H) he
  rw [← inf_assoc, inf_eq_left.mpr hn, ← inf_assoc, inf_eq_left.mpr hn] at he'
  have hi' := congrArg (fun H : Subgroup (FreeAmalgam d.radical) => H.relIndex N) he'
  rw [inf_relIndex_left, inf_relIndex_left] at hi'
  exact hi' ▸ hi

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowSmallNormalizer
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
