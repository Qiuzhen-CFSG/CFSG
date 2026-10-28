module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.EqualKernel
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.SixteenUnequal
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.SixteenUnequal
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowCompatible
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowPairedFixer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTrappedExclusion
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.NonnormalSelection

/-!
# Initial selection for every order-sixteen radical image

Equal neighboring small movers admit a common generating edge and a pair
of endpoints transported by one residual element. A trapped pair gives
X = Z. Its omega-center calculation puts the derived subgroup of the
three joined seeds in the starting seed. `EqualKernel` then bounds their
full critical-kernel commutator using the elementary action image, without
assuming that the whole radius or seed join is abelian.

The two nonzero kernel lines coincide and are fixed by the whole starting
stabilizer. Transport by the same residual element bounds joint movement
on both full kernels by two, contradicting the strict slice. Consequently
one orientation gives an overlapping backward critical path already above
distance two. Together with the unequal-mover argument this gives such a
path for every strict neighbor at distance four.

For initial selection, absence of a nonabelian large-slice path makes both
midpoint endpoint slices strict. Transport produces a strict neighbor on
the first edge; its backward path makes the whole radius escape. The
reciprocal path now makes the original forward slice strict, and another
backward path has both endpoints in its selected orbit span. That span is
nonabelian, as required. The literal original-replacement consumer leaves
only non-elementary image eight, with original Sylow and restriction index
two retained. Both moving covers, full seeds and central attachments remain.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.6)--(5.8), printed pp.918--920, and the initial selection in
(5.12), printed p.924. The image-eight selection and independently owned
selected terminal theorem are still needed for DistanceFourInput.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.SixteenEqual
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}
local notation "S" => Equiv.Perm (Fin 6)

open SylowCompatible
open SixteenUnequal

include e hz hn in
/-- Simultaneous small-mover generation and common fixed space on the actual
order-sixteen replacement. Both full edge generation equations use the same
edge and endpoint transporter as the small-mover equations. -/
private theorem sixteen_paired_small_mover_neighbor_knownSimple
    (hb : 2 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      ∃ x ∈ Ltilde d.radical (alpha d.radical),
        x^3 ∈ Q d.radical (alpha d.radical) ∧
        let J := SmallMover.join (U d.radical (alpha d.radical))
          (Q d.radical (alpha d.radical)) (Q d.radical t) 4
        Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical) ∧
        Q d.radical t ⊔ Z d.radical (act d.radical x a') = stabilizer d.radical (alpha d.radical) ∧
        J ⊔ Z d.radical a' ⊔ Z d.radical (act d.radical x a') = stabilizer d.radical (alpha d.radical) ∧
        J ⊔ J.map (MulAut.conj x).toMonoidHom = stabilizer d.radical (alpha d.radical) ∧
        (Z d.radical (alpha d.radical) ⊓ centralizer (J : Set (FreeAmalgam d.radical))) ⊓
          centralizer (J.map (MulAut.conj x).toMonoidHom : Set (FreeAmalgam d.radical)) =
          Z d.radical (alpha d.radical) ⊓
            centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨a,ha,hswap⟩ := small_critical_image_swap s hc p hsmall
  obtain ⟨u,hN,_,hj,himage,_⟩ := Nonelementary.normalizer_small_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) (sixteen_nonelementary hcard) hb
  have hnormal := SylowLarge.sixteen_radical_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d) hcard
  let J₀ := SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) d.radical 4
  have hJimage : J₀.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom := by
    rw [hnormal] at hj himage
    rw [show J₀ = _ from hj]
    exact himage
  have hRimage : d.radical.map s.projection = sylowCarrier.map (MulAut.conj u).toMonoidHom := by
    rwa [hnormal] at hN
  have hkJ : s.projection.ker ≤ J₀ := by
    rw [s.projection_kernel]
    let := replacementMoved_normal h d
    exact SmallMover.kernel_le_join _ _ _ 4 (by decide) (replacement_core_le_radical h d)
      (by rw [←moved_centralizer s]; exact le_centralizer_iff.mpr le_rfl)
  let A := (Z d.radical a').comap (embedM d.radical)
  obtain ⟨g,y,hy,hy3,htop₀,htop₁,htop,hJpair⟩ := compatible_lifts s.projection s.surjective
    d.radical J₀ (replacementComponent d) A s.component_image
    (s.projection_kernel.symm ▸ replacement_core_le_radical h d) hkJ u hRimage hJimage a ha hswap
  let R₁ := d.radical.map (MulAut.conj g).toMonoidHom
  let J₁ := J₀.map (MulAut.conj g).toMonoidHom
  let A₁ := A.map (MulAut.conj y).toMonoidHom
  have hQ : (pCore 2 d.overgroup).map (MulAut.conj g).toMonoidHom = pCore 2 d.overgroup :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
  have hU : (replacementMoved d).map (MulAut.conj g).toMonoidHom = replacementMoved d := by
    let := replacementMoved_normal h d
    exact mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
  let f := (embedM d.radical g)⁻¹
  let x := (embedM d.radical y)⁻¹
  let t := act d.radical f (beta d.radical)
  let J := SmallMover.join (U d.radical (alpha d.radical))
    (Q d.radical (alpha d.radical)) (Q d.radical t) 4
  have hf : f ∈ stabilizer d.radical (alpha d.radical) := by
    change f ∈ stabilizer d.radical (mVertex d.radical 1)
    rw [stabilizer_m_base]
    exact ⟨g⁻¹,by simp only [map_inv,f]⟩
  have ht : Q d.radical t = R₁.map (embedM d.radical) := by
    rw [Q_act,Q_beta,image_conjugate]
    simp only [f,inv_inv]
  have hJm : J₁.map (embedM d.radical) = J := by
    change ((SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) d.radical 4).map
      (MulAut.conj g).toMonoidHom).map (embedM d.radical) = J
    rw [SmallMover.join_map _ (MulAut.conj g).injective,
      hU,hQ,SmallMover.join_map _ (embedM_injective d.radical),←hc.U_eq_moved,
      ←Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d),←ht]
  have hxL : x ∈ Ltilde d.radical (alpha d.radical) := by
    rw [Ltilde_alpha,replacement_residual h d]
    exact mem_map_of_mem _ ((replacementComponent d).inv_mem hy)
  have hAm : A.map (embedM d.radical) = Z d.radical a' :=
    map_comap_eq_self ((critical_Z_le_stabilizer d.radical (replacementGeometry h d)
      (alpha d.radical) rfl (replacementDistance_pos h d) p.critical).trans_eq
        (stabilizer_m_base d.radical))
  have hA₁m : A₁.map (embedM d.radical) = Z d.radical (act d.radical x a') := by
    rw [image_conjugate,hAm,Z_act]
    simp only [x,inv_inv]
  have hrange : (embedM d.radical).range = stabilizer d.radical (alpha d.radical) :=
    (stabilizer_m_base d.radical).symm
  have hpair' : J ⊔ J.map (MulAut.conj x).toMonoidHom = stabilizer d.radical (alpha d.radical) := by
    have hh := congrArg (Subgroup.map (embedM d.radical)) hJpair
    rwa [Subgroup.map_sup,image_conjugate (embedM d.radical) J₁ y⁻¹,map_inv,hJm,←MonoidHom.range_eq_map,
      hrange] at hh
  refine ⟨t,?_,x,hxL,?_,?_,?_,?_,hpair',?_⟩
  · have hfix : act d.radical f (alpha d.radical)=alpha d.radical := hf
    rw [←hfix]
    exact (adjacent_act_iff d.radical f _ _).mpr (base_adjacent d.radical)
  · rw [s.projection_kernel] at hy3
    rw [Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)]
    have hx3 : x^3=embedM d.radical ((y^3)⁻¹) := by simp only [x,inv_pow,map_inv,map_pow]
    rw [hx3]
    exact mem_map_of_mem _ ((pCore 2 d.overgroup).inv_mem hy3)
  · have hh := congrArg (Subgroup.map (embedM d.radical)) htop₀
    rwa [Subgroup.map_sup,←ht,hAm,←MonoidHom.range_eq_map,hrange] at hh
  · have hh := congrArg (Subgroup.map (embedM d.radical)) htop₁
    rwa [Subgroup.map_sup,←ht,hA₁m,←MonoidHom.range_eq_map,hrange] at hh
  · have hh := congrArg (Subgroup.map (embedM d.radical)) htop
    rwa [Subgroup.map_sup,Subgroup.map_sup,hJm,hAm,hA₁m,←MonoidHom.range_eq_map,
      hrange] at hh
  · ext z
    constructor
    · rintro ⟨⟨hz,hzJ⟩,hzJx⟩
      refine ⟨hz,?_⟩
      have hfix : J ⊔ J.map (MulAut.conj x).toMonoidHom ≤ centralizer ({z} : Set _) :=
        sup_le (fun j hj => mem_centralizer_singleton_iff.mpr (hzJ j hj))
          (fun j hj => mem_centralizer_singleton_iff.mpr (hzJx j hj))
      rw [hpair'] at hfix
      exact fun j hj => mem_centralizer_singleton_iff.mp (hfix hj)
    · rintro ⟨hz,hzG⟩
      exact ⟨⟨hz,fun j hj => hzG j (hpair' ▸ mem_sup_left hj)⟩,
        fun j hj => hzG j (hpair' ▸ mem_sup_right hj)⟩

include e hz hn in
private theorem generating_endpoint_does_not_normalize
    (hb : 2 < replacementDistance h d)
    {z c t : Vertex d.radical}
    (hat : Adjacent d.radical (alpha d.radical) t) (hct : Adjacent d.radical c t)
    (hgen : Q d.radical t ⊔ Z d.radical z = stabilizer d.radical (alpha d.radical))
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c)) :
    ¬ Z d.radical z ≤ normalizer ((Z d.radical c ⊔ Z d.radical (alpha d.radical) :
      Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  exact eligible_generating_seed_not_normalized s hb hat hct hgen
    (fun hh => by have hi := relIndex_eq_one.mpr hh; omega)

include e hz hn in
/-- In the equal-mover source branch, a prescribed strict slice supplies
one compatible pair. Its actual neighboring mover gives both generation
and the common fixed subgroup. Both endpoints fail to normalize the same
selected seed span; the endpoint transporter retains the whole critical walk. -/
private theorem sixteen_equal_mover_strict_pair_knownSimple
    (hb : 2 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a' delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hequal : SmallMover.join (U d.radical delta) (Q d.radical delta)
        (Q d.radical (p.walk.getVert 1)) 4 =
      SmallMover.join (U d.radical (alpha d.radical)) (Q d.radical (alpha d.radical))
        (Q d.radical (p.walk.getVert 1)) 4)
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta)) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      ∃ g ∈ stabilizer d.radical (alpha d.radical),
        act d.radical g (p.walk.getVert 1) = t ∧
        Adjacent d.radical (act d.radical g delta) t ∧
        2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (act d.radical g delta)) ∧
        ∃ x ∈ Ltilde d.radical (alpha d.radical),
          ∃ q : CriticalPath d.radical (replacementGeometry h d)
              (alpha d.radical) (act d.radical x a'),
            (∀ i, q.walk.getVert i = act d.radical x (p.walk.getVert i)) ∧
            (Q d.radical (act d.radical x a')).relIndex (Z d.radical (alpha d.radical)) < 4 ∧
            let c := act d.radical g delta
            let J := SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4
            J = SmallMover.join (U d.radical (alpha d.radical))
              (Q d.radical (alpha d.radical)) (Q d.radical t) 4 ∧
            Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical) ∧
            J ⊔ Z d.radical a' ⊔ Z d.radical (act d.radical x a') = stabilizer d.radical (alpha d.radical) ∧
            J ⊔ J.map (MulAut.conj x).toMonoidHom = stabilizer d.radical (alpha d.radical) ∧
            ¬ Z d.radical a' ≤ normalizer ((Z d.radical c ⊔ Z d.radical (alpha d.radical) :
              Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ∧
            Adjacent d.radical (alpha d.radical) (act d.radical x⁻¹ t) ∧
            Adjacent d.radical (act d.radical x⁻¹ c) (act d.radical x⁻¹ t) ∧
            2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
              (U d.radical (act d.radical x⁻¹ c)) ∧
            Q d.radical (act d.radical x⁻¹ t) ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical) ∧
            ¬ Z d.radical a' ≤ normalizer
              ((Z d.radical (act d.radical x⁻¹ c) ⊔ Z d.radical (alpha d.radical) :
                Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
  obtain ⟨t,hat,x,hxL,_hx3,hgen₀,hgen₁,hgen,hpair,_hfix⟩ :=
    sixteen_paired_small_mover_neighbor_knownSimple (e := e) (hz := hz) (hn := hn) hb hcard p hsmall
  have hl : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
  have hfirst : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
  obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors d.radical (alpha d.radical) hfirst hat
  have hct : Adjacent d.radical (act d.radical g delta) t := by
    rw [←hgt]
    exact (adjacent_act_iff d.radical g delta (p.walk.getVert 1)).mpr hdelta
  have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      (by omega : 2 < replacementDistance h d) (alpha d.radical) rfl ((stabilizer d.radical (alpha d.radical)).inv_mem hg))
  have hstrict' : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (act d.radical g delta)) := by
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact hstrict
  have heq : SmallMover.join (U d.radical (act d.radical g delta))
      (Q d.radical (act d.radical g delta)) (Q d.radical t) 4 =
      SmallMover.join (U d.radical (alpha d.radical)) (Q d.radical (alpha d.radical)) (Q d.radical t) 4 := by
    have hh := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hequal
    have hga : act d.radical g (alpha d.radical) = alpha d.radical := hg
    rwa [SmallMover.join_map _ (MulAut.conj g⁻¹).injective,
      SmallMover.join_map _ (MulAut.conj g⁻¹).injective,←U_act,←Q_act,←Q_act,←U_act,←Q_act,hga,hgt] at hh
  have hx : x ∈ stabilizer d.radical (alpha d.radical) := Ltilde_le_stabilizer _ hxL
  have hxa : act d.radical x (alpha d.radical)=alpha d.radical := hx
  have hq : ∃ q : CriticalPath d.radical (replacementGeometry h d)
      (alpha d.radical) (act d.radical x a'),
      ∀ i, q.walk.getVert i = act d.radical x (p.walk.getVert i) := by
    have hh : ∃ q : CriticalPath d.radical (replacementGeometry h d)
        (act d.radical x (alpha d.radical)) (act d.radical x a'),
        ∀ i, q.walk.getVert i = act d.radical x (p.walk.getVert i) :=
      ⟨p.act x,fun i => by simp only [CriticalPath.act,actWalk_getVert]⟩
    rwa [hxa] at hh
  obtain ⟨q,hq⟩ := hq
  have hqs : (Q d.radical (act d.radical x a')).relIndex (Z d.radical (alpha d.radical)) < 4 := by
    conv_lhs => rhs; rw [←hxa]
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hsmall
  have hxainv : act d.radical x⁻¹ (alpha d.radical) = alpha d.radical :=
    (stabilizer d.radical (alpha d.radical)).inv_mem hx
  have hat₂ : Adjacent d.radical (alpha d.radical) (act d.radical x⁻¹ t) := by
    rw [←hxainv]
    exact (adjacent_act_iff d.radical x⁻¹ _ _).mpr hat
  have hct₂ : Adjacent d.radical (act d.radical x⁻¹ (act d.radical g delta))
      (act d.radical x⁻¹ t) := (adjacent_act_iff d.radical x⁻¹ _ _).mpr hct
  have hBx : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj x).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      (by omega : 2 < replacementDistance h d) (alpha d.radical) rfl hx)
  have hstrict₂ : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (act d.radical x⁻¹ (act d.radical g delta))) := by
    rw [U_act,inv_inv,←hBx,relIndex_map_map_of_injective _ _ (MulAut.conj x).injective]
    exact hstrict'
  have hgen₂ : Q d.radical (act d.radical x⁻¹ t) ⊔ Z d.radical a' =
      stabilizer d.radical (alpha d.radical) := by
    have hh := congrArg (Subgroup.map (MulAut.conj x).toMonoidHom) hgen₁
    have hQt : (Q d.radical t).map (MulAut.conj x).toMonoidHom = Q d.radical (act d.radical x⁻¹ t) := by
      rw [Q_act,inv_inv]
    have hZa : (Z d.radical (act d.radical x a')).map (MulAut.conj x).toMonoidHom = Z d.radical a' := by
      have hh := Z_act d.radical x⁻¹ (act d.radical x a')
      rw [inv_inv,←act_mul,mul_inv_cancel,act_one] at hh
      exact hh.symm
    have hG : (stabilizer d.radical (alpha d.radical)).map (MulAut.conj x).toMonoidHom =
        stabilizer d.radical (alpha d.radical) :=
      mem_normalizer_iff_map_conj_eq.mp ((stabilizer d.radical (alpha d.radical)).le_normalizer hx)
    rwa [Subgroup.map_sup,hQt,hZa,hG] at hh
  refine ⟨t,hat,g,hg,hgt,hct,hstrict',x,hxL,q,hq,hqs,heq,hgen₀,
    ?_,?_,?_,hat₂,hct₂,hstrict₂,hgen₂,?_⟩
  · rwa [heq]
  · rwa [heq]
  · exact generating_endpoint_does_not_normalize (e := e) (hz := hz) (hn := hn)
      hb hat hct hgen₀ hstrict'
  · exact generating_endpoint_does_not_normalize (e := e) (hz := hz) (hn := hn)
      hb hat₂ hct₂ hgen₂ hstrict₂

include e hz hn in
/-- The paired small movers put the common full-kernel fixer in the actual
Baumann slice. The edge core need not act abelianly on the full seed. -/
private theorem sixteen_paired_trapped_fixer_le_slice_knownSimple
    (hb : 2 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a z w c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (q : CriticalPath d.radical (replacementGeometry h d) a w)
    (hps : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (hqs : (Q d.radical w).relIndex (Z d.radical a) < 4)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hequal : SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 =
      SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4)
    (hgen : SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 ⊔
      Z d.radical z ⊔ Z d.radical w = stabilizer d.radical a)
    (hpbad : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hqbad : Z d.radical c ≤ Q d.radical (q.walk.getVert (q.walk.length-2))) :
    Z d.radical c ⊓ centralizer
      ((Z d.radical z ⊓ Q d.radical a ⊔ Z d.radical w ⊓ Q d.radical a :
        Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ≤
      B d.radical a ((replacementGeometry h d).Z_normal _) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let A := Z d.radical z ⊓ Q d.radical a ⊔ Z d.radical w ⊓ Q d.radical a
  let F := Z d.radical c ⊓ centralizer (A : Set (FreeAmalgam d.radical))
  let Y := F ⊔ Z d.radical a
  let J := SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4
  have hcol : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    rw [p.start_color] at h1
    cases hc : color d.radical c <;> cases ht : color d.radical t <;> simp_all
  have hdist : (cosetGraph d.radical).dist c a ≤ 2 := by
    have h1 : (cosetGraph d.radical).dist c t = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hct)
    have h2 : (cosetGraph d.radical).dist t a = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
    simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle
      (u := c) (v := t) (w := a)
  have hZV : Z d.radical c ≤ V d.radical a :=
    (Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hdist)
  have hVG : V d.radical a ≤ stabilizer d.radical a :=
    (replacementGeometry h d).V_local a p.start_color (by
      rw [(replacementGeometry h d).distance_constant a p.start_color]; exact hb2)
  have hQJ : Q d.radical a ≤ J := by
    change Q d.radical a ≤ SmallMover.join _ _ _ _
    rw [hequal]
    exact (SixteenUnequal.sixteen_edge_small_mover_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard p.start_color hat).1
  have hFt : J ≤ normalizer (F : Set (FreeAmalgam d.radical)) :=
    small_mover_preserves_seed_fixer_knownSimple (e := e) (hz := hz) (hn := hn)
      hb hcard hcol hct A ((sup_le inf_le_right inf_le_right).trans hQJ)
  have hmove {v : Vertex d.radical}
      (r : CriticalPath d.radical (replacementGeometry h d) a v)
      (hrs : (Q d.radical v).relIndex (Z d.radical a) < 4)
      (hrbad : Z d.radical c ≤ Q d.radical (r.walk.getVert (r.walk.length-2)))
      (hA : Z d.radical v ⊓ Q d.radical a ≤ A) :
      Z d.radical v ≤ normalizer (Y : Set (FreeAmalgam d.radical)) := by
    have hFmove : ⁅F,Z d.radical v⁆ ≤ Z d.radical a :=
      small_critical_predecessor_commutator s hc hb2 r hrs F (inf_le_left.trans hrbad)
        (inf_le_right.trans (centralizer_le hA))
    have hYmove : ⁅Y,Z d.radical v⁆ ≤ Z d.radical a :=
      commutator_sup_le_of_relative_normal (stabilizer d.radical a)
        F (Z d.radical a) (Z d.radical v) (Z d.radical a)
        (Z_normalized d.radical a) ((inf_le_left.trans hZV).trans hVG)
        (Z_le_stabilizer d.radical a) hFmove
        (((critical_Z_commutator_le_moving (h := h) r).trans inf_le_left).trans
          (DistanceEight.U_le_Z d.radical a))
    exact le_normalizer_iff_commutator_le_left.mpr (hYmove.trans le_sup_right)
  have hJG : J ≤ stabilizer d.radical a := by
    rw [←hgen]
    exact le_sup_left.trans le_sup_left
  have hYN : stabilizer d.radical a ≤ normalizer (Y : Set (FreeAmalgam d.radical)) := by
    rw [←hgen]
    refine sup_le (sup_le ?_ (hmove p hps hpbad le_sup_left)) (hmove q hqs hqbad le_sup_right)
    exact (le_inf hFt (hJG.trans (Z_normalized d.radical a))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hYV : Y ≤ V d.radical a := sup_le (inf_le_left.trans hZV) (Z_le_VBall d.radical a 2)
  have hYprod : Y ≤ Z d.radical c ⊔ Z d.radical a := sup_le_sup inf_le_left le_rfl
  let := finite_stabilizer d.radical a
  let : Finite (Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective
      (inclusion (sup_le (hZV.trans hVG) (Z_le_stabilizer d.radical a))) (inclusion_injective _)
  have hindex : (Z d.radical a).relIndex Y ≤ 8 :=
    (relIndex_le_of_le_right hYprod index_ne_zero_of_finite).trans
      (DistanceFour.adjacent_seed_span_index_le_eight
        (e := e) (hz := hz) (hn := hn) hb p.start_color hat hct)
  exact le_sup_left.trans
    (SylowSpanSelection.normal_small_radius_le_slice_at s hb2 p.start_color Y hYV hYN hindex)

include e hz hn in
/-- A strict slice forces the simultaneous paired kernel commutator to have
order greater than two, with the same two kernels and the same selected seed. -/
private theorem sixteen_paired_trapped_joint_movement_gt_two_knownSimple
    (hb : 2 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a z w c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (q : CriticalPath d.radical (replacementGeometry h d) a w)
    (hps : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (hqs : (Q d.radical w).relIndex (Z d.radical a) < 4)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hequal : SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 =
      SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4)
    (hgen : SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 ⊔
      Z d.radical z ⊔ Z d.radical w = stabilizer d.radical a)
    (hpbad : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hqbad : Z d.radical c ≤ Q d.radical (q.walk.getVert (q.walk.length-2)))
    (hindex : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c)) :
    2 < Nat.card (⁅U d.radical c,Z d.radical z ⊓ Q d.radical a ⊔
      Z d.radical w ⊓ Q d.radical a⁆ : Subgroup (FreeAmalgam d.radical)) := by
  by_contra! hbound
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let A := Z d.radical z ⊓ Q d.radical a ⊔ Z d.radical w ⊓ Q d.radical a
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [p.start_color] at hh
    cases he : color d.radical t <;> simp_all
  have hcol : color d.radical c = false := by
    have hh := adjacent_color_ne d.radical hct
    rw [ht] at hh
    cases he : color d.radical c <;> simp_all
  have hAG : A ≤ stabilizer d.radical c :=
    ((sup_le inf_le_right inf_le_right).trans (Q_le_adjacent_h d.radical ht hat)).trans
      (fun _ hx => hx.2 _ (adjacent_symm d.radical hct))
  have hi := moving_small_commutator_fixed_index s hc hcol A hAG hbound
  have hFB := sixteen_paired_trapped_fixer_le_slice_knownSimple (e := e) (hz := hz) (hn := hn)
    hb hcard p q hps hqs hat hct hequal hgen hpbad hqbad
  let := finite_Z d.radical c
  let : Finite (U d.radical c) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical c)) (inclusion_injective _)
  have hh := relIndex_le_of_le_left
    ((inf_le_inf_right _ (DistanceEight.U_le_Z d.radical c)).trans hFB)
    (index_ne_zero_of_finite (H := (U d.radical c ⊓ centralizer
      (A : Set (FreeAmalgam d.radical))).subgroupOf (U d.radical c)))
  rw [inf_relIndex_left] at hh
  exact (Nat.not_le_of_gt hindex) (hh.trans hi)

include e hz hn in
private theorem small_mover_full_seed_quadratic
    (hb : 2 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    let J := SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4
    ⁅⁅Z d.radical a,J⁆,J⁆ = ⊥ := by
  let J := SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4
  obtain ⟨_,hJT,_,_,_,hquad⟩ := SixteenUnequal.sixteen_edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard ha hat
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    cases he : color d.radical t <;> simp_all
  have hZt : Z d.radical t ≤ centralizer (J : Set (FreeAmalgam d.radical)) := by
    intro x hx j hj
    rw [Z,if_neg (by simp [ht])] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2 j (hJT hj)
  have hZtN : Z d.radical t ≤ normalizer (U d.radical a : Set (FreeAmalgam d.radical)) :=
    ((adjacent_Z_le d.radical ha hat).trans (Z_le_stabilizer d.radical a)).trans (U_normalized a)
  change ⁅⁅Z d.radical a,J⁆,J⁆ = ⊥
  rw [DistanceTwo.CentralLayer.Z_eq_moving_sup_edge_at h e hz d ha hat,
    commutator_sup_fixed _ _ J hZtN hZt]
  exact hquad

include e hz hn in
/-- Once the nonnormalizing trapped pair has supplied X = Z, equal neighboring
small movers put their entire neighbor-seed commutator in their central omega.
That omega is exactly the full starting-seed fixer, with all central elements. -/
private theorem sixteen_equal_mover_omega_control_knownSimple
    (hb : 2 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a c t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hequal : SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 =
      SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4)
    (hX : X d.radical a = Z d.radical a) :
    let J := SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4
    omegaCenter J = Z d.radical a ⊓ centralizer (J : Set (FreeAmalgam d.radical)) ∧
      ⁅Z d.radical c,J⁆ ≤ omegaCenter J := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let J := SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4
  have hcol : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    rw [ha] at h1
    cases hc : color d.radical c <;> cases ht : color d.radical t <;> simp_all
  obtain ⟨hQJ,hJT,_,_,_,_⟩ := SixteenUnequal.sixteen_edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard ha hat
  have hQcJ : Q d.radical c ≤ J := by
    change Q d.radical c ≤ SmallMover.join _ _ _ _
    rw [←hequal]
    exact (SixteenUnequal.sixteen_edge_small_mover_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard hcol hct).1
  have hJG : J ≤ stabilizer d.radical a :=
    hJT.trans (fun _ hx => hx.2 _ (adjacent_symm d.radical hat))
  have hJGc : J ≤ stabilizer d.radical c :=
    hJT.trans (fun _ hx => hx.2 _ (adjacent_symm d.radical hct))
  have hZQ : Z d.radical a ≤ Q d.radical a := hX.ge.trans (omegaCenter_le _)
  have hZcX : Z d.radical c ≤ X d.radical c := by
    apply (replacementGeometry h d).omega_bound c hcol
    rw [(replacementGeometry h d).distance_constant c hcol]
    exact replacementDistance_pos h d
  have hOmegaZ : omegaCenter J ≤ Z d.radical a := by
    rw [←hX]
    intro x hx
    obtain ⟨hxJ,hx2,hxc⟩ := mem_omegaCenter_iff.mp hx
    have hxQ : x ∈ Q d.radical a := by
      rw [←C_eq_Q s hc a ha]
      exact ⟨hJG hxJ,fun y hy => hxc y (hQJ (hZQ hy))⟩
    exact mem_omegaCenter_iff.mpr ⟨hxQ,hx2,fun y hy => hxc y (hQJ hy)⟩
  have hquad : ⁅⁅Z d.radical c,J⁆,J⁆ = ⊥ := by
    have hh := small_mover_full_seed_quadratic (e := e) (hz := hz) (hn := hn) hb hcard hcol hct
    dsimp only at hh
    rwa [hequal] at hh
  have hcommZ : ⁅Z d.radical c,J⁆ ≤ Z d.radical c :=
    le_normalizer_iff_commutator_le_left.mp (hJGc.trans (Z_normalized d.radical c))
  have hcommJ : ⁅Z d.radical c,J⁆ ≤ J :=
    (hcommZ.trans hZcX).trans ((omegaCenter_le _).trans hQcJ)
  have hcommC : ⁅Z d.radical c,J⁆ ≤ centralizer (J : Set (FreeAmalgam d.radical)) :=
    commutator_eq_bot_iff_le_centralizer.mp hquad
  refine ⟨le_antisymm (le_inf hOmegaZ ?_) ?_,?_⟩
  · intro x hx
    exact (mem_omegaCenter_iff.mp hx).2.2
  · intro x hx
    exact mem_omegaCenter_iff.mpr ⟨hQJ (hZQ hx.1),
      (mem_omegaCenter_iff.mp (hX.ge hx.1)).2.1,hx.2⟩
  · intro x hx
    exact mem_omegaCenter_iff.mpr ⟨hcommJ hx,
      (mem_omegaCenter_iff.mp (hZcX (hcommZ hx))).2.1,hcommC hx⟩

include e hz hn in
private theorem equal_mover_pair_control
    (hb : 2 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a c t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hequal : SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 =
      SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4)
    (hX : X d.radical a = Z d.radical a)
    (x : FreeAmalgam d.radical) (hx : x ∈ stabilizer d.radical a)
    (hpair : SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 ⊔
      (SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4).map
        (MulAut.conj x).toMonoidHom = stabilizer d.radical a)
    (A : Subgroup (FreeAmalgam d.radical)) (hA : A ≤ Q d.radical a) :
    ⁅Z d.radical c,A⁆ ≤ Z d.radical a ∧
      ⁅Z d.radical c,A⁆ ⊓ ⁅Z d.radical (act d.radical x⁻¹ c),A⁆ ≤
        Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
  let J := SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4
  have hQJ := (SixteenUnequal.sixteen_edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard ha hat).1
  obtain ⟨hOmega,hcomm⟩ := sixteen_equal_mover_omega_control_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard ha hat hct hequal hX
  have hcore : ⁅Z d.radical c,Q d.radical a⁆ ≤
      Z d.radical a ⊓ centralizer (J : Set (FreeAmalgam d.radical)) :=
    (commutator_mono le_rfl hQJ).trans (hcomm.trans_eq hOmega)
  have hQa : (Q d.radical a).map (MulAut.conj x).toMonoidHom = Q d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical a hx)
  have hZa : (Z d.radical a).map (MulAut.conj x).toMonoidHom = Z d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical a hx)
  have hcore₂ : ⁅Z d.radical (act d.radical x⁻¹ c),Q d.radical a⁆ ≤
      Z d.radical a ⊓ centralizer
        (J.map (MulAut.conj x).toMonoidHom : Set (FreeAmalgam d.radical)) := by
    have hh := map_mono (f := (MulAut.conj x).toMonoidHom) hcore
    rw [map_commutator,←map_inf_centralizer_of_injective _ (MulAut.conj x).injective,hQa,hZa] at hh
    simpa only [Z_act,inv_inv] using hh
  have h₁ := (commutator_mono le_rfl hA).trans hcore
  have h₂ := (commutator_mono le_rfl hA).trans hcore₂
  refine ⟨h₁.trans inf_le_left,le_inf (inf_le_left.trans (h₁.trans inf_le_left)) ?_⟩
  apply le_centralizer_iff.mpr
  rw [hequal] at hpair
  rw [←hpair]
  exact sup_le (le_centralizer_iff.mp (inf_le_left.trans (h₁.trans inf_le_right)))
    (le_centralizer_iff.mp (inf_le_right.trans (h₂.trans inf_le_right)))


variable (s : FullSymmetricAction h e hz hn d)
include s in
private theorem combined_actor_kernel_card_le_two (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) {a z c : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (P C D : Subgroup (FreeAmalgam d.radical))
    (hPdef : P = Z d.radical a ⊔ C ⊔ D)
    (helC : IsElementaryAbelian 2 C) (helD : IsElementaryAbelian 2 D)
    (hder : ⁅P,P⁆ ≤ Z d.radical a)
    (_hAP : Z d.radical a ≤ P) (hCP : Z d.radical c ≤ P)
    (hCV : Z d.radical c ≤ V d.radical a)
    (hPt : P ≤ Q d.radical (p.walk.getVert (p.walk.length-1)))
    (hK : ⁅P,Z d.radical z ⊓ Q d.radical a⁆ ≤ Z d.radical a)
    (hnorm : ¬ Z d.radical z ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) :
        Set (FreeAmalgam d.radical))) :
    Nat.card (⁅P,Z d.radical z ⊓ Q d.radical a⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2 := by
  have hlast := critical_last_edge_inputs (h := h) hb p
  have hfixed := critical_full_kernel_eq s hc p
  let := finite_Z d.radical z
  let : Finite (U d.radical z) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical z)) (inclusion_injective _)
  have hindex : (centralizer (Z d.radical a : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical z) ≤ 2 := by
    have hQC : Q d.radical a ≤ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a p.start_color))
    exact ((relIndex_le_of_le_left hQC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical z) index_ne_zero_of_finite)).trans_eq
        (small_critical_indices s hc p hsmall).2
  have hcrit : ⁅Z d.radical a,Z d.radical z⁆ ≤ Z d.radical a :=
    ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans
      (DistanceEight.U_le_Z d.radical a)
  have hfail : ¬ ⁅Z d.radical z,P⁆ ≤
      ⁅Z d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)),P⁆ ⊔
        ⁅Z d.radical z,Z d.radical a⁆ := by
    intro hh
    rw [←hfixed,commutator_comm (Z d.radical z ⊓ Q d.radical a) P,
      commutator_comm (Z d.radical z) (Z d.radical a)] at hh
    have hmove : ⁅Z d.radical c,Z d.radical z⁆ ≤ Z d.radical a := by
      rw [commutator_comm]
      exact (commutator_mono le_rfl hCP).trans (hh.trans (sup_le hK hcrit))
    have htotal := commutator_sup_le_of_relative_normal (stabilizer d.radical a)
      (Z d.radical c) (Z d.radical a) (Z d.radical z) (Z d.radical a)
      (Z_normalized d.radical a)
      (hCV.trans ((replacementGeometry h d).V_local a p.start_color (by
        rw [(replacementGeometry h d).distance_constant a p.start_color]; exact hb)))
      (Z_le_stabilizer d.radical a) hmove hcrit
    exact hnorm (le_normalizer_iff_commutator_le_left.mpr (htotal.trans le_sup_right))
  have hh := (EqualKernel.edge_join_kernel_small_aligned s hc p.end_color hlast.1
    (Z d.radical a) P hlast.2.2 hPt C D hPdef
    ((replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a p.start_color)
    helC helD hder p.critical.2 hindex hfail).1
  rwa [←hfixed,commutator_comm] at hh

include e hz hn in
private theorem paired_traps_common_line
    (hb : 2 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a z c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hequal : SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 =
      SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4)
    (x : FreeAmalgam d.radical) (hx : x ∈ stabilizer d.radical a)
    (q : CriticalPath d.radical (replacementGeometry h d) a (act d.radical x z))
    (hq : ∀ i, q.walk.getVert i = act d.radical x (p.walk.getVert i))
    (_hqs : (Q d.radical (act d.radical x z)).relIndex (Z d.radical a) < 4)
    (_hgen : SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 ⊔
      Z d.radical z ⊔ Z d.radical (act d.radical x z) = stabilizer d.radical a)
    (hpair : SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 ⊔
      (SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4).map
        (MulAut.conj x).toMonoidHom = stabilizer d.radical a)
    (hpbad : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hqbad : Z d.radical c ≤ Q d.radical (q.walk.getVert (q.walk.length-2)))
    (hnorm : ¬ Z d.radical z ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) :
        Set (FreeAmalgam d.radical)))
    (hnorm₂ : ¬ Z d.radical z ≤ normalizer
      ((Z d.radical (act d.radical x⁻¹ c) ⊔ Z d.radical a :
        Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)))
 :
    ∃ K : Subgroup (FreeAmalgam d.radical),
      K ≤ Z d.radical a ∧ Nat.card K ≤ 2 ∧
      ⁅Z d.radical c,Z d.radical z ⊓ Q d.radical a⁆ = K ∧
      ⁅Z d.radical (act d.radical x⁻¹ c),Z d.radical z ⊓ Q d.radical a⁆ = K ∧
      K ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let F := Z d.radical z ⊓ Q d.radical a
  let F₂ := Z d.radical (act d.radical x z) ⊓ Q d.radical a
  let C₂ := Z d.radical (act d.radical x⁻¹ c)
  let P := Z d.radical a ⊔ Z d.radical c ⊔ C₂
  let K := ⁅P,F⁆
  have hQa : (Q d.radical a).map (MulAut.conj x).toMonoidHom = Q d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical a hx)
  have hZa : (Z d.radical a).map (MulAut.conj x).toMonoidHom = Z d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical a hx)
  have hC₂ : C₂ = (Z d.radical c).map (MulAut.conj x).toMonoidHom := by
    simp only [C₂,Z_act,inv_inv]
  have hCV := neighbor_seed_le_radius hat hct
  have hC₂V : C₂ ≤ V d.radical a := by
    have hh := map_mono (f := (MulAut.conj x).toMonoidHom) hCV
    have he : (V d.radical a).map (MulAut.conj x).toMonoidHom = V d.radical a :=
      mem_normalizer_iff_map_conj_eq.mp (DistanceEight.V_normalized d.radical a hx)
    rwa [←hC₂,he] at hh
  have hAV : Z d.radical a ≤ V d.radical a := Z_le_VBall d.radical a 2
  have hVG := (replacementGeometry h d).V_local a p.start_color (by
    rw [(replacementGeometry h d).distance_constant a p.start_color]; exact hb2)
  have hlast := critical_last_edge_inputs (h := h) hb2 p
  have hC₂pre : C₂ ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) := by
    have hh := map_mono (f := (MulAut.conj x).toMonoidHom) hqbad
    have hlen : q.walk.length = p.walk.length := q.length_eq_b.trans p.length_eq_b.symm
    rw [hlen,hq] at hh
    have he := Q_act d.radical x⁻¹ (act d.radical x (p.walk.getVert (p.walk.length-2)))
    simp only [inv_inv,←act_mul,mul_inv_cancel,act_one] at he
    rwa [←hC₂,←he] at hh
  have hPt : P ≤ Q d.radical (p.walk.getVert (p.walk.length-1)) :=
    sup_le (sup_le hlast.2.2 (hpbad.trans hlast.2.1)) (hC₂pre.trans hlast.2.1)
  have hpreG : Q d.radical (p.walk.getVert (p.walk.length-2)) ≤ stabilizer d.radical z :=
    hlast.2.1.trans (fun _ hv => hv.2 _ (adjacent_symm d.radical hlast.1))
  have hXz := (SylowPairedFixer.trapped_nonnormalized_full_kernel_knownSimple
    (e := e) (hz := hz) (hn := hn) hb2 p hsmall hat hct hpbad hnorm).1
  have hXa := SylowPairedFixer.central_generation_eq_seed (h := h) p.start_color hat
    (X_central_generation_all p.end_color hXz a p.start_color)
  have hcontrol := equal_mover_pair_control
    (e := e) (hz := hz) (hn := hn) hb hcard p.start_color hat hct hequal hXa x hx hpair
    (Q d.radical a) le_rfl
  have hC₂Q : ⁅C₂,Q d.radical a⁆ ≤ Z d.radical a := by
    have hh := map_mono (f := (MulAut.conj x).toMonoidHom) hcontrol.1
    rwa [map_commutator,←hC₂,hQa,hZa] at hh
  have hK : K ≤ Z d.radical a := by
    apply commutator_sup_le_of_relative_normal (stabilizer d.radical a)
      (Z d.radical a ⊔ Z d.radical c) C₂ F (Z d.radical a)
      (Z_normalized d.radical a) ((sup_le hAV hCV).trans hVG) (hC₂V.trans hVG)
    · apply commutator_sup_le_of_relative_normal (stabilizer d.radical a)
        (Z d.radical a) (Z d.radical c) F (Z d.radical a)
        (Z_normalized d.radical a) (Z_le_stabilizer d.radical a) (hCV.trans hVG)
      · exact (commutator_mono le_rfl inf_le_right).trans_eq
          (Z_centralizes_Q d.radical a p.start_color) |>.trans bot_le
      · exact (commutator_mono le_rfl inf_le_right).trans hcontrol.1
    · exact (commutator_mono le_rfl inf_le_right).trans hC₂Q
  have hcol : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    rw [p.start_color] at h1
    cases hc : color d.radical c <;> cases ht : color d.radical t <;> simp_all
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a p.start_color
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) c hcol
  let : IsElementaryAbelian 2 C₂ := hC₂ ▸ IsElementaryAbelian.map (MulAut.conj x).toMonoidHom
  have hPQ : P ≤ Q d.radical a :=
    (sup_le (sup_le hAV hCV) hC₂V).trans (V_le_Q d.radical p.start_color hb2)
  have hder : ⁅P,P⁆ ≤ Z d.radical a := by
    apply commutator_sup_le_of_relative_normal (stabilizer d.radical a)
      (Z d.radical a ⊔ Z d.radical c) C₂ P (Z d.radical a)
      (Z_normalized d.radical a) ((sup_le hAV hCV).trans hVG) (hC₂V.trans hVG)
    · apply commutator_sup_le_of_relative_normal (stabilizer d.radical a)
        (Z d.radical a) (Z d.radical c) P (Z d.radical a)
        (Z_normalized d.radical a) (Z_le_stabilizer d.radical a) (hCV.trans hVG)
      · exact (commutator_mono le_rfl hPQ).trans_eq
          (Z_centralizes_Q d.radical a p.start_color) |>.trans bot_le
      · exact (commutator_mono le_rfl hPQ).trans hcontrol.1
    · exact (commutator_mono le_rfl hPQ).trans hC₂Q
  have hbound : Nat.card K ≤ 2 := combined_actor_kernel_card_le_two s hc hb2 p hsmall
    P (Z d.radical c) C₂ rfl inferInstance inferInstance hder
    (le_sup_left.trans le_sup_left) (le_sup_right.trans le_sup_left) hCV hPt hK hnorm
  have hne₁ := nonnormalizing_seed_kernel_ne_bot s hc hb2 p hsmall hCV
    (hpbad.trans hpreG) hnorm
  have hne₂ := nonnormalizing_seed_kernel_ne_bot s hc hb2 p hsmall hC₂V
    (hC₂pre.trans hpreG) hnorm₂
  have h₁ : ⁅Z d.radical c,F⁆ ≤ K := commutator_mono (le_sup_right.trans le_sup_left) le_rfl
  have h₂ : ⁅C₂,F⁆ ≤ K := commutator_mono le_sup_right le_rfl
  let := finite_Z d.radical a
  let : Finite K := Finite.of_injective (inclusion hK) (inclusion_injective _)
  let : Finite (⁅Z d.radical c,F⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion h₁) (inclusion_injective _)
  let : Finite (⁅C₂,F⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion h₂) (inclusion_injective _)
  have hpos₁ : 1 < Nat.card (⁅Z d.radical c,F⁆ : Subgroup (FreeAmalgam d.radical)) :=
    (one_lt_card_iff_ne_bot _).mpr hne₁
  have hpos₂ : 1 < Nat.card (⁅C₂,F⁆ : Subgroup (FreeAmalgam d.radical)) :=
    (one_lt_card_iff_ne_bot _).mpr hne₂
  have heq₁ : ⁅Z d.radical c,F⁆ = K := eq_of_le_of_card_ge h₁ (by omega)
  have heq₂ : ⁅C₂,F⁆ = K := eq_of_le_of_card_ge h₂ (by omega)
  have hcentral : K ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    have hh := (equal_mover_pair_control
      (e := e) (hz := hz) (hn := hn) hb hcard p.start_color hat hct hequal hXa x hx hpair F inf_le_right).2
    change ⁅Z d.radical c,F⁆ ⊓ ⁅C₂,F⁆ ≤ _ at hh
    rw [heq₁,heq₂,inf_idem] at hh
    exact hh.trans inf_le_right
  exact ⟨K,hK,hbound,heq₁,heq₂,hcentral⟩

include e hz hn in
theorem sixteen_equal_paired_traps_impossible_knownSimple
    (hb : 2 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a z c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hequal : SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 =
      SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4)
    (x : FreeAmalgam d.radical) (hx : x ∈ stabilizer d.radical a)
    (q : CriticalPath d.radical (replacementGeometry h d) a (act d.radical x z))
    (hq : ∀ i, q.walk.getVert i = act d.radical x (p.walk.getVert i))
    (hqs : (Q d.radical (act d.radical x z)).relIndex (Z d.radical a) < 4)
    (hgen : SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 ⊔
      Z d.radical z ⊔ Z d.radical (act d.radical x z) = stabilizer d.radical a)
    (hpair : SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 ⊔
      (SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4).map
        (MulAut.conj x).toMonoidHom = stabilizer d.radical a)
    (hpbad : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hqbad : Z d.radical c ≤ Q d.radical (q.walk.getVert (q.walk.length-2)))
    (hnorm : ¬ Z d.radical z ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) :
        Set (FreeAmalgam d.radical)))
    (hnorm₂ : ¬ Z d.radical z ≤ normalizer
      ((Z d.radical (act d.radical x⁻¹ c) ⊔ Z d.radical a :
        Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)))
    (hindex : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c)) : False := by
  let F := Z d.radical z ⊓ Q d.radical a
  let F₂ := Z d.radical (act d.radical x z) ⊓ Q d.radical a
  let C₂ := Z d.radical (act d.radical x⁻¹ c)
  obtain ⟨K,hK,hbound,heq₁,heq₂,hcentral⟩ := paired_traps_common_line
    (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hat hct hequal x hx q hq hqs
      hgen hpair hpbad hqbad hnorm hnorm₂
  let := finite_Z d.radical a
  let : Finite K := Finite.of_injective (inclusion hK) (inclusion_injective _)
  have hMK : stabilizer d.radical a ≤ normalizer (K : Set (FreeAmalgam d.radical)) :=
    (le_centralizer_iff.mp hcentral).trans (Subgroup.centralizer_le_normalizer _)
  have hmapK : K.map (MulAut.conj x⁻¹).toMonoidHom = K :=
    mem_normalizer_iff_map_conj_eq.mp (hMK ((stabilizer d.radical a).inv_mem hx))
  have hmapC : C₂.map (MulAut.conj x⁻¹).toMonoidHom = Z d.radical c := by
    dsimp only [C₂]
    rw [←Z_act,←act_mul,inv_mul_cancel,act_one]
  have hmapF : F.map (MulAut.conj x⁻¹).toMonoidHom = F₂ := by
    have he : (Q d.radical a).map (MulAut.conj x⁻¹).toMonoidHom = Q d.radical a :=
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical a ((stabilizer d.radical a).inv_mem hx))
    dsimp only [F,F₂]
    rw [Subgroup.map_inf _ _ _ (MulAut.conj x⁻¹).injective,←Z_act,he]
  have heq₃ : ⁅Z d.radical c,F₂⁆ = K := by
    have hh := congrArg (Subgroup.map (MulAut.conj x⁻¹).toMonoidHom) heq₂
    rwa [map_commutator,hmapC,hmapF,hmapK] at hh
  have hjoin : ⁅F ⊔ F₂,Z d.radical c⁆ ≤ K :=
    commutator_sup_le_of_relative_normal (stabilizer d.radical a) F F₂ (Z d.radical c) K
      hMK (inf_le_right.trans (show Q d.radical a ≤ stabilizer d.radical a from fun _ hv => hv.1))
      (inf_le_right.trans (show Q d.radical a ≤ stabilizer d.radical a from fun _ hv => hv.1))
      (by rw [commutator_comm]; exact heq₁.le) (by rw [commutator_comm]; exact heq₃.le)
  have hU : ⁅U d.radical c,F ⊔ F₂⁆ ≤ K := by
    rw [commutator_comm] at hjoin
    exact (commutator_mono (DistanceEight.U_le_Z d.radical c) le_rfl).trans hjoin
  have hlarge := sixteen_paired_trapped_joint_movement_gt_two_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p q hsmall hqs hat hct hequal hgen hpbad hqbad hindex
  exact (Nat.not_le_of_gt hlarge) ((card_le_of_le hU).trans hbound)

include e hz hn in
/-- The equal-mover generating pair supplies an actual backward critical path
above distance two, retaining its full seeds and original edge. -/
theorem equal_backward_shift_knownSimple
    (hb : 2 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {z delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4)
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hequal : SmallMover.join (U d.radical delta) (Q d.radical delta)
        (Q d.radical (p.walk.getVert 1)) 4 =
      SmallMover.join (U d.radical (alpha d.radical)) (Q d.radical (alpha d.radical))
        (Q d.radical (p.walk.getVert 1)) 4)
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta)) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      ∃ g ∈ stabilizer d.radical (alpha d.radical),
        act d.radical g (p.walk.getVert 1) = t ∧
        Adjacent d.radical (act d.radical g delta) t ∧
        Q d.radical t ⊔ Z d.radical z = stabilizer d.radical (alpha d.radical) ∧
        2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (act d.radical g delta)) ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d)
            (act d.radical g delta) (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = t ∧
          ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i := by
  obtain ⟨t,hat,g,hg,hgt,hct,hi,x,hx,q,hq,hqs,heq,hgen₀,hgen,hpair,
    hn₀,hat₂,hct₂,hi₂,hgen₂,hn₂⟩ :=
    sixteen_equal_mover_strict_pair_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hdelta hequal hstrict
  let c := act d.radical g delta
  have hcol : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    change false ≠ color d.radical t at h1
    change color d.radical c ≠ color d.radical t at h2
    cases hc : color d.radical c <;> cases ht : color d.radical t <;> simp_all
  have backward {v : Vertex d.radical}
      (r : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) v)
      (hbad : ¬ Z d.radical c ≤ Q d.radical (r.walk.getVert (r.walk.length-2))) :
      ∃ b : CriticalPath d.radical (replacementGeometry h d)
          c (r.walk.getVert (r.walk.length-2)),
        b.walk.getVert 1 = t ∧
        ∀ i ≤ r.walk.length-2, b.walk.getVert (i+2) = r.walk.getVert i := by
    let w : (cosetGraph d.radical).Walk c (alpha d.radical) :=
      .cons ((cosetGraph_adj d.radical _ _).mpr hct)
        (.cons ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat)) .nil)
    have hw : w.length = 2 := rfl
    let b := r.prepend_two (Nat.le_of_lt hb) hcol w hw hbad
    refine ⟨b,?_,fun i hi => r.prepend_two_overlap _ _ _ _ _ hi⟩
    simp only [b,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
      hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
      SimpleGraph.Walk.getVert_zero]
  by_cases hpbad : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2))
  · by_cases hqbad : Z d.radical c ≤ Q d.radical (q.walk.getVert (q.walk.length-2))
    · exact (sixteen_equal_paired_traps_impossible_knownSimple (e := e) (hz := hz) (hn := hn) hb hcard p hsmall
        hat hct heq x (Ltilde_le_stabilizer _ hx) q hq hqs hgen hpair
        hpbad hqbad hn₀ hn₂ hi).elim
    · obtain ⟨v,hvt,hover⟩ := backward q hqbad
      let y := g*x⁻¹
      have hy : y ∈ stabilizer d.radical (alpha d.radical) :=
        mul_mem hg (inv_mem (Ltilde_le_stabilizer _ hx))
      have hyt : act d.radical y (p.walk.getVert 1) = act d.radical x⁻¹ t := by
        rw [show y=g*x⁻¹ from rfl,act_mul,hgt]
      have hstart : act d.radical x⁻¹ (act d.radical g delta) = act d.radical y delta :=
        (act_mul d.radical g x⁻¹ delta).symm
      rw [hstart] at hct₂ hi₂
      refine ⟨act d.radical x⁻¹ t,hat₂,y,hy,hyt,hct₂,hgen₂,hi₂,?_⟩
      have hlen : q.walk.length = p.walk.length := q.length_eq_b.trans p.length_eq_b.symm
      have hend : act d.radical x⁻¹ (q.walk.getVert (q.walk.length-2)) =
          p.walk.getVert (p.walk.length-2) := by
        rw [hlen,hq,←act_mul,mul_inv_cancel,act_one]
      have hex : ∃ w : CriticalPath d.radical (replacementGeometry h d)
          (act d.radical x⁻¹ (act d.radical g delta))
          (act d.radical x⁻¹ (q.walk.getVert (q.walk.length-2))),
          w.walk.getVert 1 = act d.radical x⁻¹ t ∧
          ∀ i ≤ p.walk.length-2, w.walk.getVert (i+2) = p.walk.getVert i := by
        refine ⟨v.act x⁻¹,?_,?_⟩
        · simp only [CriticalPath.act,actWalk_getVert,hvt]
        · intro i hi
          have hiq : i ≤ q.walk.length-2 := hlen.symm ▸ hi
          simp only [CriticalPath.act,actWalk_getVert,hover i hiq,hq,
            ←act_mul,mul_inv_cancel,act_one]
      rwa [hstart,hend] at hex
  · exact ⟨t,hat,g,hg,hgt,hct,hgen₀,hi,backward p hpbad⟩
include e hz hn in
/-- Both neighboring-mover cases give the same original backward path. -/
theorem backward_shift_knownSimple
    (hb : replacementDistance h d = 4)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {z delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4)
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta)) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      ∃ g ∈ stabilizer d.radical (alpha d.radical),
        act d.radical g (p.walk.getVert 1) = t ∧
        Adjacent d.radical (act d.radical g delta) t ∧
        Q d.radical t ⊔ Z d.radical z = stabilizer d.radical (alpha d.radical) ∧
        2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (act d.radical g delta)) ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d)
            (act d.radical g delta) (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = t ∧
          ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i := by
  by_cases he : SmallMover.join (U d.radical delta) (Q d.radical delta)
      (Q d.radical (p.walk.getVert 1)) 4 =
      SmallMover.join (U d.radical (alpha d.radical)) (Q d.radical (alpha d.radical))
        (Q d.radical (p.walk.getVert 1)) 4
  · exact equal_backward_shift_knownSimple (e := e) (hz := hz) (hn := hn)
      (by omega) hcard p hsmall hdelta he hstrict
  · exact SixteenUnequal.unequal_backward_shift_knownSimple hb hcard p hsmall hdelta he hstrict

include e hz hn in
/-- A strict forward slice with arbitrary neighboring movers supplies initial
nonabelian large-slice selection, including both full moving covers. -/
theorem large_forward_initial_selection_knownSimple
    (hb : replacementDistance h d = 4)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))) :
    ∃ w, ∃ r : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) w,
      ⁅localZSpan d.radical (r.walk.getVert 2) (alpha d.radical),
        localZSpan d.radical (r.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥ ∧
      2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (r.walk.getVert 2)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  refine ⟨z,p,?_,hstrict⟩
  by_cases hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical))
  · exact large_image_selected_span_nonabelian s hc hb p hlarge
  have hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4 := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hct : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨t,hat,g,hg,hgt,hct,hgen,hi,q,hq,hover⟩ :=
    backward_shift_knownSimple hb hcard p hsmall hct hstrict
  let P := localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)
  have hstart : Z d.radical (act d.radical g (p.walk.getVert 2)) ≤ P := by
    rw [Z_act]
    exact (map_mono (Z_le_localZSpan d.radical _ _)).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (localZSpan_normalized d.radical _ _
        ((stabilizer d.radical (alpha d.radical)).inv_mem hg)))
  have hend : Z d.radical (p.walk.getVert (p.walk.length-2)) ≤ P := by
    rw [hl]
    exact Z_le_localZSpan d.radical _ _
  intro hzero
  exact critical_Z_commutator_ne_bot s hc q
    (le_bot_iff.mp ((commutator_mono hstart hend).trans_eq hzero))

private theorem strict_neighbor_at_first_edge
    (hb : replacementDistance h d = 4) {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hstrict : 2 < (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (alpha d.radical))) :
    ∃ delta, Adjacent d.radical delta (p.walk.getVert 1) ∧
      2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical delta) := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hcol : color d.radical (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical hcol
  have hbase : act d.radical g⁻¹ (p.walk.getVert 2) = alpha d.radical := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have hat₀ : Adjacent d.radical (alpha d.radical) (act d.radical g⁻¹ (p.walk.getVert 1)) := by
    simpa only [hbase] using (adjacent_act_iff d.radical g⁻¹ _ _).mpr hct
  obtain ⟨k,hk,hkt⟩ := stabilizer_transitive_neighbors d.radical (alpha d.radical) hat₀ hat
  have hdelta : Adjacent d.radical (act d.radical k (act d.radical g⁻¹ (alpha d.radical)))
      (p.walk.getVert 1) := by
    rw [←hkt]
    exact (adjacent_act_iff d.radical k _ _).mpr ((adjacent_act_iff d.radical g⁻¹ _ _).mpr hat)
  have hi : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (act d.radical g⁻¹ (alpha d.radical))) := by
    have hh : 2 < (B d.radical (act d.radical g⁻¹ (p.walk.getVert 2))
        ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (act d.radical g⁻¹ (alpha d.radical))) := by
      rw [Escape.PairingControl.FirstPairing.B_act hb2 g⁻¹ _ hcol,
        U_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
      exact hstrict
    simpa only [hbase] using hh
  have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj k⁻¹).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb2 _ rfl ((stabilizer d.radical (alpha d.radical)).inv_mem hk))
  refine ⟨_,hdelta,?_⟩
  rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
  exact hi

include e hz hn in
/-- Every order-sixteen radical image has an initial nonabelian large-slice
critical path at distance four. Both moving covers and the full central
attachments remain in the literal minimum characteristic replacement. -/
theorem initial_selection_knownSimple
    (hb : replacementDistance h d = 4)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16) :
    ∃ z, ∃ p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z,
      ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
        localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥ ∧
      2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (p.walk.getVert 2)) := by
  classical
  by_contra hno
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hlarge := (initial_selection_or_large_midpoint_slices_knownSimple
    (e := e) (hz := hz) (hn := hn) hb).resolve_left hno
  obtain ⟨z,⟨p⟩⟩ := CriticalPath.exists_from (R := d.radical)
    (geometry := replacementGeometry h d) (a := alpha d.radical) rfl
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  obtain ⟨delta,hdelta,hstrict⟩ := strict_neighbor_at_first_edge hb p (hlarge _ _ p).1
  have hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4 := by
    by_contra! hlargeimage
    exact hno (exists_nonabelian_large_slice_knownSimple (e := e) (hz := hz) (hn := hn)
      hb p (large_image_selected_span_nonabelian s hc hb p hlargeimage))
  obtain ⟨t,hat,g,hg,hgt,hct,_,_,q,_,_⟩ :=
    backward_shift_knownSimple hb hcard p hsmall hdelta hstrict
  have hout : ¬ V d.radical (alpha d.radical) ≤ Q d.radical (p.walk.getVert 2) := by
    intro htrap
    apply q.critical.2
    rw [hl]
    exact (neighbor_seed_le_radius hat hct).trans htrap
  obtain ⟨w,r,hr⟩ := radius_escape_reciprocal_path s hc hb p hout
  have hforward : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) := by
    simpa only [hr] using (hlarge _ _ r).1
  exact hno (large_forward_initial_selection_knownSimple hb hcard p hforward)

include e hz hn in
/-- The literal original-replacement selection now leaves only the non-elementary
image-eight branch, with original Sylow and exact restriction index retained. -/
theorem initial_selection_or_eight_knownSimple
    (hb : replacementDistance h d = 4) :
    (∃ z, ∃ p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z,
      ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
        localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥ ∧
      2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (p.walk.getVert 2))) ∨
    ((∃ T : Sylow 2 (L ⊔ R : Subgroup G),
        (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R)) ∧
      (¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d))) ∧
      d.radical.relIndex ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup) = 2 ∧
      Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8) := by
  rcases initial_selection_or_nonelementary_sylow_knownSimple
    (e := e) (hz := hz) (hn := hn) hb with hsel | ⟨hSylow,hne,hcases⟩
  · exact Or.inl hsel
  rcases hcases with ⟨_,hcard⟩ | ⟨hi,hcard⟩
  · exact Or.inl (initial_selection_knownSimple hb hcard)
  · exact Or.inr ⟨hSylow,hne,hi,hcard⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.SixteenEqual
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
