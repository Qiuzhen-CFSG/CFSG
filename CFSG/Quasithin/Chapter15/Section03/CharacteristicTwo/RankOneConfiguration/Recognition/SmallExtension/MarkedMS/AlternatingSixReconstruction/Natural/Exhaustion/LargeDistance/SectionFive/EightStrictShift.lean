module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightSelection
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightUnequalCore
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightSelection
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightSmallMovers
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.NonsylowImage
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeCommonFixer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTrappedExclusion

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubePredecessorSlice

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeResidualRotation

/-!
# Strict shifts and radius escape for the three-duad image-eight branches

For the mixed and even order-four movers, construct an actual edge core
which generates the starting stabilizer with a critical endpoint seed.
Inside the canonical Sylow quotient, an order-four element supplies its
nontrivial square. Together with a crossing transposition this recovers the
first two pair swaps; the mover's absence of fixed letters recovers the third.
Short checked permutation identities then give the full symmetric group.
The lift retains the entire quotient kernel and the actual edge core.

This selection closes the unequal-mover strict shift. Combining it with
EightSelection's equal-mover proof, including its zero-commutator case,
bounds every slice under a trapped radius, with no mover comparison or
small-critical-image premise. The full predecessor slice is the reverse
kernel, and its commutator with the whole predecessor core is fixed by the
predecessor residual. The same residual element preserves the nonzero
kernel line and constructs an overlapping critical path. Whole-seed
alignment contradicts a trapped nonnormalizing seed and proves radius
escape in both three-duad branches.

The applications give universal critical escape and actual forward and
backward paths, preserving their overlaps and the original radical's index
two. Both moved covers of orders sixteen and thirty-two and all central
attachments remain. The two-transposition mover, strict forward bounds,
image-eight terminal exclusion and the general distance-four cases are
still required; this module does not prove the unconditional distance bound.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.5)--(5.8), printed pp.915--920. The finite coordinates are the
existing six-letter offender models of Aschbacher--Smith B.3.2--4.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightStrictShift
local notation "S" => Equiv.Perm (Fin 6)
open CubeCommonFixer
private abbrev a : S := Equiv.swap 0 1
private abbrev b : S := Equiv.swap 2 3
private abbrev c : S := Equiv.swap 4 5
private abbrev t : S := Equiv.swap 0 4
private abbrev z : S := kleinFirst 6 (by decide)
private def pairWord (i : Fin 4) : S := ![1,a,b,a*b] i
private def adjustWord (i : Fin 4) : S := ![1,b,c,b*c] i

private theorem canonical_generates (E : Subgroup S) (hES : E ≤ sylowCarrier)
    (hne : ¬ IsElementaryAbelian 2 E)
    (hy : ∃ y ∈ E ⊓ D 6, y (4 : Fin 6) ≠ 4) : E ⊔ zpowers t = ⊤ := by
  have hex : ∃ x ∈ E, x^2 ≠ 1 := by
    by_contra! hh
    exact hne (NonsylowImage.elementary_of_squares E hh)
  obtain ⟨x,hx,hsq⟩ := hex
  obtain ⟨i,rfl⟩ := (mem_sylowCarrier_iff _).mp (hES hx)
  have hxz : (sylowWords i)^2 = z :=
    (NonsylowImage.sylow_square_certificate i).resolve_left hsq
  obtain ⟨y,hyE,hy4⟩ := hy
  obtain ⟨j,rfl⟩ := (mem_disjointTranspositions_iff (3 : Fin 4) _).mp hyE.2
  let N := E ⊔ zpowers t
  have ht : t ∈ N := mem_sup_right (mem_zpowers _)
  have hz : z ∈ N := mem_sup_left (hxz ▸ E.pow_mem hx 2)
  have hA : a ∈ N := by
    have cert : t*z*t*z*t=a := by decide +kernel
    rw [←cert]
    exact N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem ht hz) ht) hz) ht
  have hB : b ∈ N := by
    have cert : a*z=b := by decide +kernel
    rw [←cert]
    exact N.mul_mem hA hz
  have hW (k : Fin 4) : pairWord k ∈ N := by
    fin_cases k
    · exact N.one_mem
    · exact hA
    · exact hB
    · exact N.mul_mem hA hB
  have hC : c ∈ N := by
    have cert : ∀ j : Fin 8, dWords j (4 : Fin 6) ≠ 4 →
        ∃ k : Fin 4, dWords j * pairWord k = c := by decide +kernel
    obtain ⟨k,hk⟩ := cert j hy4
    rw [←hk]
    exact N.mul_mem (mem_sup_left hyE.1) (hW k)
  have hW' (k : Fin 4) : adjustWord k ∈ N := by
    fin_cases k
    · exact N.one_mem
    · exact hB
    · exact hC
    · exact N.mul_mem hB hC
  have h24 : Equiv.swap (2 : Fin 6) 4 ∈ N := by
    have cert : ∀ i : Fin 16, (sylowWords i)^2 ≠ 1 →
        ∃ k : Fin 4, (MulAut.conj (adjustWord k * sylowWords i)) t = Equiv.swap 2 4 := by
      decide +kernel
    obtain ⟨k,hk⟩ := cert i hsq
    rw [←hk]
    exact N.mul_mem (N.mul_mem (N.mul_mem (hW' k) (mem_sup_left hx)) ht)
      (N.inv_mem (N.mul_mem (hW' k) (mem_sup_left hx)))
  apply chain_generates (1 : S)
  intro k
  change Equiv.swap k.castSucc k.succ ∈ N
  fin_cases k
  · exact hA
  · have cert : a*t*(Equiv.swap (2 : Fin 6) 4)*t*a=Equiv.swap 1 2 := by decide +kernel
    change Equiv.swap (1 : Fin 6) 2 ∈ N
    rw [←cert]
    exact N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem hA ht) h24) ht) hA
  · exact hB
  · have cert : b*(Equiv.swap (2 : Fin 6) 4)*b=Equiv.swap 3 4 := by decide +kernel
    change Equiv.swap (3 : Fin 6) 4 ∈ N
    rw [←cert]
    exact N.mul_mem (N.mul_mem hB h24) hB
  · exact hC

private theorem model_moves (m : Fin 2) (u : S) (q : Fin 6) :
    ∃ y ∈ (EightSelection.model m).map (MulAut.conj u).toMonoidHom, y q ≠ q := by
  have cert : ∀ m : Fin 2, ∀ q : Fin 6, ∃ i : Fin 4,
      EightSelection.word m i q ≠ q := by decide +kernel
  obtain ⟨i,hi⟩ := cert m (u⁻¹ q)
  refine ⟨(MulAut.conj u) (EightSelection.word m i),
    mem_map_of_mem _ (EightSelection.word_mem m i),?_⟩
  intro he
  apply hi
  have hh := congrArg (fun q => u⁻¹ q) he
  simpa [MulAut.conj_apply,Equiv.Perm.mul_apply] using hh

private theorem conjugate_generates (E J : Subgroup S) (u : S)
    (hES : E ≤ sylowCarrier.map (MulAut.conj u).toMonoidHom)
    (hne : ¬ IsElementaryAbelian 2 E)
    (hJ : J = E ⊓ (D 6).map (MulAut.conj u).toMonoidHom)
    (hmodel : IsConjugateTo J plus ∨ IsConjugateTo J (evenPart 6))
    (v : S) (hv : v.IsSwap) :
    ∃ w : S, E.map (MulAut.conj w).toMonoidHom ⊔ zpowers v = ⊤ := by
  let f := (MulAut.conj u⁻¹).toMonoidHom
  have back (A : Subgroup S) : (A.map (MulAut.conj u).toMonoidHom).map f = A := by
    rw [conjugate_twice,inv_mul_cancel,
      show (MulAut.conj (1 : S)).toMonoidHom = MonoidHom.id S from rfl,map_id]
  have hE : E.map f ≤ sylowCarrier := (map_mono hES).trans_eq (back _)
  have hn : ¬ IsElementaryAbelian 2 (E.map f) := by
    intro hh
    let := hh
    apply hne
    apply NonsylowImage.elementary_of_squares
    intro x hx
    apply (MulAut.conj u⁻¹).injective
    rw [map_pow,map_one]
    exact elemPow_eq_one_of_isElementaryAbelian _ (mem_map_of_mem f hx)
  have hJF : J.map f = E.map f ⊓ D 6 := by
    rw [hJ,map_inf _ _ _ (MulAut.conj u⁻¹).injective,back]
  obtain ⟨m,r,hr⟩ : ∃ m : Fin 2, ∃ r : S,
      J = (EightSelection.model m).map (MulAut.conj r).toMonoidHom := by
    rcases hmodel with ⟨r,hr⟩ | ⟨r,hr⟩
    · exact ⟨0,r,hr⟩
    · exact ⟨1,r,hr⟩
  have hmove : ∃ y ∈ E.map f ⊓ D 6, y (4 : Fin 6) ≠ 4 := by
    rw [←hJF,hr,conjugate_twice]
    exact model_moves m (u⁻¹*r) 4
  have hgen := canonical_generates (E.map f) hE hn hmove
  obtain ⟨r,hr⟩ := swap_conjugator v hv
  let k : S := r.val * Equiv.swap 1 4
  have hk : (MulAut.conj k).toMonoidHom t = v := by
    have cert : (MulAut.conj (Equiv.swap (1 : Fin 6) 4)) t = a := by decide +kernel
    change (MulAut.conj r.val) ((MulAut.conj (Equiv.swap 1 4)) t) = v
    rw [cert]
    exact hr
  refine ⟨k*u⁻¹,?_⟩
  have hh := congrArg (Subgroup.map (MulAut.conj k).toMonoidHom) hgen
  rwa [Subgroup.map_sup,conjugate_twice,MonoidHom.map_zpowers,hk,
    map_top_of_surjective (MulAut.conj k).toMonoidHom (MulAut.conj k).surjective] at hh

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include e hz hn in
/-- The actual edge core, conjugated inside the starting stabilizer, generates
with the critical endpoint seed in the mixed and even mover branches. -/
theorem three_duad_generating_edge_knownSimple
    (hb : 4 < replacementDistance h d) (hmodel : EightSelection.ThreeDuadMover h e hz hn d)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4) :
    ∃ g ∈ stabilizer d.radical (alpha d.radical),
      let t := act d.radical g (beta d.radical)
      Adjacent d.radical (alpha d.radical) t ∧
        Q d.radical t ⊔ Z d.radical z = stabilizer d.radical (alpha d.radical) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let J := SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) d.radical 4
  obtain ⟨u,hN,_,_,hJ,_,_,_,_⟩ := EightSmallMovers.radical_small_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) hb
  obtain ⟨_,hne,_,_⟩ := SylowWholeCore.four_lt_original_sylow_eight_image_knownSimple
    (e := e) (hz := hz) (hn := hn) hb
  rw [←SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s] at hne
  have hmodel' : IsConjugateTo (J.map s.projection) plus ∨
      IsConjugateTo (J.map s.projection) (evenPart 6) := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  obtain ⟨a,ha,hswap⟩ := small_critical_image_swap s hc p hsmall
  obtain ⟨w,hw⟩ := conjugate_generates (d.radical.map s.projection) (J.map s.projection) u
    ((map_mono d.radical.le_normalizer).trans_eq hN) hne hJ hmodel' a hswap
  obtain ⟨g,hg⟩ := s.surjective w
  let E := d.radical.map (MulAut.conj g).toMonoidHom
  let A := (Z d.radical z).comap (embedM d.radical)
  have hker : s.projection.ker ≤ E := by
    have he : s.projection.ker.map (MulAut.conj g).toMonoidHom = s.projection.ker :=
      mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
    rw [←he]
    apply map_mono
    rw [s.projection_kernel]
    exact replacement_core_le_radical h d
  have htop : E ⊔ A = ⊤ := by
    apply map_injective_of_ker_le s.projection (hker.trans le_sup_left) le_top
    rw [Subgroup.map_sup,SylowCompatible.image_conjugate,map_top_of_surjective s.projection s.surjective,hg]
    apply top_unique
    rw [←hw]
    exact sup_le_sup_left (zpowers_le.mpr ha) _
  let f := (embedM d.radical g)⁻¹
  have hf : f ∈ stabilizer d.radical (alpha d.radical) := by
    change f ∈ stabilizer d.radical (mVertex d.radical 1)
    rw [stabilizer_m_base]
    exact ⟨g⁻¹,by simp only [map_inv,f]⟩
  have hQt : Q d.radical (act d.radical f (beta d.radical)) = E.map (embedM d.radical) := by
    rw [Q_act,Q_beta,SylowCompatible.image_conjugate]
    simp only [f,inv_inv]
  have hAm : A.map (embedM d.radical) = Z d.radical z :=
    map_comap_eq_self ((critical_Z_le_stabilizer d.radical (replacementGeometry h d)
      (alpha d.radical) rfl (replacementDistance_pos h d) p.critical).trans_eq
        (stabilizer_m_base d.radical))
  refine ⟨f,hf,?_,?_⟩
  · have hfix : act d.radical f (alpha d.radical)=alpha d.radical := hf
    rw [←hfix]
    exact (adjacent_act_iff d.radical f _ _).mpr (base_adjacent d.radical)
  · have hh := congrArg (Subgroup.map (embedM d.radical)) htop
    rw [Subgroup.map_sup,←hQt,hAm,←MonoidHom.range_eq_map] at hh
    exact hh.trans (stabilizer_m_base d.radical).symm

include e hz hn in
/-- A strict unequal mover has a backward critical path on a constructed
edge; the original vertices and the same seed transporter are retained. -/
theorem three_duad_unequal_backward_knownSimple
    (hb : 4 < replacementDistance h d) (hmodel : EightSelection.ThreeDuadMover h e hz hn d)
    {z delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4)
    (hdelta : Adjacent d.radical delta (beta d.radical))
    (hne : EightEdgeComparison.edgeMover (d := d) delta (beta d.radical) ≠
      EightEdgeComparison.edgeMover (d := d) (alpha d.radical) (beta d.radical))
    (hstrict : 2 < (B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical delta)) :
    ∃ g ∈ stabilizer d.radical (alpha d.radical),
      let c := act d.radical g delta
      let t := act d.radical g (beta d.radical)
      Adjacent d.radical (alpha d.radical) t ∧ Adjacent d.radical c t ∧
        2 < (B d.radical (alpha d.radical)
          ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical c) ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d)
            c (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = t ∧
          ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i := by
  obtain ⟨g,hg,hat,hgen⟩ := three_duad_generating_edge_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hmodel p hsmall
  let c := act d.radical g delta
  let t := act d.radical g (beta d.radical)
  have hga : act d.radical g (alpha d.radical) = alpha d.radical := hg
  have hct : Adjacent d.radical c t := (adjacent_act_iff d.radical g _ _).mpr hdelta
  have hne' : EightEdgeComparison.edgeMover (d := d) c t ≠
      EightEdgeComparison.edgeMover (d := d) (alpha d.radical) t := by
    intro he
    apply hne
    apply map_injective (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective
    dsimp only [EightEdgeComparison.edgeMover] at he ⊢
    rwa [SmallMover.join_map _ (MulAut.conj g⁻¹).injective,
      SmallMover.join_map _ (MulAut.conj g⁻¹).injective,←U_act,←Q_act,←Q_act,
      ←U_act,←Q_act,hga]
  have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom =
      B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      (by omega : 2 < replacementDistance h d) _ rfl ((stabilizer d.radical _).inv_mem hg))
  have hi : 2 < (B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical c) := by
    change 2 < (B d.radical (alpha d.radical) _).relIndex (U d.radical (act d.radical g delta))
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact hstrict
  exact ⟨g,hg,hat,hct,hi,EightUnequalCore.unequal_edge_generating_backward_path_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall hat hct hne' hgen hi⟩

include e hz hn in
/-- Every strict slice has an overlapping backward critical path in the
three-duad branches, with no mover comparison or edge-generation premise. -/
theorem three_duad_strict_backward_knownSimple
    (hb : 4 < replacementDistance h d) (hmodel : EightSelection.ThreeDuadMover h e hz hn d)
    {z delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4)
    (hdelta : Adjacent d.radical delta (beta d.radical))
    (hstrict : 2 < (B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical delta)) :
    ∃ g ∈ stabilizer d.radical (alpha d.radical),
      let c := act d.radical g delta
      let t := act d.radical g (beta d.radical)
      Adjacent d.radical (alpha d.radical) t ∧ Adjacent d.radical c t ∧
        2 < (B d.radical (alpha d.radical)
          ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical c) ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d)
            c (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = t ∧
          ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i := by
  by_cases he : EightEdgeComparison.edgeMover (d := d) delta (beta d.radical) =
      EightEdgeComparison.edgeMover (d := d) (alpha d.radical) (beta d.radical)
  · exact EightSelection.three_duad_equal_mover_backward_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hmodel p hsmall hdelta he hstrict
  · exact three_duad_unequal_backward_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hmodel p hsmall hdelta he hstrict

include e hz hn in
/-- A trapped radius bounds every neighboring slice in the mixed and
even branches; neither mover equality nor a small critical image is assumed. -/
theorem three_duad_trapped_slice_le_two_knownSimple
    (hb : 4 < replacementDistance h d) (hmodel : EightSelection.ThreeDuadMover h e hz hn d)
    {z delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (htrap : V d.radical (alpha d.radical) ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hdelta : Adjacent d.radical delta (beta d.radical)) :
    (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta) ≤ 2 := by
  by_contra! hstrict
  have hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4 := by
    by_contra! hlarge
    exact SylowActor.four_lt_large_image_radius_escape_knownSimple
      (e := e) (hz := hz) (hn := hn) hb p hlarge htrap
  obtain ⟨g,hg,hat,hct,_,q,_,_⟩ := three_duad_strict_backward_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hmodel p hsmall hdelta hstrict
  exact q.critical.2 ((neighbor_seed_le_radius hat hct).trans htrap)

include e hz hn in
/-- The trapped-slice estimate at every component vertex and every incident
edge, using the actual graph action and the same canonical mover alternative. -/
theorem three_duad_trapped_slice_at_knownSimple
    (hb : 4 < replacementDistance h d) (hmodel : EightSelection.ThreeDuadMover h e hz hn d)
    {a z c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (htrap : V d.radical a ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t) :
    (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical c) ≤ 2 := by
  obtain ⟨g,hg|hg⟩ := edge_transitive d.radical hat (base_adjacent d.radical)
  · change act d.radical g a = alpha d.radical ∧ act d.radical g t = beta d.radical at hg
    have base := three_duad_trapped_slice_le_two_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hmodel
      (z := act d.radical g z) (delta := act d.radical g c)
    rw [←hg.1,←hg.2] at base
    have htr : V d.radical (act d.radical g a) ≤
        Q d.radical ((p.act g).walk.getVert ((p.act g).walk.length-2)) := by
      simp only [CriticalPath.act,actWalk_getVert,actWalk_length,V_act,Q_act]
      exact map_mono htrap
    have hi := base (p.act g) htr ((adjacent_act_iff d.radical g _ _).mpr hct)
    rwa [Escape.PairingControl.FirstPairing.B_act
      (by omega : 2 < replacementDistance h d) g a p.start_color,
      U_act,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective] at hi
  · have ht : color d.radical (beta d.radical) = false := by
      change color d.radical (hVertex d.radical 1) = false
      rw [←hg.1,action_preserves_color,p.start_color]
    cases ht

include e hz hn in
/-- One trapped radius bounds all slices at every component vertex. -/
theorem three_duad_trapped_all_slices_le_two_knownSimple
    (hb : 4 < replacementDistance h d)
    (hmodel : EightSelection.ThreeDuadMover h e hz hn d)
    {a₀ z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a₀ z)
    (htrap : V d.radical a₀ ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    {a c t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t) :
    (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical c) ≤ 2 := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical ha
  obtain ⟨j,hj⟩ := exists_mVertex_of_color d.radical p.start_color
  let y := g⁻¹*j
  have hya : act d.radical y a = a₀ := by
    rw [hg,hj,act_mVertex]
    simp only [y,mul_inv_cancel_left]
  have hyt : Adjacent d.radical a₀ (act d.radical y t) := by
    rw [←hya]
    exact (adjacent_act_iff d.radical y _ _).mpr hat
  have hh := three_duad_trapped_slice_at_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hmodel p htrap hyt
      ((adjacent_act_iff d.radical y _ _).mpr hct)
  rw [←hya,Escape.PairingControl.FirstPairing.B_act (by omega : 2 < replacementDistance h d)
    y a ha,U_act,relIndex_map_map_of_injective _ _ (MulAut.conj y⁻¹).injective] at hh
  exact hh

include e hz hn in
/-- Trapping identifies every full predecessor slice with its literal reverse kernel. -/
theorem three_duad_trapped_predecessor_kernel_knownSimple
    (hb : 4 < replacementDistance h d)
    (hmodel : EightSelection.ThreeDuadMover h e hz hn d)
    {a₀ z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a₀ z)
    (htrap : V d.radical a₀ ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    {a a' : Vertex d.radical}
    (q : CriticalPath d.radical (replacementGeometry h d) a a') :
    Z d.radical a' ⊓ B d.radical (q.walk.getVert (q.walk.length-2))
        ((replacementGeometry h d).Z_normal _) = Z d.radical a' ⊓ Q d.radical a ∧
      (Q d.radical a').relIndex (Z d.radical a) = 2 ∧
      (Q d.radical a).relIndex (Z d.radical a') = 2 := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hl : 2 < q.walk.length := q.length_eq_b ▸ hb2
  have hcol : color d.radical (q.walk.getVert (q.walk.length-2)) = false := by
    apply (q.vertex_color (Nat.sub_le _ _)).mpr
    have he := replacementDistance_even h d
    rw [Nat.even_iff] at he ⊢
    have hh : q.walk.length = replacementDistance h d := q.length_eq_b
    omega
  have hct : Adjacent d.radical (q.walk.getVert (q.walk.length-2))
      (q.walk.getVert (q.walk.length-1)) := by
    have hh := q.walk.adj_getVert_succ (i := q.walk.length-2) (by omega)
    rw [show q.walk.length-2+1=q.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have het : Adjacent d.radical a' (q.walk.getVert (q.walk.length-1)) := by
    have hh := q.walk.adj_getVert_succ (i := q.walk.length-1) (by omega)
    rw [show q.walk.length-1+1=q.walk.length by omega,q.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  exact critical_predecessor_slice_eq_kernel s hc hb2 q
    (three_duad_trapped_all_slices_le_two_knownSimple (e := e) (hz := hz) (hn := hn)
      hb hmodel p htrap hcol hct het)

include e hz hn in
/-- The constructed generating edge at an arbitrary component vertex of the
same natural replacement graph. -/
theorem three_duad_generating_edge_at_knownSimple
    (hb : 4 < replacementDistance h d) (hmodel : EightSelection.ThreeDuadMover h e hz hn d)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4) :
    ∃ t, Adjacent d.radical a t ∧
      Q d.radical t ⊔ Z d.radical z = stabilizer d.radical a := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color d.radical p.start_color
  have hga : act d.radical g⁻¹ (mVertex d.radical g) = alpha d.radical := by
    simp only [act_mVertex,mul_inv_cancel]
    rfl
  have base := three_duad_generating_edge_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hmodel (z := act d.radical g⁻¹ z)
  rw [←hga] at base
  have hs : (Q d.radical (act d.radical g⁻¹ z)).relIndex
      (Z d.radical (act d.radical g⁻¹ (mVertex d.radical g))) < 4 := by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj (g⁻¹)⁻¹).injective]
    exact hsmall
  obtain ⟨j,hj,hat,hgen⟩ := base (p.act g⁻¹) hs
  let t := act d.radical j (beta d.radical)
  have hcancel (v : Vertex d.radical) : act d.radical g (act d.radical g⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  refine ⟨act d.radical g t,?_,?_⟩
  · have hh := (adjacent_act_iff d.radical g _ _).mpr hat
    rwa [hcancel] at hh
  · have hh := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hgen
    rw [Subgroup.map_sup,←Q_act,←Z_act,←stabilizer_act,hcancel,hcancel] at hh
    exact hh

open EightPairedNormalizer

include e hz hn in
/-- The whole reverse-kernel commutator is fixed by the predecessor
residual under trapping in either three-duad branch. -/
theorem three_duad_trapped_predecessor_residual_fixed_knownSimple
    (hb : 4 < replacementDistance h d)
    (hmodel : EightSelection.ThreeDuadMover h e hz hn d)
    {a₀ z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a₀ z)
    (htrap : V d.radical a₀ ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    {a a' : Vertex d.radical}
    (q : CriticalPath d.radical (replacementGeometry h d) a a')
 :
    let c := q.walk.getVert (q.walk.length-2)
    let N := ⁅Z d.radical a' ⊓ Q d.radical a,Q d.radical c⁆
    Nat.card N ≤ 8 ∧ N ≤ fixedCore d.radical c ∧
      stabilizer d.radical c ≤ normalizer (N : Set (FreeAmalgam d.radical)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hl : 2 < q.walk.length := q.length_eq_b ▸ hb2
  have hcol : color d.radical (q.walk.getVert (q.walk.length-2)) = false := by
    apply (q.vertex_color (Nat.sub_le _ _)).mpr
    have he := replacementDistance_even h d
    rw [Nat.even_iff] at he ⊢
    have hh : q.walk.length = replacementDistance h d := q.length_eq_b
    omega
  have hct : Adjacent d.radical (q.walk.getVert (q.walk.length-2))
      (q.walk.getVert (q.walk.length-1)) := by
    have hh := q.walk.adj_getVert_succ (i := q.walk.length-2) (by omega)
    rw [show q.walk.length-2+1=q.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have het : Adjacent d.radical a' (q.walk.getVert (q.walk.length-1)) := by
    have hh := q.walk.adj_getVert_succ (i := q.walk.length-1) (by omega)
    rw [show q.walk.length-1+1=q.walk.length by omega,q.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  exact predecessor_slice_commutator_residual_fixed s hc hb2 q
    (three_duad_trapped_all_slices_le_two_knownSimple (e := e) (hz := hz) (hn := hn)
      hb hmodel p htrap hcol hct het)

include e hz hn in
/-- A predecessor residual element preserves the commutator while conjugating
an arbitrary core actor, using the literal full reverse kernel. -/
theorem three_duad_trapped_radius_residual_transport_knownSimple
    (hb : 4 < replacementDistance h d)
    (hmodel : EightSelection.ThreeDuadMover h e hz hn d)
    {a₀ a₁ : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a₀ a₁)
    (hbad : V d.radical a₀ ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    {a a' : Vertex d.radical}
    (q : CriticalPath d.radical (replacementGeometry h d) a a')

    (D : Subgroup (FreeAmalgam d.radical))
    (hD : D ≤ Q d.radical (q.walk.getVert (q.walk.length-2)))
    (k : FreeAmalgam d.radical)
    (hk : k ∈ Ltilde d.radical (q.walk.getVert (q.walk.length-2))) :
    ⁅Z d.radical a' ⊓ Q d.radical a,D.map (MulAut.conj k).toMonoidHom⁆ =
      ⁅Z d.radical a' ⊓ Q d.radical a,D⁆ := by
  have hh := three_duad_trapped_predecessor_kernel_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hmodel p hbad q
  have hn := three_duad_trapped_predecessor_residual_fixed_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hmodel p hbad q
  have hcol : color d.radical (q.walk.getVert (q.walk.length-2)) = false := by
    apply (q.vertex_color (Nat.sub_le _ _)).mpr
    have he := replacementDistance_even h d
    rw [Nat.even_iff] at he ⊢
    have hl : q.walk.length = replacementDistance h d := q.length_eq_b
    omega
  exact slice_commutator_transport_of_fixed (h := h) (by omega) hcol _
    (hh.1.ge.trans inf_le_right) (hn.2.1.trans inf_le_right) D hD k hk

include e hz hn in
/-- The same predecessor residual rotation preserves the nonzero whole-kernel
commutator and yields an overlapping critical path with both indices two.
No equality between terminal relative movers is needed. -/
theorem three_duad_trapped_residual_critical_path_knownSimple
    (hb4 : 4 < replacementDistance h d)
    (hmodel : EightSelection.ThreeDuadMover h e hz hn d)
    {a₀ a₁ : Vertex d.radical}
    (p₀ : CriticalPath d.radical (replacementGeometry h d) a₀ a₁)
    (htrapped : V d.radical a₀ ≤ Q d.radical (p₀.walk.getVert (p₀.walk.length-2)))
    {a a' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hD : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hne : ⁅Z d.radical a' ⊓ Q d.radical a,Z d.radical c⁆ ≠ ⊥) :
    ∃ k ∈ Ltilde d.radical (p.walk.getVert (p.walk.length-2)),
      act d.radical k (p.walk.getVert (p.walk.length-1)) = p.walk.getVert (p.walk.length-3) ∧
      ∃ q : CriticalPath d.radical (replacementGeometry h d) c (act d.radical k a'),
        q.walk.getVert 1=t ∧
        (∀ i ≤ p.walk.length-3, q.walk.getVert (i+2)=p.walk.getVert i) ∧
        (Q d.radical (act d.radical k a')).relIndex (Z d.radical c)=2 ∧
        (Q d.radical c).relIndex (Z d.radical (act d.radical k a'))=2 ∧
        let H := ⁅Z d.radical a' ⊓ Q d.radical a,Z d.radical c⁆
        Nat.card H=2 ∧
        H ≤ fixedCore d.radical (p.walk.getVert (p.walk.length-2)) ∧
        ⁅Z d.radical a' ⊓ Q d.radical a,Z d.radical (act d.radical k⁻¹ c)⁆=H ∧
        ⁅Z d.radical a',Z d.radical (act d.radical k⁻¹ c)⁆=H ∧
        ⁅U d.radical a',Z d.radical (act d.radical k⁻¹ c)⁆=H := by
  have hb : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hp := three_duad_trapped_predecessor_residual_fixed_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 hmodel p₀ htrapped p
  have htransport (k : FreeAmalgam d.radical)
      (hk : k ∈ Ltilde d.radical (p.walk.getVert (p.walk.length-2))) :
      ⁅Z d.radical a' ⊓ Q d.radical a,Z d.radical (act d.radical k⁻¹ c)⁆ =
        ⁅Z d.radical a' ⊓ Q d.radical a,Z d.radical c⁆ := by
    rw [Z_act,inv_inv]
    exact three_duad_trapped_radius_residual_transport_knownSimple
      (e := e) (hz := hz) (hn := hn) hb4 hmodel p₀ htrapped p _ hD k hk
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcol : color d.radical (p.walk.getVert (p.walk.length-2)) = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := replacementDistance_even h d
    rw [Nat.even_iff] at he ⊢
    have hh : p.walk.length = replacementDistance h d := p.length_eq_b
    omega
  have hpred : Adjacent d.radical (p.walk.getVert (p.walk.length-2))
      (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have hprev : Adjacent d.radical (p.walk.getVert (p.walk.length-2))
      (p.walk.getVert (p.walk.length-3)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-3) (by omega)
    rw [show p.walk.length-3+1=p.walk.length-2 by omega] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  obtain ⟨k,hk,hkt⟩ := residual_neighbor_transporter (h := h) hcol hpred hprev
  have hescape : ¬ Z d.radical c ≤ Q d.radical (act d.radical k a') := by
    intro hh
    have hm : Z d.radical (act d.radical k⁻¹ c) ≤ Q d.radical a' := by
      calc
        _ = (Z d.radical c).map (MulAut.conj k).toMonoidHom := by rw [Z_act,inv_inv]
        _ ≤ (Q d.radical (act d.radical k a')).map (MulAut.conj k).toMonoidHom := map_mono hh
        _ = Q d.radical (act d.radical k⁻¹ (act d.radical k a')) := by
          simpa only [inv_inv] using (Q_act d.radical k⁻¹ (act d.radical k a')).symm
        _ = Q d.radical a' := by rw [←act_mul,mul_inv_cancel,act_one]
    apply hne
    rw [←htransport k hk]
    exact le_bot_iff.mp ((commutator_mono inf_le_left hm).trans_eq
      (Z_centralizes_Q d.radical a' p.end_color))
  have hcfalse : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    rw [p.start_color] at h1
    cases hc : color d.radical c <;> cases ht : color d.radical t <;> simp_all
  have hlast : Adjacent d.radical (p.walk.getVert (p.walk.length-1)) a' := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have hend : (cosetGraph d.radical).Adj (p.walk.getVert (p.walk.length-3)) (act d.radical k a') := by
    rw [←hkt]
    exact (cosetGraph_adj d.radical _ _).mpr
      ((adjacent_act_iff d.radical k _ _).mpr hlast)
  let w₀ : (cosetGraph d.radical).Walk c a :=
    .cons ((cosetGraph_adj d.radical _ _).mpr hct)
      (.cons ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat)) .nil)
  let w₁ := (p.walk.take (p.walk.length-3)).concat hend
  let w := w₀.append w₁
  have hw₀ : w₀.length = 2 := rfl
  have hw : w.length = p.walk.length := by
    simp only [w,w₁,SimpleGraph.Walk.length_append,hw₀,SimpleGraph.Walk.length_concat,
      SimpleGraph.Walk.take_length,inf_eq_left.mpr (Nat.sub_le _ _)]
    omega
  have hmin := criticalDistance_le d.radical c ((replacementGeometry h d).exists_critical c hcfalse) hescape
  rw [(replacementGeometry h d).distance_constant c hcfalse] at hmin
  have hdist : (cosetGraph d.radical).dist c (act d.radical k a') = replacementDistance h d := by
    have hh := SimpleGraph.dist_le w
    rw [hw,p.length_eq_b] at hh
    exact le_antisymm hh hmin
  let q : CriticalPath d.radical (replacementGeometry h d) c (act d.radical k a') :=
    ⟨hcfalse,w,hw.trans (p.length_eq_b.trans hdist.symm),by
      refine ⟨?_,hescape⟩
      rw [(replacementGeometry h d).distance_constant c hcfalse]
      exact hdist⟩
  have hover (i : ℕ) (hi : i ≤ p.walk.length-3) :
      q.walk.getVert (i+2) = p.walk.getVert i := by
    change (w₀.append w₁).getVert (i+2)=p.walk.getVert i
    rw [SimpleGraph.Walk.getVert_append,hw₀,if_neg (by omega),Nat.add_sub_cancel]
    change ((p.walk.take (p.walk.length-3)).concat hend).getVert i=p.walk.getVert i
    rw [SimpleGraph.Walk.concat_eq_append,SimpleGraph.Walk.getVert_append']
    rw [if_pos (by simpa only [SimpleGraph.Walk.take_length,
      inf_eq_left.mpr (Nat.sub_le _ _)] using hi),SimpleGraph.Walk.take_getVert,inf_eq_right.mpr hi]
  have hq := three_duad_trapped_predecessor_kernel_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 hmodel p₀ htrapped q
  let qr := CriticalPath.ofPair (geometry := replacementGeometry h d) q.end_color
    (critical_reverse_pair s hc q)
  have hqrsmall : (Q d.radical c).relIndex (Z d.radical (act d.radical k a')) < 4 := by
    rw [hq.2.2]
    decide
  let H := ⁅Z d.radical a' ⊓ Q d.radical a,Z d.radical c⁆
  let D := ⁅Z d.radical a',Z d.radical (act d.radical k⁻¹ c)⁆
  let E := ⁅U d.radical a',Z d.radical (act d.radical k⁻¹ c)⁆
  have hcardD : Nat.card D=2 := by
    dsimp only [D]
    rw [←card_map_of_injective (f := (MulAut.conj k⁻¹).toMonoidHom)
      (MulAut.conj k⁻¹).injective,map_commutator]
    have hZ : (Z d.radical (act d.radical k⁻¹ c)).map (MulAut.conj k⁻¹).toMonoidHom =
        Z d.radical c := by
      rw [←Z_act,←act_mul,inv_mul_cancel,act_one]
    rw [←Z_act,hZ]
    exact small_critical_commutator_card s hc qr hqrsmall
  have hED : E=D := by
    apply (map_injective (f := (MulAut.conj k⁻¹).toMonoidHom) (MulAut.conj k⁻¹).injective)
    dsimp only [E,D]
    rw [map_commutator,map_commutator,←U_act,←Z_act,←Z_act,←act_mul,inv_mul_cancel,act_one]
    exact small_critical_moving_commutator_eq s hc qr hqrsmall
  have hHD : H ≤ D := by
    rw [show H=⁅Z d.radical a' ⊓ Q d.radical a,Z d.radical (act d.radical k⁻¹ c)⁆
      from (htransport k hk).symm]
    exact commutator_mono inf_le_left le_rfl
  let : Finite D := Nat.finite_of_card_ne_zero (by rw [hcardD]; decide)
  let : Finite H := Finite.of_injective (inclusion hHD) (inclusion_injective _)
  have hpos : 1 < Nat.card H := (one_lt_card_iff_ne_bot H).mpr hne
  have hHcard : Nat.card H=2 := by
    have hh := card_le_of_le hHD
    omega
  have heq : H=D := eq_of_le_of_card_ge hHD (by rw [hHcard,hcardD])
  refine ⟨k,hk,hkt,q,?_,?_,hq.2.1,hq.2.2,hHcard,?_,htransport k hk,heq.symm,hED.trans heq.symm⟩
  · change (w₀.append w₁).getVert 1=t
    simp only [SimpleGraph.Walk.getVert_append,hw₀,show 1<2 from by decide,ite_true,
      w₀,SimpleGraph.Walk.getVert_cons_succ,SimpleGraph.Walk.getVert_zero]
  · intro i hi
    change (w₀.append w₁).getVert (i+2)=p.walk.getVert i
    rw [SimpleGraph.Walk.getVert_append,hw₀,if_neg (by omega),Nat.add_sub_cancel]
    change ((p.walk.take (p.walk.length-3)).concat hend).getVert i=p.walk.getVert i
    rw [SimpleGraph.Walk.concat_eq_append,SimpleGraph.Walk.getVert_append']
    rw [if_pos (by simpa only [SimpleGraph.Walk.take_length,
      inf_eq_left.mpr (Nat.sub_le _ _)] using hi),SimpleGraph.Walk.take_getVert,inf_eq_right.mpr hi]
  · exact (commutator_mono le_rfl hD).trans hp.2.1

include e hz hn in
/-- A trapped nonnormalizing seed is impossible in either three-duad branch.
The same predecessor residual element carries its nonzero full-kernel line. -/
theorem three_duad_trapped_tail_nonnormalization_false_knownSimple
    (hb4 : 4 < replacementDistance h d)
    (hmodel : EightSelection.ThreeDuadMover h e hz hn d)
    {a₀ a₁ : Vertex d.radical}
    (p₀ : CriticalPath d.radical (replacementGeometry h d) a₀ a₁)
    (htrapped : V d.radical a₀ ≤ Q d.radical (p₀.walk.getVert (p₀.walk.length-2)))
    {a a' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hD : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hnorm : ¬ Z d.radical a' ≤ normalizer ((Z d.radical c ⊔ Z d.radical a :
      Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))) : False := by
  have hb : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hp := three_duad_trapped_predecessor_kernel_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 hmodel p₀ htrapped p
  have hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4 := by
    rw [hp.2.1]
    decide
  have hline := trapped_nonnormalizing_seed_kernel_line_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 p hsmall hat hct hD hnorm
  have hne : ⁅Z d.radical a' ⊓ Q d.radical a,Z d.radical c⁆ ≠ ⊥ := by
    intro hz
    have hh := hline.1
    rw [commutator_comm, hz, card_bot] at hh
    contradiction
  obtain ⟨k,hk,hkt,r,hrt,hover,hi,hj,hcard,hpre,hK,hZ,hU⟩ :=
    three_duad_trapped_residual_critical_path_knownSimple
      (e := e) (hz := hz) (hn := hn) hb4 hmodel p₀ htrapped p hat hct hD hne
  have halign : ⁅Z d.radical a' ⊓ Q d.radical a,Z d.radical c⁆ ≤
      ⁅Z d.radical a,Z d.radical a'⁆ ⊔
        (stabilizer d.radical a' ⊓ centralizer (stabilizer d.radical a' :
          Set (FreeAmalgam d.radical))) := by
    rw [commutator_comm]
    exact hline.2.trans (sup_le_sup_left (inf_le_inf_right _ (Z_le_stabilizer d.radical a')) _)
  have hJ : Z d.radical (act d.radical k⁻¹ c) ≤ stabilizer d.radical a' := by
    have hh := map_mono (f := (MulAut.conj k).toMonoidHom)
      (Z_le_stabilizer_of_dist_le c _ r.critical.1.le)
    have h1 := Z_act d.radical k⁻¹ c
    have h2 := stabilizer_act d.radical k⁻¹ (act d.radical k a')
    rw [inv_inv] at h1 h2
    have hcancel : act d.radical k⁻¹ (act d.radical k a') = a' := by
      rw [←act_mul,mul_inv_cancel,act_one]
    rwa [←h1,←h2,hcancel] at hh
  have hz0 := small_critical_aligned_kernel_commutator_eq_bot s hc p hsmall
    (Z d.radical (act d.radical k⁻¹ c)) hJ (hU ▸ halign)
  rw [hK] at hz0
  exact hne hz0

include e hz hn in
/-- No whole radius is trapped in the predecessor core in either three-duad
image-eight branch. The selected nonnormalizing seed is itself trapped. -/
theorem three_duad_radius_escape_knownSimple
    (hb : 4 < replacementDistance h d)
    (hmodel : EightSelection.ThreeDuadMover h e hz hn d)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z) :
    ¬ V d.radical a ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) := by
  intro htrap
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4 := by
    by_contra! hlarge
    exact SylowActor.four_lt_large_image_radius_escape_knownSimple
      (e := e) (hz := hz) (hn := hn) hb p hlarge htrap
  obtain ⟨t,hat,hgen⟩ := three_duad_generating_edge_at_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hmodel p hsmall
  obtain ⟨c,hct,hel⟩ := exists_eligible_neighbor_at_edge s hc hb2 p.start_color hat
  have hnorm : ¬ Z d.radical z ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) :
        Set (FreeAmalgam d.radical)) := by
    intro hbad
    let Y := Z d.radical c ⊔ Z d.radical a
    have hYN : stabilizer d.radical a ≤ normalizer (Y : Set (FreeAmalgam d.radical)) := by
      rw [←hgen]
      refine sup_le ?_ hbad
      apply (le_inf _ _).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
      · exact (show Q d.radical t ≤ stabilizer d.radical c from
          fun _ hx => hx.2 _ (adjacent_symm d.radical hct)).trans (Z_normalized d.radical c)
      · exact (show Q d.radical t ≤ stabilizer d.radical a from
          fun _ hx => hx.2 _ (adjacent_symm d.radical hat)).trans (Z_normalized d.radical a)
    have hYV : Y ≤ V d.radical a :=
      sup_le (neighbor_seed_le_radius hat hct) (Z_le_VBall d.radical a 2)
    have hYB := residual_small_radius_le_slice_knownSimple (e := e) hb2 p.start_color
      Y hYV ((Ltilde_le_stabilizer a).trans hYN)
      (SylowSpanSelection.adjacent_seed_span_index_le_eight
        (e := e) (hz := hz) (hn := hn) hb p.start_color hat hct)
    exact hel ((DistanceEight.U_le_Z d.radical c).trans (le_sup_left.trans hYB))
  exact three_duad_trapped_tail_nonnormalization_false_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hmodel p htrap p hat hct
      ((neighbor_seed_le_radius hat hct).trans htrap) hnorm

include e hz hn in
/-- Universal critical escape in the actual three-duad replacement graph,
including every shortest predecessor of every critical pair. -/
theorem three_duad_criticalEscape_knownSimple
    (hb4 : 4 < replacementDistance h d)
    (hmodel : EightSelection.ThreeDuadMover h e hz hn d) :
    Factorization.CriticalEscape d.radical (replacementGeometry h d) := by
  intro a ha a' hcrit c hce hpath
  obtain ⟨w,hw⟩ := (cosetGraph_connected d.radical).exists_walk_length_eq_dist a c
  obtain ⟨v,hv⟩ := (cosetGraph_connected d.radical).exists_walk_length_eq_dist c a'
  let p : CriticalPath d.radical (replacementGeometry h d) a a' :=
    ⟨ha,w.append v,by rw [SimpleGraph.Walk.length_append,hw,hv,hce,hpath],hcrit⟩
  have heq : p.walk.getVert (p.walk.length-2) = c := by
    change (w.append v).getVert ((w.append v).length-2) = c
    rw [SimpleGraph.Walk.length_append,hv,hce,Nat.add_sub_cancel]
    simp only [SimpleGraph.Walk.getVert_append,lt_self_iff_false,ite_false,
      Nat.sub_self,SimpleGraph.Walk.getVert_zero]
  simpa only [heq] using three_duad_radius_escape_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 hmodel p

include e hz hn in
/-- Both source (5.8) slice lower bounds and the actual forward shift follow
without a point-core-image or strict-slice hypothesis. -/
theorem three_duad_forward_path_knownSimple
    (hb4 : 4 < replacementDistance h d)
    (hmodel : EightSelection.ThreeDuadMover h e hz hn d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    2 ≤ (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (p.walk.getVert 2)) ∧
      2 ≤ (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical a) ∧
      ∃ z, ∃ q : CriticalPath d.radical (replacementGeometry h d) (p.walk.getVert 2) z,
        (cosetGraph d.radical).dist a' z = 2 ∧
        (∀ i ≤ p.walk.length-2, q.walk.getVert i = p.walk.getVert (i+2)) ∧
        q.walk.getVert (q.walk.length-2) = a' := by
  have hb : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hesc := three_duad_criticalEscape_knownSimple (e := e) (hz := hz) (hn := hn) hb4 hmodel
  exact ⟨critical_forward_slice_index_two_le_of_escape s hc hb hesc p,
    critical_start_slice_index_two_le s hc hb p,
    critical_forward_extension_of_escape s hc hb hesc p⟩

include e hz hn in
/-- An actual backward critical path follows from radius escape, with every
overlapping vertex retained and no strict Baumann-slice premise. -/
theorem three_duad_backward_path_of_radius_knownSimple
    (hb4 : 4 < replacementDistance h d)
    (hmodel : EightSelection.ThreeDuadMover h e hz hn d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    ∃ c t, Adjacent d.radical a t ∧ Adjacent d.radical c t ∧
      ∃ q : CriticalPath d.radical (replacementGeometry h d) c
        (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1=t ∧
        (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2)=p.walk.getVert i) ∧
        2 ≤ (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical c) := by
  have hb : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hd : (cosetGraph d.radical).dist a (p.walk.getVert (p.walk.length-2)) + 2 =
      (replacementGeometry h d).b d.radical := by
    rw [p.dist_start (Nat.sub_le _ _),p.length_eq_b]
    change replacementDistance h d - 2 + 2 = replacementDistance h d
    omega
  obtain ⟨c,hcol,hca,hcrit⟩ := exists_critical_shift d.radical p.start_color hd
    (three_duad_radius_escape_knownSimple (e := e) (hz := hz) (hn := hn) hb4 hmodel p)
  obtain ⟨w,hw⟩ := (cosetGraph_connected d.radical).exists_walk_length_eq_dist c a
  have hwlen : w.length=2 := hw.trans hca
  let t := w.getVert 1
  have hct : Adjacent d.radical c t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      w.adj_getVert_succ (i := 0) (by omega)
  have hat : Adjacent d.radical a t := by
    apply adjacent_symm d.radical
    apply (cosetGraph_adj d.radical _ _).mp
    have hh := w.adj_getVert_succ (i := 1) (by omega)
    simpa only [show 1+1=w.length by omega,SimpleGraph.Walk.getVert_length] using hh
  let q := p.prepend_two (Nat.le_of_lt hb) hcol w hwlen hcrit.2
  have hqt : q.walk.getVert 1=t := by
    simp only [q,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
      hwlen,show 1<2 from by decide,ite_true,t]
  have hover (i : ℕ) (hi : i ≤ p.walk.length-2) :
      q.walk.getVert (i+2)=p.walk.getVert i := p.prepend_two_overlap _ _ _ _ _ hi
  have hqa : q.walk.getVert 2=a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (Nat.zero_le _)
  refine ⟨c,t,hat,hct,q,hqt,hover,?_⟩
  have hh := critical_start_slice_index_two_le s hc hb q
  rwa [hqa] at hh

include e hz hn in
/-- Application to the literal original radical: the replacement edge core
still has index two in its restricted original Sylow, and radius escape gives
a backward path without a strict-slice or mover-comparison premise. -/
theorem original_radical_three_duad_backward_knownSimple
    (hb : 4 < replacementDistance h d)
    (hmodel : EightSelection.ThreeDuadMover h e hz hn d)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z) :
    let T := ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)
    (Q d.radical (beta d.radical)).relIndex T = 2 ∧
      ∃ c t, Adjacent d.radical (alpha d.radical) t ∧ Adjacent d.radical c t ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d) c
          (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1=t ∧
          (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2)=p.walk.getVert i) ∧
          2 ≤ (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
            (U d.radical c) := by
  constructor
  · rw [Q_beta,relIndex_map_map_of_injective _ _ (embedM_injective d.radical)]
    exact (SylowWholeCore.four_lt_original_sylow_eight_image_knownSimple
      (e := e) (hz := hz) (hn := hn) hb).2.2.1
  · exact three_duad_backward_path_of_radius_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hmodel p

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightStrictShift
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
