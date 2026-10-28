module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.ElementarySmallSecondBackward

/-!
# Excluding a small opposite slice for the cube

The existing compatible selection gives two backward critical endpoints and
an incident edge generating with their joined seed actors.  Their first
strict intersections remain compatible because the cubic preserves the
original first-edge core.  The second backward-kernel theorem therefore
contradicts a strict forward slice followed by a small opposite slice.

Source: Meierfrankenfeld--Stellmacher (1993), (5.12)(3), pp.926--927.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation BinaryPermutation
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include e hz hn in
/-- A strict forward cube slice cannot have a small opposite slice. -/
theorem cube_strict_small_opposite_false_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      (D 6).map (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)))
    (hopposite : (B d.radical (p.walk.getVert 2)
      ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical z) ≤ 2) : False := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hfull : d.radical.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  obtain ⟨q,hq,hxN,r,hr1,hr2,_,t,ht,hfirst,hactors⟩ :=
    cube_strict_small_opposite_generation_knownSimple
      (e := e) (hz := hz) (hn := hn) hb u him p hstrict hopposite
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  obtain ⟨q₀,hq₀2⟩ : ∃ q₀ : CriticalPath d.radical (replacementGeometry h d)
      q.start (p.walk.getVert 2), q₀.walk.getVert 2 = a := by
    have hh : ∃ q₀ : CriticalPath d.radical (replacementGeometry h d)
        q.start (p.walk.getVert (p.walk.length-2)), q₀.walk.getVert 2 = a := by
      refine ⟨q.path,?_⟩
      simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using q.overlap 0 (by omega)
    rw [show p.walk.length-2=2 by omega] at hh
    exact hh
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hvt : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have tripleV : Z d.radical q.start ⊓ Z d.radical a ⊓ Z d.radical (p.walk.getVert 2) ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    have hh := cube_strict_compatible_triple_central s hb2 u hfull p.start_color hat hvt
      q.adjacent_start q.adjacent_shift hstrict hq q.first_kernel_generation
    have he : Z d.radical q.start ⊓ Z d.radical a ⊓ Z d.radical (p.walk.getVert 2) =
        Z d.radical (p.walk.getVert 2) ⊓ Z d.radical a ⊓ Z d.radical q.start := by ac_rfl
    rwa [he]
  let x := q.cubic
  have hx : x ∈ stabilizer d.radical a := Ltilde_le_stabilizer _ q.cubic_mem
  have hxa : act d.radical x a = a := hx
  have hxstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (act d.radical x (p.walk.getVert 2))) := by
    have hB := Escape.PairingControl.FirstPairing.B_act
      (geometry := replacementGeometry h d) hb2 x a p.start_color
    rw [hxa] at hB
    rw [hB,U_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hstrict
  have hax : Adjacent d.radical a (act d.radical x (p.walk.getVert 1)) := by
    simpa only [hxa] using (adjacent_act_iff d.radical x _ _).mpr hat
  have hvx : Adjacent d.radical (act d.radical x (p.walk.getVert 2))
      (act d.radical x (p.walk.getVert 1)) := (adjacent_act_iff d.radical x _ _).mpr hvt
  have hQx : Q d.radical (act d.radical x (p.walk.getVert 1)) =
      Q d.radical (p.walk.getVert 1) := by
    rw [Q_act]
    exact mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical))).inv_mem hxN)
  have tripleW : Z d.radical q.start ⊓ Z d.radical a ⊓
      Z d.radical (act d.radical x (p.walk.getVert 2)) ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    have hh := cube_strict_compatible_triple_central s hb2 u hfull p.start_color hax hvx
      q.adjacent_start q.adjacent_shift hxstrict hq
      (by rw [hQx]; exact q.first_kernel_generation)
    have he : Z d.radical q.start ⊓ Z d.radical a ⊓
          Z d.radical (act d.radical x (p.walk.getVert 2)) =
        Z d.radical (act d.radical x (p.walk.getVert 2)) ⊓ Z d.radical a ⊓ Z d.radical q.start := by
      ac_rfl
    rwa [he]
  let k := x⁻¹ * q.transporter
  have hk : k ∈ stabilizer d.radical a := mul_mem (inv_mem hx) q.transporter_mem
  have hkw : act d.radical k (act d.radical x (p.walk.getVert 2)) = q.start := by
    have hcancel (v : Vertex d.radical) : act d.radical x⁻¹ (act d.radical x v) = v := by
      rw [←act_mul,mul_inv_cancel,act_one]
    rw [show k=x⁻¹*q.transporter from rfl,act_mul,hcancel]
    exact q.start_eq
  exact cube_paired_second_backward_strict_false s hc hb u hfull q₀ r hq₀2 hr2
    q.adjacent_start q.adjacent_shift ht hq hfirst hactors
    q.transporter q.transporter_mem q.start_eq k hk hkw tripleV tripleW

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
