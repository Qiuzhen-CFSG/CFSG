module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneSliceOrbit
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneSpanControl
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneSpanCollapse
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneKernelChoice
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicOrbitKernelControl
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSliceShift

/-!
# Stabilization of the actual plane small-slice span

A conjugate of the shifted seed realizes the same nonzero full reverse-kernel
line R₃. The escaping local span forces its larger predecessor-kernel
commutator to have order four. Aligned-line uniqueness then gives the endpoint
comparison for the entire span orbit. Its line centralizer and the actual
endpoint generate the midpoint stabilizer, so that comparison normalizes the
orbit. Whole-stabilizer section control and nilpotent saturation collapse it
to the original shifted span.

This is a source consumer with only the original plane, distance and small
slice hypotheses. The orbit invariance and comparison required by the earlier
algebraic collapse are conclusions here. Both full covers and the original
cubic extension kernel are retained throughout. The final strict-slice
contradiction is a separate consumer.

Source: Meierfrankenfeld--Stellmacher (1993), (5.9), printed pp.921--922.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped commutatorElement IsMulCommutative Pointwise
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk
namespace SmallSliceShift
variable {a' : Vertex (edge L R)}
  {p : CriticalPath (edge L R) (sourceGeometry h) (alpha (edge L R)) a'}
  (s : SmallSliceShift h p)

include e hz hk in
/-- The actual entire span orbit collapses to its original shifted span and
is normalized by the whole midpoint stabilizer. No orbit-control input remains. -/
theorem plane_spanOrbit_stabilizes
    (hb : 4 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2) :
    s.spanOrbit = s.span ∧ stabilizer Rg (p.walk.getVert 2) ≤
      normalizer (s.spanOrbit : Set (FreeAmalgam Rg)) := by
  have hb2 : 2 < sourceDistance h := by omega
  have hel := (plane_critical_paths h e hz hk u hR p).2.2.2
  have hs : (Q Rg s.endpoint).relIndex (Z Rg (p.walk.getVert 2)) < 4 := by
    rw [(s.shifted_indices e hz hk hb hsmall hslice hel).1]
    decide
  have ho := s.centralizer_orbits_le_old_endpoint_core e hz hk hb hsmall hslice hel
  have hd := s.plane_orbitDisplacement_alignment e hz hk hb u hR hsmall hslice
  obtain ⟨x,hx,hline⟩ := s.exists_seed_conjugate_orbitDisplacement hd.1
  let f := (MulAut.conj x).toMonoidHom
  let c := p.walk.getVert 2
  let t := s.path.walk.getVert (s.path.walk.length-1)
  have hZxD : (Z Rg s.centerVertex).map f ≤ s.seedOrbit := by
    rw [seedOrbit,conjugateSpanBy_eq_iSup_conj]
    exact le_iSup (fun k : s.lineCentralizer => (Z Rg s.centerVertex).map
      (MulAut.conj (k : FreeAmalgam Rg)).toMonoidHom) ⟨x,hx⟩
  have hYxW : s.span.map f ≤ s.spanOrbit := by
    rw [spanOrbit,conjugateSpanBy_eq_iSup_conj]
    exact le_iSup (fun k : s.lineCentralizer => s.span.map
      (MulAut.conj (k : FreeAmalgam Rg)).toMonoidHom) ⟨x,hx⟩
  have hl : s.path.walk.length = sourceDistance h := s.path.length_eq_b
  have hpre : s.path.walk.getVert (s.path.walk.length-2) = a' := by
    have hp : p.walk.length = sourceDistance h := p.length_eq_b
    rw [show s.path.walk.length-2=p.walk.length-2 by omega,
      s.overlap _ (Nat.le_refl _),show p.walk.length-2+2=p.walk.length by omega,
      p.walk.getVert_length]
  have hca : (cosetGraph Rg).dist c s.centerVertex = 2 := by
    rw [SimpleGraph.dist_comm]
    exact s.center_distance hb2
  have hYV : s.span ≤ V Rg s.centerVertex := s.span_le_radius hb2
  have hYN : stabilizer Rg s.centerVertex ≤ normalizer (s.span : Set (FreeAmalgam Rg)) :=
    localZSpan_normalized Rg c s.centerVertex
  have hYB := s.span_not_le_slice hb2 hel
  have hsaturated := plane_predecessor_kernel_saturated h e hz hk hb2 u hR.le
    s.path hs s.center_color hca.le s.span hYV hYN hYB x hx.1
    (by rw [hpre]; exact hZxD.trans ho.1)
    (by rw [hpre]; exact hYxW.trans ho.2)
    (by change Nat.card (⁅(Z Rg s.centerVertex).map f,s.orbitKernel⁆ :
          Subgroup (FreeAmalgam Rg)) = 2
        rw [hline]
        exact hd.1)
  have hWnot : ¬ ⁅s.spanOrbit,s.orbitKernel⁆ ≤ s.orbitDisplacement := by
    intro hh
    apply hsaturated.2.1
    change ⁅s.span.map f,s.orbitKernel⁆ ≤ ⁅(Z Rg s.centerVertex).map f,s.orbitKernel⁆
    rw [hline]
    exact (commutator_mono hYxW le_rfl).trans hh
  have hzt : Adjacent Rg s.endpoint t := by
    have hh := s.path.walk.adj_getVert_succ (i := s.path.walk.length-1) (by omega)
    rw [show s.path.walk.length-1+1=s.path.walk.length by omega,
      s.path.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hzt
    rw [s.path.end_color] at hh
    cases he : color Rg t <;> simp_all
  have hpred : Q Rg a' ≤ Q Rg t := by
    rw [←hpre]
    apply Q_le_adjacent_h Rg ht
    have hh := s.path.walk.adj_getVert_succ (i := s.path.walk.length-2) (by omega)
    rw [show s.path.walk.length-2+1=s.path.walk.length-1 by omega] at hh
    exact (cosetGraph_adj Rg _ _).mp hh
  have hZt : Z Rg c ≤ Q Rg t := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ s.path.start_color)
    rw [(sourceGeometry h).distance_constant _ s.path.start_color,
      s.path.dist_start (Nat.sub_le _ _)]
    change s.path.walk.length-1 < sourceDistance h
    omega
  have hnon : ⁅(Z Rg s.centerVertex).map f,s.orbitKernel⁆ ≠ ⊥ := by
    rw [hline]
    intro hh
    have hc := hd.1
    rw [hh,card_bot] at hc
    omega
  have halign : ⁅(Z Rg s.centerVertex).map f,s.orbitKernel⁆ ≤
      ⁅Z Rg c,Z Rg s.endpoint⁆ ⊔
        (stabilizer Rg s.endpoint ⊓ centralizer
          (stabilizer Rg s.endpoint : Set (FreeAmalgam Rg))) := by
    rw [hline]
    exact le_sup_left.trans_eq hd.2.2.2.2.2
  have hcontrol := plane_edge_control_of_kernel_escape h e hz hk u hR s.path hs
    hzt hZt ((Z Rg s.centerVertex).map f) s.spanOrbit
    ((hZxD.trans ho.1).trans hpred) (ho.2.trans hpred) hnon halign (by
      change ¬ ⁅s.spanOrbit,s.orbitKernel⁆ ≤ ⁅(Z Rg s.centerVertex).map f,s.orbitKernel⁆
      rw [hline]
      exact hWnot)
  have hZcY : Z Rg c ≤ s.span := Z_le_localZSpan Rg c s.centerVertex
  have hZcW : Z Rg c ≤ s.spanOrbit := hZcY.trans (le_conjugateSpanBy _ _)
  have hZG : Z Rg s.endpoint ≤ stabilizer Rg c :=
    critical_Z_le_stabilizer Rg (sourceGeometry h) c s.path.start_color
      (by rw [(sourceGeometry h).distance_constant _ s.path.start_color]
          exact sourceDistance_pos h) s.path.critical
  have hcrit : ⁅Z Rg c,Z Rg s.endpoint⁆ ≤ Z Rg c :=
    le_normalizer_iff_commutator_le_left.mp (hZG.trans (Z_normalized Rg c))
  have hWN : stabilizer Rg c ≤ normalizer (s.spanOrbit : Set (FreeAmalgam Rg)) := by
    rw [←s.centralizer_orbits_normalized.2.2]
    refine sup_le s.centralizer_orbits_normalized.2.1 ?_
    apply le_normalizer_iff_commutator_le_left.mpr
    exact hcontrol.trans (sup_le
      (le_normalizer_iff_commutator_le_left.mp
        ((inf_le_right.trans (s.second_core_le_lineCentralizer hb2)).trans
          s.centralizer_orbits_normalized.2.1))
      (hcrit.trans hZcW))
  refine ⟨?_,hWN⟩
  exact cubic_small_critical_span_collapse h e hz hk hb s.path hs s.center_color hca.le
    s.span s.lineCentralizer hYV hYN hZcY inf_le_left hWN hcontrol

end SmallSliceShift
end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
