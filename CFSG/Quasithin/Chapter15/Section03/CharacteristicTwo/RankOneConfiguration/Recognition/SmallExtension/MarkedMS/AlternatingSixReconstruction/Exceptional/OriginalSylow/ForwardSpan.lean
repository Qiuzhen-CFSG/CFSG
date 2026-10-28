module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.ForwardCollapse
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicOrbitKernelControl

/-!
# The whole span orbit and the order-two Borel displacement

The full span orbit normalizes the entire reverse critical kernel: it
lies in both the second two-core and the old endpoint two-core. It also
normalizes the seed orbit, so it fixes their order-two commutator R₃.

The span orbit's own kernel displacement cannot be contained in R₃.
Conjugate a seed realizing R₃ back to the shifted center. Such containment
would control the whole normal span modulo that center's seed, forcing
the span into its Baumann slice unless the actor belongs to the two-core.
That core alternative fixes the seed and contradicts the chosen nonzero
commutator. Thus joining the two orbits strictly increases displacement
beyond order two.

These facts preserve the original Borel, both full moving covers, and the
odd cubic kernel quotient. They distinguish the seed orbit Z from the
whole span orbit W in MS93 (5.9), printed pp.921--922. The point-core
whole-orbit bound cannot be reused here. Full-stabilizer centrality of R₃,
the source orbit-stabilization argument, strict forward slices and terminal
exclusions are still needed for the exceptional reconstruction.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
open AlternatingSixReconstruction.Exceptional.OriginalSylow
namespace SmallSliceShift
variable {a' : Vertex (edge L R)}
  {p : CriticalPath (edge L R) (sourceGeometry h) (alpha (edge L R)) a'}
  (s : SmallSliceShift h p)

include e hz hk in
/-- The whole shifted span orbit cannot have its reverse-kernel displacement
contained in R₃. Conjugating the actual seed witness back to its center
would put the entire span in the Baumann slice. -/
theorem borel_spanOrbit_displacement_not_le
    (hb : 4 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map (CubicAction.projection h e hz hk) =
      Theory.SpecificGroups.SymmetricSix.borel.map (MulAut.conj u).toMonoidHom)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2) :
    ¬ ⁅s.spanOrbit,s.orbitKernel⁆ ≤ s.orbitDisplacement := by
  intro hcontrol
  let c := p.walk.getVert 2
  have hb2 : 2 < sourceDistance h := by omega
  have heligible := (borel_critical_paths h e hz hk u hR p).2.2.2
  have hcard := s.borel_orbit_displacement_card_two e hz hk hb u hR hslice
  obtain ⟨t,ht,hwitness⟩ := s.exists_seed_conjugate_orbitDisplacement hcard
  let f := (MulAut.conj t).toMonoidHom
  let fi := (MulAut.conj t⁻¹).toMonoidHom
  let A := s.orbitKernel.map fi
  have hAf : A.map f = s.orbitKernel := by
    rw [map_map]
    have he : f.comp fi = MonoidHom.id (FreeAmalgam Rg) := by
      apply MonoidHom.ext
      intro x
      change t*(t⁻¹*x*(t⁻¹)⁻¹)*t⁻¹ = x
      group
    rw [he,map_id]
  have hAQ : A ≤ Q Rg c := by
    have hQ := mem_normalizer_iff_map_conj_eq.mp
      ((Q_normalized Rg c) ((stabilizer Rg c).inv_mem ht.1))
    exact (map_mono (show s.orbitKernel ≤ Q Rg c from inf_le_right)).trans_eq hQ
  have hdist : (cosetGraph Rg).dist c s.centerVertex = 2 := by
    have hh := dist_act Rg s.conjugator⁻¹ c (alpha Rg)
    rw [s.fixes_second,SimpleGraph.dist_comm (u := c) (v := alpha Rg)] at hh
    exact hh.trans (p.dist_start (by
      have hl : p.walk.length = sourceDistance h := p.length_eq_b
      omega))
  have hAG : A ≤ stabilizer Rg s.centerVertex := hAQ.trans
    (Q_le_stabilizer_of_dist_le_two c s.centerVertex s.path.start_color
      s.center_color hdist.le)
  have hZA : ⁅Z Rg s.centerVertex,A⁆ ≤ Z Rg s.centerVertex :=
    le_normalizer_iff_commutator_le_left.mp (hAG.trans (Z_normalized Rg _))
  have hZAmap : (⁅Z Rg s.centerVertex,A⁆ : Subgroup (FreeAmalgam Rg)).map f =
      s.orbitDisplacement := by
    rw [map_commutator,hAf]
    exact hwitness
  have hspan : s.span.map f ≤ s.spanOrbit := by
    rw [spanOrbit,conjugateSpanBy_eq_iSup_conj]
    exact le_iSup (fun x : s.lineCentralizer =>
      s.span.map (MulAut.conj (x : FreeAmalgam Rg)).toMonoidHom) ⟨t,ht⟩
  have hcomm : ⁅s.span,A⁆ ≤ Z Rg s.centerVertex := by
    apply le_trans _ hZA
    apply (map_le_map_iff_of_injective (f := f) (MulAut.conj t).injective).mp
    rw [hZAmap,map_commutator,hAf]
    exact (commutator_mono hspan le_rfl).trans hcontrol
  have hAcore : A ≤ Q Rg s.centerVertex := by
    by_contra hn
    have hAB := normalized_radius_le_slice_of_controlled_actor h e hz hb2
      s.center_color s.span A (localZSpan_le_V Rg hdist.le)
      (localZSpan_normalized Rg _ _) hAG
      ((Q_isPGroup Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le c
        s.path.start_color).to_le hAQ) hn hcomm
    exact s.span_not_le_slice hb2 heligible hAB
  have hzero : ⁅Z Rg s.centerVertex,A⁆ = ⊥ := le_bot_iff.mp
    ((commutator_mono le_rfl hAcore).trans_eq
      (Z_centralizes_Q Rg s.centerVertex s.center_color))
  rw [hzero,Subgroup.map_bot] at hZAmap
  rw [←hZAmap] at hcard
  simp at hcard

include e hz hk in
/-- The span orbit normalizes the full reverse kernel. It also fixes R₃:
its second-core containment makes it normalize the seed orbit, and the
commutator has order two. This does not assert full-stabilizer centrality. -/
theorem borel_spanOrbit_kernel_normalizes_and_line_fixed
    (hb : 4 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map (CubicAction.projection h e hz hk) =
      Theory.SpecificGroups.SymmetricSix.borel.map (MulAut.conj u).toMonoidHom)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2) :
    s.spanOrbit ≤ normalizer (s.orbitKernel : Set (FreeAmalgam Rg)) ∧
      s.orbitDisplacement ≤ centralizer (s.spanOrbit : Set (FreeAmalgam Rg)) := by
  have hb2 : 2 < sourceDistance h := by omega
  have hel := (borel_critical_paths h e hz hk u hR p).2.2.2
  have ho := s.borel_centralizer_orbits_le_old_endpoint_core e hz hk hb u hR hslice hel
  have hWQ := s.spanOrbit_le_second_core e hz hb
  have hWG : s.spanOrbit ≤ stabilizer Rg (p.walk.getVert 2) := hWQ.trans (fun _ hx => hx.1)
  have hWN : s.spanOrbit ≤ normalizer (s.orbitKernel : Set (FreeAmalgam Rg)) :=
    (le_inf ((ho.2.trans (s.old_core_le_endpoint_stabilizer hb2)).trans (Z_normalized Rg _))
      (hWG.trans (Q_normalized Rg _))).trans inf_normalizer_le_normalizer_inf
  have hWD : s.spanOrbit ≤ normalizer (s.seedOrbit : Set (FreeAmalgam Rg)) :=
    (hWQ.trans (s.second_core_le_lineCentralizer hb2)).trans s.centralizer_orbits_normalized.1
  have hWR : s.spanOrbit ≤ normalizer (s.orbitDisplacement : Set (FreeAmalgam Rg)) := by
    intro x hx
    rw [mem_normalizer_iff_map_conj_eq]
    change (⁅s.seedOrbit,s.orbitKernel⁆ : Subgroup (FreeAmalgam Rg)).map _ = _
    rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp (hWD hx),
      mem_normalizer_iff_map_conj_eq.mp (hWN hx)]
    rfl
  exact ⟨hWN,le_centralizer_iff.mp (hWR.trans
    (normalizer_le_centralizer_of_card_two _
      (s.borel_orbit_displacement_card_two e hz hk hb u hR hslice)))⟩

include e hz hk in
/-- Joining the seed and whole-span orbits strictly increases the full
reverse-kernel displacement beyond the order-two subgroup R₃. Both
orbits remain in the same second two-core. -/
theorem borel_combined_orbit_displacement_gt_two
    (hb : 4 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map (CubicAction.projection h e hz hk) =
      Theory.SpecificGroups.SymmetricSix.borel.map (MulAut.conj u).toMonoidHom)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2) :
    s.orbitDisplacement < ⁅s.seedOrbit ⊔ s.spanOrbit,s.orbitKernel⁆ ∧
      2 < Nat.card (⁅s.seedOrbit ⊔ s.spanOrbit,s.orbitKernel⁆ : Subgroup (FreeAmalgam Rg)) := by
  let T := ⁅s.seedOrbit ⊔ s.spanOrbit,s.orbitKernel⁆
  have hRT : s.orbitDisplacement ≤ T := commutator_mono le_sup_left le_rfl
  have hnot : ¬ T ≤ s.orbitDisplacement := by
    intro he
    exact s.borel_spanOrbit_displacement_not_le e hz hk hb u hR hslice
      ((commutator_mono le_sup_right le_rfl).trans he)
  have hb2 : 2 < sourceDistance h := by omega
  have hDQ : s.seedOrbit ⊔ s.spanOrbit ≤ Q Rg (p.walk.getVert 2) := sup_le
    ((s.seedOrbit_radius_and_escape e hz hb2).1.trans
      ((sourceGeometry h).V_le_Q hb2 _ s.path.start_color))
    (s.spanOrbit_le_second_core e hz hb)
  have hTQ : T ≤ Q Rg (p.walk.getVert 2) :=
    (Subgroup.commutator_le_sup _ _).trans (sup_le hDQ inf_le_right)
  let := finite_stabilizer Rg (p.walk.getVert 2)
  let : Finite T := Finite.of_injective (inclusion (hTQ.trans (fun _ hx => hx.1)))
    (inclusion_injective _)
  have hcard := s.borel_orbit_displacement_card_two e hz hk hb u hR hslice
  refine ⟨lt_of_le_not_ge hRT hnot,?_⟩
  change 2 < Nat.card T
  by_contra! hh
  exact hnot (eq_of_le_of_card_ge hRT (by omega)).ge


end SmallSliceShift
end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
