module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicOrbitKernelControl

/-!
# Strict eligible slices for the original cubic cover

Above distance four, a small eligible forward slice is impossible in the
small-critical-image, full point-core branch. The full reverse-kernel
commutator R₃ is realized by one conjugated seed. Conjugating its actor back
to the shifted center makes the whole shifted span's displacement lie in
that center's full seed. The span is normal there and escapes its Baumann
slice, so the actor must lie in the local two-core. It then centralizes the
seed, contradicting the nontrivial R₃ witness.

This uses the checked equality between R₃ and the full old-endpoint core
commutator to control the entire span orbit. It proves the strict slice
directly, without needing the source's intervening Thompson case split.
Both full covers, the original cubic kernel, and the literal graph maps
are retained. The estimate transports to any critical walk and discharges
the strict-index premise of the actual small-image backward shift.

The whole-core and literal C.1.32 consumers retain the other radical-image,
ineligible-slice, large-image and exact-four cases. R4/R6, the terminal
MS93 (5.11)--(5.12) exclusions, natural exhaustion and both unconditional
reconstruction outcomes remain necessary.

Source: Meierfrankenfeld--Stellmacher (1993), (3.3)(ii), pp.866--867,
(5.7), p.919, and the strict-slice argument (5.9), pp.920--922.
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
namespace SmallSliceShift
variable {a' : Vertex (edge L R)}
  {p : CriticalPath (edge L R) (sourceGeometry h) (alpha (edge L R)) a'}
  (s : SmallSliceShift h p)

include s e hz hk in
theorem small_slice_impossible
    (hb : 4 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map (CubicAction.projection h e hz hk) ≤
      pointCore.map (MulAut.conj u).toMonoidHom)
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (heligible : ¬ U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)) :
    False := by
  let c := p.walk.getVert 2
  have hb2 : 2 < sourceDistance h := by omega
  have hcard := (s.orbitDisplacement_full_core e hz hk hb u hR hsmall hslice heligible).2.1
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
    exact (commutator_mono (hspan.trans le_sup_right) le_rfl).trans_eq
      (s.full_orbit_kernel_commutator e hz hk hb u hR hsmall hslice heligible).1
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

end SmallSliceShift

include e hz hk in
/-- Above distance four an eligible small-image forward slice is strict.
The full point-core marking supplies the actual shifted critical path. -/
theorem full_point_small_forward_slice_gt_two
    (hb : 4 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map (CubicAction.projection h e hz hk) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4)
    (heligible : ¬ U Rg (p.walk.getVert 2) ≤
      B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)) :
    2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) := by
  by_contra! hslice
  obtain ⟨s⟩ := exists_small_slice_shift h e hz hk (by omega) u hfull p
    hsmall hslice heligible
  exact s.small_slice_impossible e hz hk hb u hfull.le hsmall hslice heligible

include e hz hk in
/-- The strict small-image slice estimate on any actual critical walk,
transporting its second vertex and Baumann slice by the same element. -/
theorem full_point_small_forward_slice_gt_two_at
    (hb : 4 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map (CubicAction.projection h e hz hk) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (hsmall : (Q Rg a').relIndex (Z Rg a) < 4)
    (heligible : ¬ U Rg (p.walk.getVert 2) ≤ B Rg a ((sourceGeometry h).Z_normal _)) :
    2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color Rg p.start_color
  have hbase : act Rg g⁻¹ a = alpha Rg := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have hpact : ∃ p₀ : CriticalPath Rg (sourceGeometry h)
      (act Rg g⁻¹ a) (act Rg g⁻¹ a'),
      p₀.walk.getVert 2 = act Rg g⁻¹ (p.walk.getVert 2) :=
    ⟨p.act g⁻¹,by simp only [CriticalPath.act,actWalk_getVert]⟩
  rw [hbase] at hpact
  obtain ⟨p₀,hvert⟩ := hpact
  have hsmall₀ : (Q Rg (act Rg g⁻¹ a')).relIndex (Z Rg (alpha Rg)) < 4 := by
    rw [←hbase,Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹⁻¹).injective]
    exact hsmall
  have hB := Escape.PairingControl.FirstPairing.B_act
    (geometry := sourceGeometry h) (by change 2 < sourceDistance h; omega) g⁻¹ a p.start_color
  rw [hbase,inv_inv] at hB
  have hel₀ : ¬ U Rg (p₀.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) := by
    rw [hvert,U_act,inv_inv,hB]
    exact fun hh => heligible
      ((map_le_map_iff_of_injective (MulAut.conj g).injective).mp hh)
  have hi := full_point_small_forward_slice_gt_two e hz hk hb u hfull p₀ hsmall₀ hel₀
  rw [hvert,U_act,inv_inv,hB,relIndex_map_map_of_injective _ _ (MulAut.conj g).injective] at hi
  exact hi

include e hz hk in
/-- The strict bound now discharges the slice premise of the actual
small-image backward shift. The selected second vertex, transported first
edge and complete overlap all use the same original cubic graph. -/
theorem full_point_small_backward_shift_of_forward_eligibility
    (hb : 4 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map (CubicAction.projection h e hz hk) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4)
    (heligible : ¬ U Rg (p.walk.getVert 2) ≤
      B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)) :
    2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ∧
    ∃ t, Adjacent Rg (alpha Rg) t ∧
      Q Rg t ⊔ Z Rg a' = stabilizer Rg (alpha Rg) ∧
      ∃ g ∈ stabilizer Rg (alpha Rg),
        act Rg g (p.walk.getVert 1) = t ∧
        ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g (p.walk.getVert 2))
          (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = t ∧
          (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
          2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
            (U Rg (act Rg g (p.walk.getVert 2))) := by
  have hi := full_point_small_forward_slice_gt_two e hz hk hb u hfull p hsmall heligible
  have hct : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) := by
    apply adjacent_symm Rg
    apply (cosetGraph_adj Rg _ _).mp
    exact p.walk.adj_getVert_succ (i := 1) (by
      have hl : p.walk.length = sourceDistance h := p.length_eq_b
      omega)
  exact ⟨hi,small_full_point_backward_shift h e hz hk u hfull p hsmall hct hi⟩

omit hk in
include h e hz in
/-- Whole-core application of the strict small-image slice bound and its
actual backward path. Both full covers and the original odd kernel remain. -/
theorem coreExhaustion_or_cubic_strict_small_shifts :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false → Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∀ (u : Equiv.Perm (Fin 6)),
        (Rg).map (CubicAction.projection h e hz hk) = pointCore.map (MulAut.conj u).toMonoidHom →
        4 < sourceDistance h →
        ∀ (a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a'),
          (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4 →
          ¬ U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) →
          2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
            (U Rg (p.walk.getVert 2)) ∧
          ∃ t, Adjacent Rg (alpha Rg) t ∧
            Q Rg t ⊔ Z Rg a' = stabilizer Rg (alpha Rg) ∧
            ∃ g ∈ stabilizer Rg (alpha Rg),
              act Rg g (p.walk.getVert 1) = t ∧
              ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g (p.walk.getVert 2))
                (p.walk.getVert (p.walk.length-2)),
                q.walk.getVert 1 = t ∧
                (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
                2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
                  (U Rg (act Rg g (p.walk.getVert 2))) := by
  rcases CubicEven.coreExhaustion_or_cubic_fullSymmetric h e hz with hx | ⟨hk,hs,hb⟩
  · exact Or.inl hx
  · exact Or.inr ⟨hk,hs,hb,graph_U_card h e hz hk,fun u hu hb4 a' p hp hel =>
      full_point_small_backward_shift_of_forward_eligibility e hz hk hb4 u hu p hp hel⟩

omit hk in
include h e hz in
/-- Literal C.1.32 consumer of the proved strict small-image slice and
backward shift. The remaining source cases and full reconstruction stay open. -/
theorem rankTwo_or_cubic_strict_small_shifts :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false → Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∀ (u : Equiv.Perm (Fin 6)),
        (Rg).map (CubicAction.projection h e hz hk) = pointCore.map (MulAut.conj u).toMonoidHom →
        4 < sourceDistance h →
        ∀ (a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a'),
          (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4 →
          ¬ U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) →
          2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
            (U Rg (p.walk.getVert 2)) ∧
          ∃ t, Adjacent Rg (alpha Rg) t ∧
            Q Rg t ⊔ Z Rg a' = stabilizer Rg (alpha Rg) ∧
            ∃ g ∈ stabilizer Rg (alpha Rg),
              act Rg g (p.walk.getVert 1) = t ∧
              ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g (p.walk.getVert 2))
                (p.walk.getVert (p.walk.length-2)),
                q.walk.getVert 1 = t ∧
                (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
                2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
                  (U Rg (act Rg g (p.walk.getVert 2))) :=
  (coreExhaustion_or_cubic_strict_small_shifts e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
