module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.TerminalSaturation

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.TerminalKernels
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSmallBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicOmegaGeneration
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadiusNormalizer

/-!
# Distance-six normalization on the original Borel graph

A critical line contained in the next selected seed makes the intersection
of the two seeds normal under the generating stabilizer. Residual control
then puts the entire moving part in that intersection. In the nonnormalizing
branch the full omega layer is its moving part joined to the fixed part,
so the neighboring two-core centralizes the whole seed. Its containment in
the starting core, together with conjugacy and equal orders, identifies the
two cores and their omega layers. This contradicts the strict forward slice.

TerminalSaturation gives exactly the forbidden line containment at distance
six. Thus the endpoint seed normalizes the restricted-kernel join for every
critical distance above four. The existing full-omega comparison extends
normalization to the entire endpoint omega group, and mover comparison puts
the intermediate core in the opposite proper Thompson mover.

All graph vertices, full central attachments and cubic kernels are the
original ones. OriginalSylowExceptional supplies the literal source consumer.
The rest of (5.10), terminal exclusions (5.11)--(5.12), whole-core exhaustion
and reconstruction still require their proofs.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.10), printed pp.922--923.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.GroupTheory Representation.NormalElementaryQuotient
open Theory.SpecificGroups.SymmetricSix
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open scoped IsMulCommutative commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "M" => (L ⊔ R : Subgroup G)
local notation "W₀" => (⁅centralOmega L R,L.subgroupOf M⁆ : Subgroup M)
local notation "π" => CubicAction.projection h e hz hk
local instance : IsElementaryAbelian 2 W₀ := IsElementaryAbelian.of_le (commutator_le_left _ _)

include h e hz hk in
private theorem normal_seed_residual_control {c d : Vertex Rg}
    (q : CriticalPath Rg (sourceGeometry h) c d)
    (N : Subgroup (FreeAmalgam Rg)) (hNG : N ≤ stabilizer Rg c)
    (hNN : stabilizer Rg c ≤ normalizer (N : Set (FreeAmalgam Rg)))
    (hcomm : ⁅Z Rg c,Z Rg d⁆ ≤ N) : U Rg c ≤ N := by
  obtain ⟨i,hi,hir,hiQ,_⟩ := graph_cover h e hz hk c q.start_color
  let D₀ := (Z Rg c).comap i
  let Z₀ := N.comap i
  let A₀ := (Z Rg d).comap i
  have hDm : D₀.map i = Z Rg c :=
    map_comap_eq_self ((Z_le_stabilizer Rg c).trans_eq hir.symm)
  have hZm : Z₀.map i = N := map_comap_eq_self (hNG.trans_eq hir.symm)
  have hAm : A₀.map i = Z Rg d := map_comap_eq_self
    ((critical_Z_le_stabilizer Rg (sourceGeometry h) c q.start_color
      (by rw [(sourceGeometry h).distance_constant _ q.start_color]; exact sourceDistance_pos h)
      q.critical).trans_eq hir.symm)
  have hg (m : (L ⊔ R : Subgroup G)) : i m ∈ stabilizer Rg c := by
    rw [←hir]
    exact ⟨m,rfl⟩
  let : D₀.Normal := ⟨by
    intro z hd m
    change i (m*z*m⁻¹) ∈ Z Rg c
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp ((Z_normalized Rg _) (hg m)) (i z)).mp hd⟩
  let : Z₀.Normal := ⟨by
    intro z hd m
    change i (m*z*m⁻¹) ∈ N
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp (hNN (hg m)) (i z)).mp hd⟩
  have hcomm₀ : ⁅D₀,A₀⁆ ≤ Z₀ := by
    apply (map_le_map_iff_of_injective hi).mp
    rwa [map_commutator,hDm,hAm,hZm]
  have hne : ¬ A₀ ≤ pCore 2 (L ⊔ R : Subgroup G) := by
    intro he
    have hh := map_mono (f := i) he
    rw [hAm,hiQ] at hh
    exact (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
      c q.start_color (by
        rw [(sourceGeometry h).distance_constant _ q.start_color]
        exact sourceDistance_pos h) d q.end_color q.critical).2 hh
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) d q.end_color
  have hAtwo : IsPGroup 2 A₀ :=
    (IsElementaryAbelian.isPGroup 2 (Z Rg d)).comap_of_injective i hi
  have hm := map_mono (f := i)
    (CubicAction.normal_commutator_le_of_escaping_two h e hz D₀ Z₀ A₀ hAtwo hne hcomm₀)
  let j : (L ⊔ R : Subgroup G) →* stabilizer Rg c := i.codRestrict _ hg
  have hjs : Function.Surjective j := by
    intro x
    have hx : (x : FreeAmalgam Rg) ∈ i.range := hir.symm ▸ x.property
    obtain ⟨m,hm⟩ := hx
    exact ⟨m,Subtype.ext hm⟩
  have hj : (stabilizer Rg c).subtype.comp j = i := rfl
  have hLm : (L.subgroupOf (L ⊔ R)).map i = Ltilde Rg c := by
    rw [←h.relative_residual,←hj,←map_map,map_pResidual_of_surjective 2 j hjs]
    rfl
  rwa [map_commutator,hDm,hZm,hLm] at hm

include h e hz hk in
private theorem critical_line_not_le_selected_seed
    (hb : 2 < sourceDistance h)
    {a z c t : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hc : color Rg c = false) (hat : Adjacent Rg a t) (hct : Adjacent Rg c t)
    (hgen : Q Rg t ⊔ Z Rg z = stabilizer Rg a)
    (hsplit : Z Rg a = U Rg a ⊔
      (Z Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))))
    (hXa : X Rg a = Z Rg a) (hXc : X Rg c = Z Rg c)
    (hescape : ¬ U Rg c ≤ B Rg a ((sourceGeometry h).Z_normal _)) :
    ¬ ⁅Z Rg a,Z Rg z⁆ ≤ Z Rg c := by
  intro hline
  let N := Z Rg a ⊓ Z Rg c
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    rw [p.start_color] at hh
    cases he : color Rg t
    · exact (hh he.symm).elim
    · rfl
  have hTa : Q Rg t ≤ stabilizer Rg a := fun _ hx => hx.2 _ (adjacent_symm Rg hat)
  have hTc : Q Rg t ≤ stabilizer Rg c := fun _ hx => hx.2 _ (adjacent_symm Rg hct)
  have hAZ : ⁅Z Rg a,Z Rg z⁆ ≤ N := le_inf (critical_seed_commutator_le h p) hline
  have hNN : stabilizer Rg a ≤ normalizer (N : Set (FreeAmalgam Rg)) := by
    rw [←hgen]
    apply sup_le
    · exact (le_inf (hTa.trans (Z_normalized Rg a))
        (hTc.trans (Z_normalized Rg c))).trans inf_normalizer_le_normalizer_inf
    · exact le_normalizer_iff_commutator_le_left.mpr
        ((commutator_mono inf_le_left le_rfl).trans hAZ)
  have hU : U Rg a ≤ Z Rg c :=
    (normal_seed_residual_control h e hz hk p N
      (inf_le_left.trans (Z_le_stabilizer Rg a)) hNN hAZ).trans inf_le_right
  have hQcG : Q Rg c ≤ stabilizer Rg a := (Q_le_adjacent_h Rg ht hct).trans hTa
  have hQcZ : Q Rg c ≤ centralizer (Z Rg a : Set (FreeAmalgam Rg)) := by
    apply le_centralizer_iff.mp
    rw [hsplit]
    apply sup_le
    · exact hU.trans (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg c hc))
    · exact inf_le_right.trans (centralizer_le hQcG)
  have hQca : Q Rg c ≤ Q Rg a := two_subgroup_seed_centralizer_le_core h e hz p.start_color
    (Q Rg c) (Q_isPGroup Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le c hc)
    (le_inf hQcG hQcZ)
  obtain ⟨g,_,hga⟩ := stabilizer_transitive_neighbors Rg t
    (adjacent_symm Rg hat) (adjacent_symm Rg hct)
  have hcard : Nat.card (Q Rg c) = Nat.card (Q Rg a) := by
    rw [←hga,Q_act,card_map_of_injective (MulAut.conj g⁻¹).injective]
  let := finite_stabilizer Rg a
  let : Finite (Q Rg a) := Finite.of_injective
    (inclusion (show Q Rg a ≤ stabilizer Rg a from fun _ hx => hx.1)) (inclusion_injective _)
  have hQeq : Q Rg c = Q Rg a := eq_of_le_of_card_ge hQca hcard.ge
  have hZeq : Z Rg c = Z Rg a := by rw [←hXc,←hXa,X,X,hQeq]
  apply hescape
  intro x hx
  apply (mem_B_iff Rg a _ ((sourceGeometry h).V_local a p.start_color (by
    rw [(sourceGeometry h).distance_constant a p.start_color]; exact hb)) x).mpr
  have hxZ : x ∈ Z Rg a := hZeq ▸ (DistanceEight.U_le_Z Rg c hx)
  refine ⟨Z_le_VBall Rg a 2 hxZ,?_⟩
  intro l hl
  exact le_normalizer_iff_commutator_le_left.mp
    ((Ltilde_le_stabilizer a).trans (Z_normalized Rg a))
      (by rw [commutator_comm]; exact commutator_mem_commutator hl hxZ)

include h e hz hk in
/-- In the nonnormalizing branch the preceding critical line avoids the
next selected seed. Generation makes their intersection normal; residual
control and the full central splitting would otherwise identify the two
cores and contradict the strict forward slice. -/
theorem borel_three_shift_selected_avoidance
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : BorelBackwardShift (h := h) p) (r : BorelBackwardShift (h := h) q.path)
    (t : BorelBackwardShift (h := h) r.path)
    (hnorm : ¬ Z Rg (q.path.walk.getVert (q.path.walk.length-2)) ≤ normalizer
      (((Z Rg t.start ⊓ Q Rg (r.path.walk.getVert (r.path.walk.length-2))) ⊔
        Z Rg r.start : Subgroup (FreeAmalgam Rg)) : Set _)) :
    ¬ ⁅Z Rg r.start,Z Rg (q.path.walk.getVert (q.path.walk.length-2))⁆ ≤ Z Rg t.start := by
  have hb2 : 2 < sourceDistance h := by omega
  have hsplit := (borel_three_shift_restricted_kernel h e hz hk hb u hR p q r t).2.2.2.2 hnorm |>.2.2
  have hr := hsplit r.start r.path.start_color
  have ht := hsplit t.start t.path.start_color
  have hsplitZ : Z Rg r.start = U Rg r.start ⊔
      (Z Rg r.start ⊓ centralizer (stabilizer Rg r.start : Set (FreeAmalgam Rg))) := by
    rw [←hr.2]
    exact hr.1
  apply critical_line_not_le_selected_seed h e hz hk hb2 r.path t.path.start_color
    t.adjacent_start t.adjacent_shift t.generation hsplitZ hr.2 ht.2
  have hB : (B Rg r.start ((sourceGeometry h).Z_normal _)).map
      (MulAut.conj t.transporter⁻¹).toMonoidHom = B Rg r.start ((sourceGeometry h).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb2 r.start r.path.start_color ((stabilizer Rg r.start).inv_mem t.transporter_mem))
  have hstrict : 2 < (B Rg r.start ((sourceGeometry h).Z_normal _)).relIndex (U Rg t.start) := by
    rw [←t.start_eq,U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj t.transporter⁻¹).injective]
    exact borel_forward_slice_strict_at h e hz hk hb u hR r.path
  intro hle
  have hi := relIndex_eq_one.mpr hle
  omega

include h e hz hk in
/-- The endpoint seed normalizes the restricted-kernel join at every
critical distance above four, including distance six. -/
theorem borel_three_shift_endpoint_normalization
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : BorelBackwardShift (h := h) p) (r : BorelBackwardShift (h := h) q.path)
    (t : BorelBackwardShift (h := h) r.path) :
    let z := q.path.walk.getVert (q.path.walk.length-2)
    let v := r.path.walk.getVert (r.path.walk.length-2)
    let N := (Z Rg t.start ⊓ Q Rg v) ⊔ Z Rg r.start
    Z Rg z ≤ normalizer (N : Set (FreeAmalgam Rg)) ∧
      Q Rg r.start ≤ edgeOffenderJoin t.start t.edge := by
  by_cases hb6 : 6 < sourceDistance h
  · exact (borel_three_shift_normalization h e hz hk hb6 u hR p q r t).2
  have heven := sourceDistance_even h
  rw [Nat.even_iff] at heven
  have heq : sourceDistance h = 6 := by omega
  have hnorm : Z Rg (q.path.walk.getVert (q.path.walk.length-2)) ≤ normalizer
      (((Z Rg t.start ⊓ Q Rg (r.path.walk.getVert (r.path.walk.length-2))) ⊔
        Z Rg r.start : Subgroup (FreeAmalgam Rg)) : Set _) := by
    by_contra hn
    exact borel_three_shift_selected_avoidance h e hz hk hb u hR p q r t hn
      (borel_six_attachment_saturated h e hz hk heq u hR p q r t hn).2
  exact ⟨hnorm,(borel_three_shift_mover_comparison h e hz hk hb u hR p q r t).2 hnorm |>.1⟩

include h e hz hk in
/-- The whole endpoint omega group normalizes the restricted-kernel join
above distance four, including its component-fixed central factor. -/
theorem borel_three_shift_omega_normalization
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : BorelBackwardShift (h := h) p) (r : BorelBackwardShift (h := h) q.path)
    (t : BorelBackwardShift (h := h) r.path) :
    let z := q.path.walk.getVert (q.path.walk.length-2)
    let v := r.path.walk.getVert (r.path.walk.length-2)
    X Rg z ≤ normalizer (((Z Rg t.start ⊓ Q Rg v) ⊔ Z Rg r.start :
      Subgroup (FreeAmalgam Rg)) : Set _) := by
  let z := q.path.walk.getVert (q.path.walk.length-2)
  let v := r.path.walk.getVert (r.path.walk.length-2)
  let K := Z Rg t.start ⊓ Q Rg v
  let N := K ⊔ Z Rg r.start
  have hb4 : 4 < sourceDistance h := by omega
  have hb2 : 2 < sourceDistance h := by omega
  have hnorm := (borel_three_shift_endpoint_normalization h e hz hk hb u hR p q r t).1
  have hNK := (borel_three_shift_restricted_kernel h e hz hk hb4 u hR p q r t).2.2.2.1
  have hr := two_borel_backward_shifts_small_moving h e hz hk hb4 p q r
  let pr : CriticalPath Rg (sourceGeometry h) z r.start :=
    CriticalPath.ofPair r.path.end_color (reverse_pair h e r.path)
  have hs : (Q Rg r.start).relIndex (Z Rg z) < 4 := by rw [hr.2.2.1]; decide
  rcases small_critical_omega_generation_or_control_at h e hz hk pr hs with hgen | hc
  · have heq := omega_eq_seed_of_central_generation h z r.path.end_color hgen
    change X Rg z ≤ normalizer (N : Set (FreeAmalgam Rg))
    rw [heq]
    exact hnorm
  · have hKG : K ≤ stabilizer Rg z := inf_le_right.trans (terminal_last_edge_inputs h r.path hb2).2.2
    have hKQ : K ≤ Q Rg r.start :=
      (inf_le_left.trans (terminal_neighbor_seed_radius t.adjacent_start t.adjacent_shift)).trans
        ((sourceGeometry h).V_le_Q hb2 r.start r.path.start_color)
    have hXN : X Rg z ≤ normalizer (Z Rg r.start : Set (FreeAmalgam Rg)) :=
      (critical_X_le_vertex h e z r.path.end_color r.start pr.critical).trans
        (Z_normalized Rg r.start)
    have hRZ : ⁅X Rg z,Z Rg r.start⁆ ≤ Z Rg r.start := le_normalizer_iff_commutator_le_right.mp hXN
    have hKR : K ≤ centralizer ((⁅X Rg z,Z Rg r.start⁆ :
        Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) :=
      (hKQ.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q Rg r.start r.path.start_color)))).trans (centralizer_le hRZ)
    have hbound : ⁅X Rg z,K⁆ ≤ N := by
      rw [commutator_comm]
      exact (hc K hKG hKR).trans (sup_le (hRZ.trans le_sup_right)
        ((le_normalizer_iff_commutator_le_left.mp hNK).trans le_sup_left))
    change X Rg z ≤ normalizer (N : Set (FreeAmalgam Rg))
    apply le_normalizer_iff.mpr
    intro x hx y hy
    have hm : N.map (MulAut.conj x).toMonoidHom ≤ N := by
      rw [show N = K ⊔ Z Rg r.start from rfl,Subgroup.map_sup]
      refine sup_le ?_ ((mem_normalizer_iff_map_conj_eq.mp (hXN hx)).le.trans le_sup_right)
      rintro _ ⟨k,hkK,rfl⟩
      have hh := N.mul_mem (hbound (commutator_mem_commutator hx hkK)) (mem_sup_left hkK)
      simpa [MulAut.conj_apply,commutatorElement_def,mul_assoc] using hh
    exact hm (mem_map_of_mem (MulAut.conj x).toMonoidHom hy)

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
