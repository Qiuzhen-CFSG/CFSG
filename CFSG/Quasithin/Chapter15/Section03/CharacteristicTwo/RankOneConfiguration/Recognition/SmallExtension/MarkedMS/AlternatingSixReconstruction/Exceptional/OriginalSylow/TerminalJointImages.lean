module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.TerminalReverseKernels
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicKernelTransport
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSmallBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneNormalizer

/-!
# Joint reverse images in the terminal original Borel configuration

A fourth compatible backward shift supplies the reverse core containment
on the preceding edge. The proof transports the already established core
containment by the actual edge transporter. For distinct proper Thompson
movers, the two neighboring cores therefore lie in their intersection,
whose relative index over either core is four.

Both reverse selected seeds lie in the same neighboring core, by their
literal path overlaps. Their joint image has order two or four. In the
order-two case, centralizing supplements identify their whole-seed
commutators and their full critical kernels. In the order-four case, the
joint image fills the core product modulo the starting core, so its
commutator equals the entire neighboring-core movement. Quadratic action
on the full seed identifies that commutator with the join of the two
individual commutators.

All paths, switches, full-omega normalizers and central attachments are
retained. The cubic projection still has kernel E, including E/Q of odd
order; no quotient kernel is replaced by Q. The original c.L,d.S consumer
is in OriginalSylowExceptional. Excluding these two joint-image cases,
mover equality, the terminal distance contradictions and CoreExhaustion
remain necessary for the complete exceptional reconstruction.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.5)(c) and (5.10), printed pp.916--917 and 923.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags Theory.SpecificGroups.SymmetricSix
open Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

include h e hz hk in
/-- A fourth compatible shift supplies the reverse core containment on
its preceding edge, using the literal edge transporter. -/
theorem borel_four_shift_mutual_cores
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : BorelBackwardShift (h := h) p) (r : BorelBackwardShift (h := h) q.path)
    (t : BorelBackwardShift (h := h) r.path) (s : BorelBackwardShift (h := h) t.path)
    (hse : act Rg s.transporter (t.path.walk.getVert 1) = s.edge) :
    Q Rg r.start ≤ edgeOffenderJoin t.start t.edge ∧
    Q Rg t.start ≤ edgeOffenderJoin r.start t.edge := by
  refine ⟨(borel_three_shift_endpoint_normalization h e hz hk hb u hR p q r t).2,?_⟩
  have hc := (borel_three_shift_endpoint_normalization h e hz hk hb u hR q.path r t s).2
  have ht2 : t.path.walk.getVert 2 = r.start := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using t.overlap 0 (Nat.zero_le _)
  have hsr : act Rg s.transporter r.start = s.start := by
    simpa only [ht2] using s.start_eq
  have hst : act Rg s.transporter t.edge = s.edge := by simpa only [t.first] using hse
  have hm := remaining_edge_join_act h e hz hk u (Or.inr hR)
    r.path.start_color t.adjacent_start s.transporter
  rw [hsr,hst] at hm
  have hQ : (Q Rg t.start).map (MulAut.conj s.transporter⁻¹).toMonoidHom = Q Rg t.start := by
    rw [←Q_act,show act Rg s.transporter t.start = t.start from s.transporter_mem]
  rw [hm,←hQ] at hc
  exact (map_le_map_iff_of_injective (MulAut.conj _).injective).mp hc

include h e hz hk in
/-- Mutually contained cores on a distinct-mover Borel edge have joint
index at most four over either core. These are relative indices on the
original graph, with no replacement of the cubic kernel by the two-core. -/
theorem borel_mutual_core_product_index
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a c d : Vertex Rg} (ha : color Rg a = false) (hc : color Rg c = false)
    (had : Adjacent Rg a d) (hcd : Adjacent Rg c d)
    (hne : edgeOffenderJoin a d ≠ edgeOffenderJoin c d)
    (hca : Q Rg c ≤ edgeOffenderJoin a d)
    (hac : Q Rg a ≤ edgeOffenderJoin c d) :
    Q Rg a ⊔ Q Rg c ≤ edgeOffenderJoin a d ⊓ edgeOffenderJoin c d ∧
      (Q Rg a).relIndex (Q Rg a ⊔ Q Rg c) ∣ 4 ∧
      (Q Rg c).relIndex (Q Rg a ⊔ Q Rg c) ∣ 4 := by
  obtain ⟨Ja,_,hJa,hQa,_⟩ := borel_edge_maximal_offenders h e hz hk u hR ha had
  obtain ⟨Jc,_,hJc,hQc,_⟩ := borel_edge_maximal_offenders h e hz hk u hR hc hcd
  rw [←hJa] at hQa
  rw [←hJc] at hQc
  have hle : Q Rg a ⊔ Q Rg c ≤ edgeOffenderJoin a d ⊓ edgeOffenderJoin c d :=
    sup_le (le_inf hQa hac) (le_inf hca hQc)
  have hi := borel_opposite_containing_core_index h e hz hk u hR ha hc had hcd hne hac
  have hj := borel_opposite_containing_core_index h e hz hk u hR hc ha hcd had hne.symm hca
  rw [inf_comm] at hj
  have hi' := relIndex_mul_relIndex (Q Rg a) (Q Rg a ⊔ Q Rg c) _ le_sup_left hle
  have hj' := relIndex_mul_relIndex (Q Rg c) (Q Rg a ⊔ Q Rg c) _ le_sup_right hle
  rw [hi] at hi'
  rw [hj] at hj'
  exact ⟨hle,⟨_,hi'.symm⟩,⟨_,hj'.symm⟩⟩

private theorem terminal_normal_core_index {F : Type*} [Group F]
    (N A : Subgroup F) (hn : A ≤ normalizer (N : Set F)) :
    N.relIndex (N ⊔ A) = N.relIndex A := by
  let H := N ⊔ A
  let : (N.subgroupOf H).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le N.le_normalizer hn)
  have hh := relIndex_sup_left (A.subgroupOf H) (N.subgroupOf H)
  rw [←subgroupOf_sup (show N ≤ H from le_sup_left) (show A ≤ H from le_sup_right),
    relIndex_subgroupOf le_rfl,relIndex_subgroupOf (show A ≤ H from le_sup_right)] at hh
  exact hh

private theorem terminal_core_saturation {F : Type*} [Group F]
    (N C A : Subgroup F) (hAC : A ≤ C) (hn : A ≤ normalizer (N : Set F))
    (hdiv : N.relIndex (N ⊔ C) ∣ 4) (hfour : N.relIndex A = 4) :
    N ⊔ A = N ⊔ C := by
  have hi : N.relIndex (N ⊔ A) = 4 := (terminal_normal_core_index N A hn).trans hfour
  have hmul := relIndex_mul_relIndex N (N ⊔ A) (N ⊔ C) le_sup_left (sup_le_sup_left hAC N)
  rw [hi] at hmul
  have hbound : N.relIndex (N ⊔ C) ≤ 4 := Nat.le_of_dvd (by decide) hdiv
  have hpos : N.relIndex (N ⊔ C) ≠ 0 := by intro hz; rw [hz] at hdiv; norm_num at hdiv
  have he : (N ⊔ A).relIndex (N ⊔ C) = 1 := by omega
  exact le_antisymm (sup_le_sup_left hAC N) (relIndex_eq_one.mp he)

include h e hz hk in
/-- The two-core product bounds every joint seed image on the same edge.
If the joint image has order four, it supplies the whole neighboring-core
commutator, not merely a subspace of the moving quotient. -/
theorem borel_mutual_core_joint_image
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a c d : Vertex Rg} (ha : color Rg a = false) (hc : color Rg c = false)
    (had : Adjacent Rg a d) (hcd : Adjacent Rg c d)
    (hne : edgeOffenderJoin a d ≠ edgeOffenderJoin c d)
    (hca : Q Rg c ≤ edgeOffenderJoin a d)
    (hac : Q Rg a ≤ edgeOffenderJoin c d)
    (A : Subgroup (FreeAmalgam Rg)) (hAC : A ≤ Q Rg c) :
    (Q Rg a).relIndex A ∣ 4 ∧
      ((Q Rg a).relIndex A = 4 →
        Q Rg a ⊔ A = Q Rg a ⊔ Q Rg c ∧
        ⁅Z Rg a,A⁆ = ⁅Z Rg a,Q Rg c⁆) := by
  have hprod := borel_mutual_core_product_index h e hz hk u hR ha hc had hcd hne hca hac
  obtain ⟨J,_,hJ,_,hJT,_⟩ := borel_edge_maximal_offenders h e hz hk u hR ha had
  have hJE : edgeOffenderJoin a d ≤ Q Rg d := by rwa [hJ]
  have hCG : Q Rg c ≤ stabilizer Rg a :=
    (hca.trans hJE).trans (fun _ hx => hx.2 _ (adjacent_symm Rg had))
  have hAN : A ≤ normalizer (Q Rg a : Set (FreeAmalgam Rg)) :=
    (hAC.trans hCG).trans (Q_normalized Rg a)
  have hi := relIndex_mul_relIndex (Q Rg a) (Q Rg a ⊔ A) (Q Rg a ⊔ Q Rg c)
    le_sup_left (sup_le_sup_left hAC _)
  rw [terminal_normal_core_index _ _ hAN] at hi
  refine ⟨(Dvd.intro _ hi).trans hprod.2.1,fun hfour => ?_⟩
  have he := terminal_core_saturation (Q Rg a) (Q Rg c) A hAC hAN hprod.2.1 hfour
  have hQZ : Q Rg a ≤ centralizer (Z Rg a : Set (FreeAmalgam Rg)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg a ha))
  have hAZ := (hAC.trans hCG).trans (Z_normalized Rg a)
  have hCZ := hCG.trans (Z_normalized Rg a)
  exact ⟨he,(commutator_eq_of_centralizing_sup rfl hQZ hAZ).trans
    ((congrArg (fun D => ⁅Z Rg a,D⁆) he).trans
      (commutator_eq_of_centralizing_sup rfl hQZ hCZ).symm)⟩

include h e hz hk in
/-- For two critical seeds at a common endpoint, a joint image of order
two forces the same whole-seed commutator and the same full critical kernel. -/
theorem borel_joint_image_two_equal_lines
    {a c f : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) c a)
    (q : CriticalPath Rg (sourceGeometry h) f a)
    (hi : (Q Rg a).relIndex (Z Rg c ⊔ Z Rg f) = 2) :
    ⁅Z Rg c,Z Rg a⁆ = ⁅Z Rg f,Z Rg a⁆ ∧
      Nat.card (⁅Z Rg c,Z Rg a⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
      Z Rg a ⊓ Q Rg c = Z Rg a ⊓ Q Rg f := by
  let A := Z Rg c ⊔ Z Rg f
  have hca : Z Rg c ≤ stabilizer Rg a := Z_le_stabilizer_of_dist_le c ((sourceGeometry h).exists_critical c p.start_color) p.critical.1.le
  have hfa : Z Rg f ≤ stabilizer Rg a := Z_le_stabilizer_of_dist_le f ((sourceGeometry h).exists_critical f q.start_color) q.critical.1.le
  have hA : A ≤ stabilizer Rg a := sup_le hca hfa
  let := finite_stabilizer Rg a
  let := finite_Z Rg c
  let := finite_Z Rg f
  let : Finite A := Finite.of_injective (inclusion hA) (inclusion_injective _)
  have hc2 : (Q Rg a).relIndex (Z Rg c) = 2 := by
    have hle := relIndex_le_of_le_right (show Z Rg c ≤ A from le_sup_left)
      (index_ne_zero_of_finite : (Q Rg a).relIndex A ≠ 0)
    have hpos : (Q Rg a).relIndex (Z Rg c) ≠ 0 := index_ne_zero_of_finite
    have hne : (Q Rg a).relIndex (Z Rg c) ≠ 1 := fun he => p.critical.2 (relIndex_eq_one.mp he)
    change (Q Rg a).relIndex A = 2 at hi
    omega
  have hf2 : (Q Rg a).relIndex (Z Rg f) = 2 := by
    have hle := relIndex_le_of_le_right (show Z Rg f ≤ A from le_sup_right)
      (index_ne_zero_of_finite : (Q Rg a).relIndex A ≠ 0)
    have hpos : (Q Rg a).relIndex (Z Rg f) ≠ 0 := index_ne_zero_of_finite
    have hne : (Q Rg a).relIndex (Z Rg f) ≠ 1 := fun he => q.critical.2 (relIndex_eq_one.mp he)
    change (Q Rg a).relIndex A = 2 at hi
    omega
  have hAN := hA.trans (Q_normalized Rg a)
  have join_eq (D : Subgroup (FreeAmalgam Rg)) (hD : D ≤ A)
      (hD2 : (Q Rg a).relIndex D = 2) : Q Rg a ⊔ D = Q Rg a ⊔ A := by
    have hm := relIndex_mul_relIndex (Q Rg a) (Q Rg a ⊔ D) (Q Rg a ⊔ A)
      le_sup_left (sup_le_sup_left hD _)
    rw [terminal_normal_core_index _ _ (hD.trans hAN),terminal_normal_core_index _ _ hAN,
      hD2,hi] at hm
    have he : (Q Rg a ⊔ D).relIndex (Q Rg a ⊔ A) = 1 := by omega
    exact le_antisymm (sup_le_sup_left hD _) (relIndex_eq_one.mp he)
  have hgen := (join_eq (Z Rg c) le_sup_left hc2).trans
    (join_eq (Z Rg f) le_sup_right hf2).symm
  have hQZ : Q Rg a ≤ centralizer (Z Rg a : Set (FreeAmalgam Rg)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg a p.end_color))
  have he : ⁅Z Rg a,Z Rg c⁆ = ⁅Z Rg a,Z Rg f⁆ :=
    (commutator_eq_of_centralizing_sup rfl hQZ (hca.trans (Z_normalized Rg a))).trans
      ((congrArg (fun D => ⁅Z Rg a,D⁆) hgen).trans
        (commutator_eq_of_centralizing_sup rfl hQZ (hfa.trans (Z_normalized Rg a))).symm)
  let pr : CriticalPath Rg (sourceGeometry h) a c := CriticalPath.ofPair p.end_color (reverse_pair h e p)
  let qr : CriticalPath Rg (sourceGeometry h) a f := CriticalPath.ofPair q.end_color (reverse_pair h e q)
  have hp : (Q Rg a).relIndex (Z Rg c) < 4 := by omega
  have hq : (Q Rg a).relIndex (Z Rg f) < 4 := by omega
  have hpr : (Q Rg c).relIndex (Z Rg a) < 4 := by
    rw [(small_critical_indices h e hz hk p hp).2]; decide
  have hqr : (Q Rg f).relIndex (Z Rg a) < 4 := by
    rw [(small_critical_indices h e hz hk q hq).2]; decide
  refine ⟨?_,small_critical_commutator_card h e hz hk p hp,
    small_critical_equal_lines_kernels h e hz hk pr qr hpr hqr he⟩
  simpa only [commutator_comm (Z Rg c),commutator_comm (Z Rg f)] using he

include h e hz hk in
private theorem borel_core_joint_commutator
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a d : Vertex Rg} (ha : color Rg a = false) (had : Adjacent Rg a d)
    (C A B : Subgroup (FreeAmalgam Rg))
    (hC : C ≤ edgeOffenderJoin a d) (hA : A ≤ C) (hB : B ≤ C) :
    ⁅Z Rg a,A ⊔ B⁆ = ⁅Z Rg a,A⁆ ⊔ ⁅Z Rg a,B⁆ := by
  let H := ⁅Z Rg a,A⁆ ⊔ ⁅Z Rg a,B⁆
  have hquad : ⁅⁅Z Rg a,C⁆,C⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact (commutator_mono (commutator_mono le_rfl hC) hC).trans_eq
      (remaining_edge_full_seed_quadratic h e hz hk u (Or.inr hR) ha had)
  have hHC : H ≤ ⁅Z Rg a,C⁆ := sup_le (commutator_mono le_rfl hA) (commutator_mono le_rfl hB)
  have hCH : C ≤ normalizer (H : Set (FreeAmalgam Rg)) :=
    ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hquad)).trans
      (centralizer_le hHC)).trans (Subgroup.centralizer_le_normalizer _)
  apply le_antisymm
  · rw [commutator_comm]
    exact commutator_sup_le_of_relative_normal C A B (Z Rg a) H hCH hA hB
      (by rw [commutator_comm]; exact le_sup_left)
      (by rw [commutator_comm]; exact le_sup_right)
  · exact sup_le (commutator_mono le_rfl le_sup_left) (commutator_mono le_rfl le_sup_right)

include h e hz hk in
/-- Both actual reverse selectors have joint image of order two or four.
The order-two branch has equal full critical kernels and equal lines; the
order-four branch generates the whole neighboring-core movement. Every
path overlap, full-omega normalizer and actual transporter is retained. -/
theorem borel_four_shift_reverse_joint_image
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : BorelBackwardShift (h := h) p) (r : BorelBackwardShift (h := h) q.path)
    (t : BorelBackwardShift (h := h) r.path) (s : BorelBackwardShift (h := h) t.path)
    (hse : act Rg s.transporter (t.path.walk.getVert 1) = s.edge)
    (hne : edgeOffenderJoin t.start s.edge ≠ edgeOffenderJoin s.start s.edge) :
    let v := t.path.walk.getVert (t.path.walk.length-2)
    ∃ g ∈ stabilizer Rg v, ∃ x ∈ stabilizer Rg v,
      let d := act Rg g (s.path.walk.getVert (s.path.walk.length-1))
      let c := act Rg g (s.path.walk.getVert (s.path.walk.length-2))
      let A := Z Rg c ⊔ Z Rg (act Rg x c)
      Q Rg d ⊔ Z Rg s.start = stabilizer Rg v ∧
      Q Rg (act Rg x d) ⊔ Z Rg s.start = stabilizer Rg v ∧
      edgeOffenderJoin v d ⊔ edgeOffenderJoin v (act Rg x d) = stabilizer Rg v ∧
      x ∈ normalizer (edgeOffenderJoin v
        (s.path.walk.getVert (s.path.walk.length-1)) : Set (FreeAmalgam Rg)) ∧
      X Rg s.start ≤ normalizer (((Z Rg c ⊓ Q Rg t.start) ⊔ Z Rg v :
        Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
      X Rg s.start ≤ normalizer (((Z Rg (act Rg x c) ⊓ Q Rg t.start) ⊔ Z Rg v :
        Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
      A ≤ Q Rg r.start ∧
      ((Q Rg t.start).relIndex A = 2 ∨ (Q Rg t.start).relIndex A = 4) ∧
      ((Q Rg t.start).relIndex A = 2 →
        ⁅Z Rg c,Z Rg t.start⁆ = ⁅Z Rg (act Rg x c),Z Rg t.start⁆ ∧
        Nat.card (⁅Z Rg c,Z Rg t.start⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
        Z Rg t.start ⊓ Q Rg c = Z Rg t.start ⊓ Q Rg (act Rg x c)) ∧
      ((Q Rg t.start).relIndex A = 4 →
        Q Rg t.start ⊔ A = Q Rg t.start ⊔ Q Rg r.start ∧
        ⁅Z Rg c,Z Rg t.start⁆ ⊔ ⁅Z Rg (act Rg x c),Z Rg t.start⁆ =
          ⁅Z Rg t.start,Q Rg r.start⁆) ∧
      ∃ (s₁ : CriticalPath Rg (sourceGeometry h) c t.start)
        (s₂ : CriticalPath Rg (sourceGeometry h) (act Rg x c) t.start),
        s₁.walk.getVert 1 = d ∧ s₂.walk.getVert 1 = act Rg x d ∧
        (∀ i ≤ s.path.walk.length-2,
          s₁.walk.getVert (i+2) = s.path.walk.getVert (s.path.walk.length-i)) ∧
        (∀ i ≤ s.path.walk.length-2,
          s₂.walk.getVert (i+2) = s.path.walk.getVert (s.path.walk.length-i)) := by
  obtain ⟨g,hg,x,hx,hgen₁,hgen₂,hpair,hnorm,hN₁,hN₂,_,_,s₁,s₂,hs₁,hs₂,ho₁,ho₂⟩ :=
    borel_three_shift_reverse_choices h e hz hk hb u hR q.path r t s hne
  let c := act Rg g (s.path.walk.getVert (s.path.walk.length-2))
  let A := Z Rg c ⊔ Z Rg (act Rg x c)
  have htlen : t.path.walk.length = sourceDistance h := t.path.length_eq_b
  have hslen : s.path.walk.length = sourceDistance h := s.path.length_eq_b
  have ht2 : t.path.walk.getVert 2 = r.start := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using t.overlap 0 (Nat.zero_le _)
  have hs4 : s.path.walk.getVert 4 = r.start := by
    simpa only [show 2+2=4 from rfl,ht2] using s.overlap 2 (by omega)
  have seed_core {y : Vertex Rg} (w : CriticalPath Rg (sourceGeometry h) y t.start)
      (ho : ∀ i ≤ s.path.walk.length-2,
        w.walk.getVert (i+2) = s.path.walk.getVert (s.path.walk.length-i)) :
      Z Rg y ≤ Q Rg r.start := by
    have hwlen : w.walk.length = sourceDistance h := w.length_eq_b
    have hv : w.walk.getVert (w.walk.length-2) = r.start := by
      have hh := ho (s.path.walk.length-4) (by omega)
      rw [show s.path.walk.length-4+2=w.walk.length-2 by omega,
        show s.path.walk.length-(s.path.walk.length-4)=4 by omega,hs4] at hh
      exact hh
    apply Z_le_Q_of_dist_lt Rg y ((sourceGeometry h).exists_critical y w.start_color)
    have hd : (cosetGraph Rg).dist y r.start = w.walk.length-2 :=
      (congrArg (fun z => (cosetGraph Rg).dist y z) hv).symm.trans
        (w.dist_start (by omega : w.walk.length-2 ≤ w.walk.length))
    rw [hd,(sourceGeometry h).distance_constant _ w.start_color]
    change w.walk.length-2 < sourceDistance h
    omega
  have hAC : A ≤ Q Rg r.start := sup_le (seed_core s₁ ho₁) (seed_core s₂ ho₂)
  have hsr : act Rg s.transporter r.start = s.start := by simpa only [ht2] using s.start_eq
  have hst : act Rg s.transporter t.edge = s.edge := by simpa only [t.first] using hse
  have hjt := remaining_edge_join_act h e hz hk u (Or.inr hR)
    t.path.start_color t.adjacent_shift s.transporter
  have hjr := remaining_edge_join_act h e hz hk u (Or.inr hR)
    r.path.start_color t.adjacent_start s.transporter
  rw [show act Rg s.transporter t.start = t.start from s.transporter_mem,hst] at hjt
  rw [hsr,hst] at hjr
  have hne' : edgeOffenderJoin t.start t.edge ≠ edgeOffenderJoin r.start t.edge := by
    intro he
    exact hne (hjt.trans ((congrArg (Subgroup.map (MulAut.conj s.transporter⁻¹).toMonoidHom) he).trans hjr.symm))
  have hcores := borel_four_shift_mutual_cores h e hz hk hb u hR p q r t s hse
  have him := borel_mutual_core_joint_image h e hz hk u hR t.path.start_color r.path.start_color
    t.adjacent_shift t.adjacent_start hne' hcores.1 hcores.2 A hAC
  have hi : (Q Rg t.start).relIndex A = 2 ∨ (Q Rg t.start).relIndex A = 4 := by
    have hbound := Nat.le_of_dvd (by decide : 0 < 4) him.1
    have hn : (Q Rg t.start).relIndex A ≠ 1 :=
      fun he => s₁.critical.2 (le_sup_left.trans (relIndex_eq_one.mp he))
    have hd := him.1
    interval_cases he : (Q Rg t.start).relIndex A <;> norm_num at hd <;> omega
  refine ⟨g,hg,x,hx,hgen₁,hgen₂,hpair,hnorm,hN₁,hN₂,hAC,hi,
    fun he => borel_joint_image_two_equal_lines h e hz hk s₁ s₂ he,?_,
    s₁,s₂,hs₁,hs₂,ho₁,ho₂⟩
  intro he
  have hh := him.2 he
  have hcomm := borel_core_joint_commutator h e hz hk u hR t.path.start_color t.adjacent_shift
    (Q Rg r.start) (Z Rg c) (Z Rg (act Rg x c)) hcores.1
    (seed_core s₁ ho₁) (seed_core s₂ ho₂)
  refine ⟨hh.1,?_⟩
  rw [commutator_comm (Z Rg c),commutator_comm (Z Rg (act Rg x c)),←hcomm]
  exact hh.2

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
