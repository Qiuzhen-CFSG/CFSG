module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.TerminalIndices

/-!
# Retained central kernels on the nonbinary terminal paths

The full R₄ commutator meets its first edge seed in exactly its full
starting-vertex central kernel. The same kernel is its intersection with
the preceding starting-vertex center, so both quotients have order q.
The reverse inclusion uses the actual common edge: a central involution
in its neighborhood kernel lies in its omega-center.

The residual two-step orbit choices propagate this retained subgroup into
every subsequent starting-vertex center. On those same paths, the exact
critical-image order and MS93 (5.9) force the whole critical seed kernel
outside B at the preceding start. Both critical endpoints also have the
proved full-X decomposition over their actual central attachments.

This is an application to the existing large-mover terminal sequence, with
no additional selection premise or field-degree restriction. It supplies
central-kernel comparisons used in (5.10); the unequal-contained Lambda
selectors, remaining normalizer and displacement comparisons, terminal
exclusions and minimum-replacement distance-two witness remain to be proved.
It supplies no original-radical characteristic-control assertion.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.10), printed pp.922--923; the strict-index input is (5.9).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic

private theorem central_seed_le_incident_edge
    {M : Type*} [Group M] {R : Subgroup M} {geometry : Geometry R}
    (hb : 2 < geometry.b R) {a c t : Vertex R}
    (ha : color R a=false) (hat : Adjacent R a t) (hct : Adjacent R c t) :
    Z R a ⊓ centralizer (stabilizer R c : Set (FreeAmalgam R)) ≤ Z R t := by
  have ht : color R t ≠ false := fun ht => (adjacent_color_ne R hat) (ha.trans ht.symm)
  have hZT : Z R a ≤ Q R t := by
    apply Z_le_Q_of_dist_lt R a (geometry.exists_critical a ha)
    rw [geometry.distance_constant a ha,
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hat)]
    exact lt_trans (by decide : 1 < 2) hb
  let : IsElementaryAbelian 2 (Z R a) := geometry.Z_elementary (by omega) a ha
  rintro x ⟨hx,hc⟩
  rw [Z,if_neg ht]
  apply mem_omegaCenter_iff.mpr
  refine ⟨hZT hx,elemPow_eq_one_of_isElementaryAbelian _ hx,?_⟩
  exact (centralizer_le (show Q R t ≤ stabilizer R c from
    fun _ hy => hy.2 c (adjacent_symm R hct))) hc

private theorem full_center_transport
    {M : Type*} [Group M] {R : Subgroup M}
    (A : Subgroup (FreeAmalgam R)) {a c v : Vertex R}
    (ha : A ≤ stabilizer R a ⊓ centralizer (stabilizer R a : Set (FreeAmalgam R)))
    (hc : A ≤ centralizer (stabilizer R c : Set (FreeAmalgam R)))
    {y : FreeAmalgam R} (hy : y ∈ stabilizer R c) (hv : act R y a=v) :
    A ≤ stabilizer R v ⊓ centralizer (stabilizer R v : Set (FreeAmalgam R)) := by
  have hfixed : A.map (MulAut.conj y⁻¹).toMonoidHom=A :=
    mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.centralizer_le_normalizer _
        (le_centralizer_iff.mp hc ((stabilizer R c).inv_mem hy)))
  have hh := map_mono (f := (MulAut.conj y⁻¹).toMonoidHom) ha
  rw [hfixed,map_inf _ _ _ (MulAut.conj y⁻¹).injective,
    Theory.GroupTheory.map_centralizer_equiv] at hh
  change A ≤ (stabilizer R a).map (MulAut.conj y⁻¹).toMonoidHom ⊓
    centralizer (((stabilizer R a).map (MulAut.conj y⁻¹).toMonoidHom : Subgroup (FreeAmalgam R)) : Set _) at hh
  rw [←stabilizer_act,hv] at hh
  exact hh

/-- Residual two-step orbit shifts propagate a retained full-center subgroup
through all the subsequent chosen starting vertices. -/
private theorem point_path_full_center_propagation
    {M : Type*} [Group M] {R : Subgroup M} {geometry : Geometry R}
    (hb : 2 ≤ geometry.b R) (q : ℕ)
    (s : ℕ → CriticalSegment geometry)
    (hs : ∀ i, BackwardLink geometry (pointPathChoice geometry q) (s i) (s (i+1)))
    (A : Subgroup (FreeAmalgam R)) (i : ℕ)
    (h₀ : A ≤ stabilizer R (s i).first ⊓
      centralizer (stabilizer R (s i).first : Set (FreeAmalgam R)))
    (h₁ : A ≤ stabilizer R (s (i+1)).first ⊓
      centralizer (stabilizer R (s (i+1)).first : Set (FreeAmalgam R))) :
    ∀ k, A ≤ stabilizer R (s (i+k)).first ⊓
      centralizer (stabilizer R (s (i+k)).first : Set (FreeAmalgam R)) := by
  have hpair : ∀ k,
      (A ≤ stabilizer R (s (i+k)).first ⊓
        centralizer (stabilizer R (s (i+k)).first : Set (FreeAmalgam R))) ∧
      (A ≤ stabilizer R (s (i+k+1)).first ⊓
        centralizer (stabilizer R (s (i+k+1)).first : Set (FreeAmalgam R))) := by
    intro k
    induction k with
    | zero => simpa only [Nat.add_zero] using And.intro h₀ h₁
    | succ k ih =>
      refine ⟨by simpa only [Nat.add_assoc] using ih.2,?_⟩
      obtain ⟨t,⟨⟨y,hy,hyv,hyt,hidx⟩,hgen,hfix⟩,hct,hat,hfirst⟩ := (hs (i+k+1)).choice
      have he := (hs (i+k)).overlap 0 hb
      simp only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] at he
      rw [he] at hyv
      have hh := full_center_transport A ih.1 (ih.2.trans inf_le_right)
        (Ltilde_le_stabilizer _ hy) hyv.symm
      simpa only [Nat.add_assoc] using hh
  exact fun k => (hpair k).1

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

omit h d in
private theorem kernel_not_le_B_of_index
    {M : Type*} [Group M] [Finite M] {R : Subgroup M} {geometry : Geometry R}
    {a z c : Vertex R} {q : ℕ}
    (hi : (Q R z).relIndex (Z R a) ≤ q)
    (hstrict : q < (B R c (geometry.Z_normal c)).relIndex (U R a)) :
    ¬ Z R a ⊓ Q R z ≤ B R c (geometry.Z_normal c) := by
  intro hle
  let := finite_Z R a
  let : Finite (U R a) := Finite.of_injective
    (inclusion (U_le_Z a)) (inclusion_injective _)
  have hZ := relIndex_le_of_le_left hle (L := Z R a) index_ne_zero_of_finite
  simp only [inf_relIndex_left] at hZ
  have hU := (B R c (geometry.Z_normal c)).relIndex_le_of_le_right
    (U_le_Z a) index_ne_zero_of_finite
  omega

/-- On the actual large-mover terminal sequence, the full R₄ central kernel
is exactly its first-edge intersection and has index q. The same retained
kernel lies in every subsequent starting-vertex center. The literal critical
seed kernel escapes B at the preceding start; both endpoint X-layers split
over their full central attachments. -/
theorem Input.replacement_large_mover_terminal_central_kernels
    {geometry : Geometry d.radical} (p : CriticalSegment geometry)
    (hb : 4 < geometry.b d.radical)
    (hJm : Nat.card F^2 < (centralizer (Subgroup.SmallMover.join (U d.radical p.first)
      (Q d.radical p.first) (Q d.radical (p.path.walk.getVert 1)) (Nat.card F^2) :
        Set (FreeAmalgam d.radical))).relIndex (U d.radical p.first)) :
    ∃ s : ℕ → CriticalSegment geometry, s 0 = p ∧
      (∀ i, BackwardLink geometry (pointPathChoice geometry (Nat.card F)) (s i) (s (i+1))) ∧
      (∀ i k j, j+2*k ≤ geometry.b d.radical →
        (s (i+k)).path.walk.getVert (j+2*k) = (s i).path.walk.getVert j) ∧
      (∀ i, let a := (s (i+2)).first
        let z := (s (i+2)).last
        let t := (s (i+2)).path.walk.getVert 1
        let D := ⁅Z d.radical a,Z d.radical z⁆
        let C := stabilizer d.radical a ⊓
          centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))
        (Q d.radical z).relIndex (Z d.radical a)=Nat.card F ∧
        (Q d.radical a).relIndex (Z d.radical z)=Nat.card F ∧
        D ⊓ Z d.radical t = D ⊓ C ∧
        (Z d.radical t).relIndex D = Nat.card F ∧
        D ⊓ C = D ⊓ (stabilizer d.radical (s (i+1)).first ⊓
          centralizer (stabilizer d.radical (s (i+1)).first : Set (FreeAmalgam d.radical))) ∧
        (stabilizer d.radical (s (i+1)).first ⊓
          centralizer (stabilizer d.radical (s (i+1)).first : Set (FreeAmalgam d.radical))).relIndex D = Nat.card F ∧
        (¬ D ≤ Z d.radical t) ∧
        (∀ k, D ⊓ C ≤ stabilizer d.radical (s (i+k)).first ⊓
          centralizer (stabilizer d.radical (s (i+k)).first : Set (FreeAmalgam d.radical))) ∧
        (¬ Z d.radical a ⊓ Q d.radical z ≤
          B d.radical (s (i+1)).first (geometry.Z_normal (s (i+1)).first)) ∧
        X d.radical a = U d.radical a ⊔
          (X d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
        X d.radical z = U d.radical z ⊔
          (X d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical)))) := by
  obtain ⟨s,hs0,hs,hover,hindices⟩ := h.replacement_large_mover_terminal_indices d p hb hJm
  refine ⟨s,hs0,hs,hover,?_⟩
  intro i
  dsimp only
  obtain ⟨hia,hiz,hiC,hiCz,hcent⟩ := hindices i
  let a := (s (i+2)).first
  let z := (s (i+2)).last
  let t := (s (i+2)).path.walk.getVert 1
  let D := ⁅Z d.radical a,Z d.radical z⁆
  let C := stabilizer d.radical a ⊓
    centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))
  have hat : Adjacent d.radical a t := by
    have hh := (cosetGraph_adj d.radical _ _).mp
      ((s (i+2)).path.walk.adj_getVert_succ
        (by rw [(s (i+2)).path.length_eq_b]; omega : 0 < (s (i+2)).path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using hh
  have hD : D ≤ Z d.radical a := critical_commutator_le_start (s (i+2)) (by omega)
  have heq : D ⊓ Z d.radical t = D ⊓ C := by
    apply le_antisymm
    · exact le_inf inf_le_left (hcent.trans inf_le_right)
    · exact le_inf inf_le_left
        ((le_inf (inf_le_left.trans hD) (inf_le_right.trans inf_le_right)).trans
          (central_seed_le_incident_edge (geometry := geometry) (by omega) (s (i+2)).path.start_color hat hat))
  have hedgeidx : (Z d.radical t).relIndex D=Nat.card F := by
    have hh := congrArg (fun A : Subgroup (FreeAmalgam d.radical) => A.relIndex D) heq
    simp only [inf_relIndex_left] at hh
    exact hh.trans hiC
  have hct : Adjacent d.radical (s (i+1)).first t := by
    obtain ⟨w,hw,hcw,haw,hfirst⟩ := (hs (i+1)).choice
    simpa only [t,show i+1+1=i+2 by omega,hfirst] using hcw
  have heqprev : D ⊓ C = D ⊓ (stabilizer d.radical (s (i+1)).first ⊓
      centralizer (stabilizer d.radical (s (i+1)).first : Set (FreeAmalgam d.radical))) := by
    rw [←heq]
    apply le_antisymm
    · exact le_inf inf_le_left (hcent.trans (inf_le_left.trans inf_le_left))
    · exact le_inf inf_le_left
        ((le_inf (inf_le_left.trans hD) (inf_le_right.trans inf_le_right)).trans
          (central_seed_le_incident_edge (geometry := geometry) (by omega)
            (s (i+2)).path.start_color hat hct))
  have hiprev : (stabilizer d.radical (s (i+1)).first ⊓
      centralizer (stabilizer d.radical (s (i+1)).first : Set (FreeAmalgam d.radical))).relIndex D = Nat.card F := by
    have hh := congrArg (fun A : Subgroup (FreeAmalgam d.radical) => A.relIndex D) heqprev
    simp only [inf_relIndex_left] at hh
    exact hh.symm.trans hiC
  have hnot : ¬ D ≤ Z d.radical t := by
    intro hh
    have hone := relIndex_eq_one.mpr hh
    rw [hedgeidx] at hone
    have hq : 1 < Nat.card F := Finite.one_lt_card
    omega
  have hall : ∀ k, D ⊓ C ≤ stabilizer d.radical (s (i+k)).first ⊓
      centralizer (stabilizer d.radical (s (i+k)).first : Set (FreeAmalgam d.radical)) := by
    apply point_path_full_center_propagation (by omega) (Nat.card F) s hs (D ⊓ C) i
    · rw [←heq]
      exact hcent.trans (inf_le_left.trans inf_le_right)
    · rw [←heq]
      exact hcent.trans (inf_le_left.trans inf_le_left)
  have hmove : Nat.card F <
      (B d.radical (s (i+1)).first (geometry.Z_normal (s (i+1)).first)).relIndex
        (U d.radical a) := by
    obtain ⟨w,⟨horbit,hgen,hfix⟩,_,_,_⟩ := (hs (i+1)).choice
    obtain ⟨y,hy,hya,hyw,hidx⟩ := horbit
    rw [hidx]
    exact h.replacement_path_moving_index_gt_field d (s (i+1)).path hb
  have hkernel := kernel_not_le_B_of_index (geometry := geometry) hia.le hmove
  have hsmall : Nat.card F < Nat.card F^2 := by
    have hq : 1 < Nat.card F := Finite.one_lt_card
    nlinarith
  have hsplit := h.replacement_root_X_decomposition_center d (s (i+2)).path hb.le
    (hiz.trans_lt hsmall)
  let hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d)
  let rev := (s (i+2)).reverse hedge (by omega)
  have hsplitz := h.replacement_root_X_decomposition_center d rev.path hb.le
    (hia.trans_lt hsmall)
  exact ⟨hia,hiz,heq,hedgeidx,heqprev,hiprev,hnot,hall,hkernel,hsplit,hsplitz⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
