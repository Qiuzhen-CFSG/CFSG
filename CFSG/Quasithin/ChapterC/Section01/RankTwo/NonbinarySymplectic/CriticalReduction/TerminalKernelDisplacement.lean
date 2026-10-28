module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.TerminalKernelSaturation
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.SmallMoverKernels

/-!
# Displacement between the full terminal critical kernels

On the actual large-mover terminal sequence, write a,z for the endpoints
of the second backward shift and c,e for the preceding shift. The smaller
mover at a normalizes E = Z_a intersect Q_z. Its generation with Z_e and
the proved escape E not contained in B_c force displacement beyond Z_c.
The full critical-intersection calculation therefore makes
R_gamma = [E, Z_e intersect Q_c] nontrivial, of order at least q.

The same commutator is obtained using the entire X_e intersection or the
U_e intersection. It lies in E intersect U_e and centralizes E. If Z_e
normalized E joined with Z_c, the whole vertex residual would normalize
that radius subgroup. Its index modulo Z_c is at most q cubed, so the
small-section theorem would put E in B_c, a contradiction.

All conclusions hold on the same prescribed residual-orbit sequence as
the saturated central kernels, their two-step periodicity, propagation
and exact full commutator orders. The original field degree and every
central attachment are retained. This constructs the literal nonzero
kernel commutator needed in the normalizer comparison of MS93 (5.10),
printed p.922. Its remaining comparison with the critical commutator,
the unequal-contained Lambda selectors, terminal exclusions and actual
minimum-replacement distance-two witness remain to be proved. The
separate original-radical characteristic-control obligation is unchanged.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3), (5.9)--(5.10), printed pp.866--867 and 920--923.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem first_mover_normalizes_critical_kernel
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hi : (Q d.radical z).relIndex (Z d.radical a)=Nat.card F) :
    Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) ≤
        normalizer ((Z d.radical a ⊓ Q d.radical z : Subgroup (FreeAmalgam d.radical)) : Set _) := by
  let t := path.walk.getVert 1
  have hat : Adjacent d.radical a t := by
    have hh := (cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by rw [path.length_eq_b]; omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using hh
  have hzT : Z d.radical z ≤ Q d.radical t := by
    apply Z_le_Q_of_dist_lt _ z (geometry.exists_critical z path.end_color)
    rw [geometry.distance_constant z path.end_color,SimpleGraph.dist_comm,path.dist_end,path.length_eq_b]
    change geometry.b d.radical-1 < geometry.b d.radical
    omega
  have hS : Z d.radical a ≤ stabilizer d.radical z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
  have hC := MSCentralOrbit.C_eq_Q d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d) z path.end_color
  have he : Z d.radical a ⊓ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) =
      Z d.radical a ⊓ Q d.radical z := by
    rw [←hC]
    ext x
    exact ⟨fun hx => ⟨hx.1,hS hx.1,hx.2⟩,fun hx => ⟨hx.1,hx.2.2⟩⟩
  have hidx : (centralizer (Z d.radical z : Set (FreeAmalgam d.radical))).relIndex
      (Z d.radical a)=Nat.card F := by
    rw [←inf_relIndex_left,he,inf_relIndex_left,hi]
  let := finite_Z d.radical a
  have hiU : (centralizer (Z d.radical z : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) ≤ Nat.card F :=
    (relIndex_le_of_le_right (U_le_Z a) index_ne_zero_of_finite).trans_eq hidx
  have hn := h.replacement_small_mover_join_normalizes_full_seed_fixed d geometry hb
    path.start_color hat (Z d.radical z) hzT hiU
  rwa [he] at hn

/-- The same saturated terminal sequence has a nonzero mutual critical-kernel
commutator and endpoint normalizer escape. The complete X/U identities and
all retained central kernels belong to these literal paths. -/
theorem Input.replacement_large_mover_terminal_kernel_displacement
    {geometry : Geometry d.radical} (p : CriticalSegment geometry)
    (hb : 4 < geometry.b d.radical)
    (hJm : Nat.card F^2 < (centralizer (Subgroup.SmallMover.join (U d.radical p.first)
      (Q d.radical p.first) (Q d.radical (p.path.walk.getVert 1)) (Nat.card F^2) :
        Set (FreeAmalgam d.radical))).relIndex (U d.radical p.first)) :
    ∃ s : ℕ → CriticalSegment geometry, s 0 = p ∧
      (∀ i, BackwardLink geometry (pointPathChoice geometry (Nat.card F)) (s i) (s (i+1))) ∧
      (∀ i k j, j+2*k ≤ geometry.b d.radical →
        (s (i+k)).path.walk.getVert (j+2*k) = (s i).path.walk.getVert j) ∧
      (∀ i, let C := fun j => U d.radical (s j).first ⊓
          centralizer (stabilizer d.radical (s j).first : Set (FreeAmalgam d.radical))
        let D := ⁅Z d.radical (s (i+2)).first,Z d.radical (s (i+2)).last⁆
        C (i+2) = C i ∧
        D ⊓ Z d.radical ((s (i+2)).path.walk.getVert 1) = C i ∧
        D ⊓ (stabilizer d.radical (s (i+1)).first ⊓
          centralizer (stabilizer d.radical (s (i+1)).first : Set (FreeAmalgam d.radical))) = C i ∧
        Nat.card D = Nat.card F * Nat.card (C 0) ∧
        (∀ k, C i ≤ stabilizer d.radical (s (i+k)).first ⊓
          centralizer (stabilizer d.radical (s (i+k)).first : Set (FreeAmalgam d.radical))) ∧
        (Q d.radical (s (i+2)).last).relIndex (Z d.radical (s (i+2)).first)=Nat.card F ∧
        (Q d.radical (s (i+2)).first).relIndex (Z d.radical (s (i+2)).last)=Nat.card F ∧
        (¬ Z d.radical (s (i+2)).first ⊓ Q d.radical (s (i+2)).last ≤
          B d.radical (s (i+1)).first (geometry.Z_normal (s (i+1)).first))) ∧
      (∀ i, let a := (s (i+2)).first
        let z := (s (i+2)).last
        let c := (s (i+1)).first
        let e := (s (i+1)).last
        let E := Z d.radical a ⊓ Q d.radical z
        let D := ⁅E,Z d.radical e ⊓ Q d.radical c⁆
        (Q d.radical e).relIndex (Z d.radical c)=Nat.card F ∧
        (Q d.radical c).relIndex (Z d.radical e)=Nat.card F ∧
        ¬ ⁅E,Z d.radical e⁆ ≤ Z d.radical c ∧
        (¬ Z d.radical e ≤ normalizer ((E ⊔ Z d.radical c : Subgroup (FreeAmalgam d.radical)) : Set _)) ∧
        D ≠ ⊥ ∧ Nat.card F ≤ Nat.card D ∧
        ⁅E,X d.radical e ⊓ Q d.radical c⁆ = D ∧
        D = ⁅E,U d.radical e ⊓ Q d.radical c⁆ ∧
        D ≤ E ⊓ U d.radical e ∧ ⁅D,E⁆=⊥) := by
  obtain ⟨s,hs0,hs,hover,hdata⟩ := h.replacement_large_mover_terminal_saturated_kernels d p hb hJm
  refine ⟨s,hs0,hs,hover,hdata,?_⟩
  intro i
  dsimp only
  let a := (s (i+2)).first
  let z := (s (i+2)).last
  let c := (s (i+1)).first
  let e := (s (i+1)).last
  let t := (s (i+2)).path.walk.getVert 1
  let E := Z d.radical a ⊓ Q d.radical z
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  obtain ⟨hperiod,hedge,hprev,hcard,hprop,hi,hi',hnotB⟩ := hdata i
  have hJN : J ≤ normalizer (E : Set (FreeAmalgam d.radical)) :=
    first_mover_normalizes_critical_kernel h d (s (i+2)).path hb.le hi
  obtain ⟨w,hw,hcw,haw,hfirst⟩ := (hs (i+1)).choice
  have htw : t=w := by simpa only [t,show i+1+1=i+2 by omega] using hfirst
  have hgen : J ⊔ Z d.radical e=stabilizer d.radical c := by
    simpa only [J,t,htw,show i+1+1=i+2 by omega] using hw.2.1
  have hEV : E ≤ V d.radical c := inf_le_left.trans
    (le_sup_left.trans (neighbor_seed_join_le_radius hcw haw))
  have hdist : (cosetGraph d.radical).dist z e=2 := by
    simpa only [show i+1+1=i+2 by omega] using
      shifted_last_distance (pointPathChoice geometry (Nat.card F)) s hs (i+1) 1 (by omega)
  have hES : E ≤ stabilizer d.radical e := inf_le_right.trans
    (Q_le_stabilizer_of_dist_le_two z e (s (i+2)).path.end_color
      (s (i+1)).path.end_color hdist.le)
  obtain ⟨hbad,hic,hie,hn,hlo,heq⟩ := h.replacement_generated_radius_intersection d
    (s (i+1)).path hb.le E J hEV hES (le_sup_left.trans_eq hgen) hJN hgen hnotB
  have hZX : Z d.radical e ≤ X d.radical e := geometry.omega_bound e (s (i+1)).path.end_color
    (by
      rw [geometry.distance_constant e (s (i+1)).path.end_color]
      change 0 < geometry.b d.radical
      omega)
  have hEq : ⁅E,Z d.radical e ⊓ Q d.radical c⁆ = ⁅E,X d.radical e ⊓ Q d.radical c⁆ := by
    apply le_antisymm (commutator_mono le_rfl (inf_le_inf_right _ hZX))
    rw [heq]
    exact commutator_mono le_rfl (inf_le_inf_right _ (U_le_Z e))
  have hsmall : (Q d.radical c).relIndex (Z d.radical e) < Nat.card F^2 := by
    rw [hie]
    have hq : 1 < Nat.card F := Finite.one_lt_card
    nlinarith
  have hnormbad : ¬ Z d.radical e ≤ normalizer
      ((E ⊔ Z d.radical c : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    intro hnorm
    have hJY : J ≤ normalizer ((E ⊔ Z d.radical c : Subgroup (FreeAmalgam d.radical)) : Set _) :=
      (le_inf hJN ((le_sup_left.trans_eq hgen).trans (Z_normalized d.radical c))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
    have hYN : stabilizer d.radical c ≤ normalizer
        ((E ⊔ Z d.radical c : Subgroup (FreeAmalgam d.radical)) : Set _) :=
      hgen.symm.le.trans (sup_le hJY hnorm)
    have hSV : Z d.radical a ⊔ Z d.radical c ≤ V d.radical c :=
      neighbor_seed_join_le_radius hcw haw
    let := finite_stabilizer d.radical c
    let : Finite (Z d.radical a ⊔ Z d.radical c : Subgroup (FreeAmalgam d.radical)) :=
      Finite.of_injective (inclusion (hSV.trans
        ((geometry.V_le_Q (by omega) c (s (i+1)).path.start_color).trans (fun _ hx => hx.1))))
        (inclusion_injective _)
    have hbound := h.replacement_root_neighbor_seed_index_le_cube d (s (i+1)).path hb.le hcw haw hsmall
    have hiY : (Z d.radical c).relIndex (E ⊔ Z d.radical c) ≤ Nat.card F^3 :=
      (relIndex_le_of_le_right (sup_le_sup inf_le_left le_rfl) index_ne_zero_of_finite).trans
      ((neighbor_seed_join_index_le geometry (by omega) (s (i+1)).path.start_color hcw haw).trans hbound)
    have hlt : Nat.card F^3 < Nat.card F^4 := Nat.pow_lt_pow_right (by exact Finite.one_lt_card) (by decide)
    exact hnotB (le_sup_left.trans (h.replacement_small_radius_le_B d geometry (by omega)
      (s (i+1)).path.start_color (E ⊔ Z d.radical c)
      (sup_le hEV (Z_le_VBall d.radical c 2))
      ((Ltilde_le_stabilizer c).trans hYN) (hiY.trans_lt hlt)))
  have hAeS : U d.radical e ⊓ Q d.radical c ≤ stabilizer d.radical a :=
    inf_le_right.trans (Q_le_stabilizer_of_dist_le_two c a (s (i+1)).path.start_color
      (s (i+2)).path.start_color (by
        rw [SimpleGraph.dist_comm]
        simpa only [show i+1+1=i+2 by omega] using
          (shifted_start_distance (pointPathChoice geometry (Nat.card F)) s hs (i+1) 1 (by omega)).le))
  have heQz : U d.radical e ≤ Q d.radical z := (U_le_Z e).trans (by
    apply Z_le_Q_of_dist_lt _ e (geometry.exists_critical e (s (i+1)).path.end_color)
    rw [geometry.distance_constant e (s (i+1)).path.end_color,SimpleGraph.dist_comm,hdist]
    change 2 < geometry.b d.radical; omega)
  have hAN : U d.radical e ⊓ Q d.radical c ≤ normalizer (E : Set (FreeAmalgam d.radical)) := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    change E.map (MulAut.conj x).toMonoidHom=E
    dsimp only [E]
    rw [map_inf _ _ _ (MulAut.conj x).injective,MulEquiv.toMonoidHom_eq_coe,
      mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical a (hAeS hx)),
      mem_normalizer_iff_map_conj_eq.mp ((Q d.radical z).le_normalizer (heQz hx.1))]
  have hDE : ⁅E,U d.radical e ⊓ Q d.radical c⁆ ≤ E :=
    le_normalizer_iff_commutator_le_left.mp hAN
  have hDU : ⁅E,U d.radical e ⊓ Q d.radical c⁆ ≤ U d.radical e := by
    rw [commutator_comm]
    exact (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hES.trans (U_normalized e)))
  have hquad : ⁅⁅E,U d.radical e ⊓ Q d.radical c⁆,E⁆=⊥ := by
    rw [commutator_comm E]
    exact le_bot_iff.mp ((commutator_mono
      (commutator_mono (inf_le_inf_right _ ((U_le_Z e).trans hZX)) (le_inf hEV inf_le_right))
      (le_inf hEV inf_le_right)).trans_eq
        (h.replacement_radius_commutator_bounds d geometry hb.le (s (i+1)).path.start_color e z).2)
  exact ⟨hic,hie,hbad,hnormbad,by rwa [hEq],by rwa [hEq],hEq.symm,hEq.trans heq,
    (hEq.trans heq).symm ▸ le_inf hDE hDU,by rwa [hEq,heq]⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
