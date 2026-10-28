module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.EscapeComparison
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RadiusChief
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootSplitting

/-!
# The actual actor in the distance-four commutator comparison

Retain the original critical path a to z and an actual backward critical
path u to its midpoint e. A prospective selected vertex v shares its
literal edge with u. The full actor W = U_v intersect Q_z then lies in Q_u
and in G_e. It centralizes [Z_u,Z_e], acts quadratically on X_e intersect
Q_u, and is normalized by that whole intersection. These facts follow
from the actual graph placement and the proved radius commutator theorem.
They do not assume that v to a is critical.

If the source comparison [W,Z_e] <= [Z_u,Z_e] [W,X_e intersect Q_u] fails,
the same actor escapes the critical displacement. The existing natural
comparison forces both critical image indices to equal q. Transporting
the resulting whole-X decomposition gives it at the original midpoint a,
with its complete vertex-fixed attachment retained.

Source: MS93 (5.12)(1), printed pp.924--925, using (5.2)(iii) and (3.3).
This is the first inference from failure of (1), not its exclusion. The
tighter root-displacement comparison and the selected-source normality
argument that proves (1) remain separate obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The source actor and its whole fixed intersection have their required
containments, centralization, quadraticity and normalization before the
prospective earlier pair is known to be critical. -/
theorem Input.replacement_distance_four_comparison_actor
    {geometry : Geometry d.radical} {a z u v t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hut : Adjacent d.radical u t) (hvt : Adjacent d.radical v t) :
    let e := path.walk.getVert 2
    let W := U d.radical v ⊓ Q d.radical z
    let A := X d.radical e ⊓ Q d.radical u
    W ≤ Q d.radical u ∧ W ≤ stabilizer d.radical e ∧
      W ≤ centralizer ((⁅Z d.radical u,Z d.radical e⁆ : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      ⁅⁅A,W⁆,W⁆=⊥ ∧ A ≤ normalizer (W : Set (FreeAmalgam d.radical)) := by
  dsimp only
  let e := path.walk.getVert 2
  let W := U d.radical v ⊓ Q d.radical z
  let A := X d.radical e ⊓ Q d.radical u
  have hWVu : W ≤ V d.radical u :=
    inf_le_left.trans ((U_le_Z v).trans
      (le_sup_left.trans (neighbor_seed_join_le_radius hut hvt)))
  have hWQu : W ≤ Q d.radical u :=
    hWVu.trans (geometry.V_le_Q (by omega) u back.start_color)
  have hez : (cosetGraph d.radical).dist e z=2 := by
    dsimp only [e]
    rw [path.dist_end,path.length_eq_b,hb]
  have hQzSe : Q d.radical z ≤ stabilizer d.radical e :=
    Q_le_stabilizer_of_dist_le_two z e path.end_color back.end_color
      (by rw [SimpleGraph.dist_comm,hez])
  have hWSe : W ≤ stabilizer d.radical e := inf_le_right.trans hQzSe
  have hcent : W ≤ centralizer ((⁅Z d.radical u,Z d.radical e⁆ : Subgroup (FreeAmalgam d.radical)) : Set _) :=
    (hWQu.trans (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes u back.start_color)))).trans
      (centralizer_le (critical_commutator_le_start_seed back))
  have hquad : ⁅⁅A,W⁆,W⁆=⊥ := le_bot_iff.mp
    ((commutator_mono (commutator_mono le_rfl (le_inf hWVu inf_le_right))
      (le_inf hWVu inf_le_right)).trans_eq
        (h.replacement_radius_commutator_bounds d geometry (by omega) back.start_color e z).2)
  refine ⟨hWQu,hWSe,hcent,hquad,?_⟩
  have hvcol : color d.radical v=false := by
    have h₁ := adjacent_color_ne d.radical hut
    have h₂ := adjacent_color_ne d.radical hvt
    rw [back.start_color] at h₁
    cases ht : color d.radical t <;> cases hv : color d.radical v <;> simp_all
  have hASv : A ≤ stabilizer d.radical v := inf_le_right.trans
    (Q_le_stabilizer_of_dist_le_two u v back.start_color hvcol
      (by rw [SimpleGraph.dist_comm]; exact neighbor_distance_le_two hut hvt))
  have hASz : A ≤ stabilizer d.radical z :=
    (inf_le_left.trans (omegaCenter_le (Q d.radical e))).trans
      (Q_le_stabilizer_of_dist_le_two e z back.end_color path.end_color hez.le)
  intro x hx
  apply mem_normalizer_iff_map_conj_eq.mpr
  change W.map (MulAut.conj x).toMonoidHom=W
  dsimp only [W]
  rw [map_inf _ _ _ (MulAut.conj x).injective,MulEquiv.toMonoidHom_eq_coe,
    mem_normalizer_iff_map_conj_eq.mp (U_normalized v (hASv hx)),
    mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical z (hASz hx))]

/-- Failure of the literal source comparison forces field-sized reciprocal
critical images and the full X decomposition at the original middle vertex.
No normality conclusion or new critical pair is assumed. -/
theorem Input.replacement_distance_four_comparison_failure
    {geometry : Geometry d.radical} {a z u v t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hut : Adjacent d.radical u t) (hvt : Adjacent d.radical v t)
    (hbad : ¬ ⁅U d.radical v ⊓ Q d.radical z,Z d.radical (path.walk.getVert 2)⁆ ≤
      ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ ⊔
        ⁅U d.radical v ⊓ Q d.radical z,X d.radical (path.walk.getVert 2) ⊓ Q d.radical u⁆) :
    (Q d.radical (path.walk.getVert 2)).relIndex (Z d.radical u)=Nat.card F ∧
      (Q d.radical u).relIndex (Z d.radical (path.walk.getVert 2))=Nat.card F ∧
      X d.radical a = U d.radical a ⊔
        (X d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) := by
  obtain ⟨_,hWS,hcent,_,_⟩ :=
    h.replacement_distance_four_comparison_actor d path hb back hut hvt
  have hsmall := h.replacement_critical_index_lt_square_of_escape d back (by omega)
    (U d.radical v ⊓ Q d.radical z) hWS hcent (by
      rw [commutator_comm]
      exact fun hh => hbad (hh.trans le_sup_left))
  obtain ⟨hi,hi'⟩ := h.replacement_small_critical_indices_eq_field d back (by omega) hsmall
  refine ⟨hi,hi',?_⟩
  have hsmall' : (Q d.radical u).relIndex (Z d.radical (path.walk.getVert 2)) < Nat.card F^2 := by
    rw [hi']
    have hq : 1 < Nat.card F := Finite.one_lt_card
    nlinarith
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical back.start_color
  obtain ⟨j,hj⟩ := exists_mVertex_of_color d.radical path.start_color
  let y := g⁻¹*j
  have hy : act d.radical y u=a := by
    rw [hg,act_mVertex]
    dsimp only [y]
    rw [mul_inv_cancel_left,←hj]
  have hsmallAct : (Q d.radical (act d.radical y u)).relIndex
      (Z d.radical (act d.radical y (path.walk.getVert 2))) < Nat.card F^2 := by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj y⁻¹).injective]
    exact hsmall'
  have hs := h.replacement_root_X_decomposition_center d (back.act y) (by omega) hsmallAct
  simpa only [hy] using hs

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
