module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.OrbitCore
public import Theory.GroupTheory.CommutatorPreimage

/-!
# Critical commutator layers and the fixed kernel

At either endpoint Z is the product of the moving layer and the common
edge layer. The edge radical centralizes its edge layer, so it displaces Z
inside the moving layer. Thus the original orbit commutator also lies in
the opposite moving layer. Independently, the three-subgroups lemma makes
the component-fixed preimage of A/Zalpha centralize the whole original core.
These are the disjoint-layer and central-kernel steps of MS93 (3.6), p.871.
-/

public noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M]
  {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)
include s

theorem Z_eq_moving_sup_edge_at (h : NativeCentralLayer s)
    {a b : Vertex R} (ha : color R a = false) (hab : Adjacent R a b) :
    Z R a = U R a ⊔ Z R b := by
  obtain ⟨g,hg | hg⟩ := (adjacent_iff_exists_common R a b).mp hab
  · rcases hg with ⟨rfl,rfl⟩
    have he := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom)
      (s.Z_eq_moving_sup_edge h)
    rw [Subgroup.map_sup,←Z_act,←U_act,←Z_act] at he
    simpa only [alpha,beta,act_mVertex,act_hVertex,one_mul] using he
  · rw [hg.1] at ha
    cases ha

omit [Finite M] [L.Normal] [W.Normal] s in
private theorem moving_normalized (a : Vertex R) :
    stabilizer R a ≤ normalizer (U R a : Set (FreeAmalgam R)) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  change (U R a).map (MulAut.conj g).toMonoidHom = U R a
  have hh := U_act R g⁻¹ a
  have hga : act R g⁻¹ a = a := (stabilizer R a).inv_mem hg
  simpa only [hga,inv_inv] using hh.symm

theorem edge_commutator_Z_le_moving (h : NativeCentralLayer s)
    {a b : Vertex R} (ha : color R a = false) (hab : Adjacent R a b) :
    ⁅Q R b,Z R a⁆ ≤ U R a := by
  have hb : color R b = true := by
    have hh := (adjacent_color_ne R hab)
    rw [ha] at hh
    cases he : color R b <;> simp_all
  have hQG : Q R b ≤ stabilizer R a := fun _ hx => hx.2 _ (adjacent_symm R hab)
  have hZGn : Z R a ≤ normalizer (U R a : Set (FreeAmalgam R)) :=
    (Z_le_stabilizer R a).trans (moving_normalized a)
  have hUcomm : ⁅U R a,Q R b⁆ ≤ U R a :=
    le_normalizer_iff_commutator_le_left.mp (hQG.trans (moving_normalized a))
  have hZcomm : ⁅Z R b,Q R b⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    simpa only [Z,hb,Bool.true_eq_false,if_false,edgeOmega] using
      (show omegaCenter (Q R b) ≤ centralizer (Q R b : Set (FreeAmalgam R)) from
        fun _ hx => (mem_omegaCenter_iff.mp hx).2.2)
  have hp : Z R a ≤ commutatorPreimage (Z R a) (Q R b) (U R a) := by
    rw [s.Z_eq_moving_sup_edge_at h ha hab]
    exact sup_le (le_commutatorPreimage le_sup_left hUcomm)
      (le_commutatorPreimage le_sup_right (hZcomm.le.trans bot_le))
  rw [commutator_comm]
  exact (commutator_mono hp le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ hZGn)

theorem criticalOrbit_commutator_le_opposite_moving (h : NativeCentralLayer s) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2) {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b)
    (hne : core R (alpha R) ≠ U R (alpha R)) :
    ⁅Q R (alpha R),criticalOrbit R c b⁆ ≤ U R c := by
  rw [s.criticalOrbit_commutator_eq_plane t hfull hb hc hab hcb hne]
  exact (commutator_mono (Q_le_adjacent_h R (DistanceTwo.NaturalCore.edge_color hab) hab)
    (criticalPlane_le_opposite (R := R) c b)).trans
      (s.edge_commutator_Z_le_moving h (critical_endpoint_color R (alpha R) rfl _ hc) hcb)

theorem criticalOrbit_fixedPreimage_centralizes_core (h : NativeCentralLayer s) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b) :
    ⁅commutatorPreimage (criticalOrbit R c b) (Ltilde R (alpha R)) (Z R (alpha R)),
      core R (alpha R)⁆ = ⊥ := by
  let A := criticalOrbit R c b
  let D := commutatorPreimage A (Ltilde R (alpha R)) (Z R (alpha R))
  have hne : core R (alpha R) ≠ U R (alpha R) := by
    intro he
    apply hlarge
    rw [he]
    exact ((U_le_Z _).trans s.Z_le_X).trans le_sup_right
  have hAQ : A ≤ Q R (alpha R) := (s.criticalOrbit_le_Q_iff hb hc b).mpr
    (s.criticalPlane_le_Q_of_core_ne hb hc hab hcb hne)
  have hDZ : ⁅D,Ltilde R (alpha R)⁆ ≤ Z R (alpha R) :=
    commutator_commutatorPreimage_le _ _ _
      ((hAQ.trans (fun _ hx => hx.1)).trans (Z_normalized R (alpha R)))
  have hDA : D ≤ A := commutatorPreimage_le _ _ _
  have h1 : ⁅⁅D,Ltilde R (alpha R)⁆,A⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact (commutator_mono hDZ hAQ).trans_eq (Z_centralizes_Q R (alpha R) rfl)
  have h2 : ⁅⁅A,D⁆,Ltilde R (alpha R)⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact (commutator_mono (commutator_mono hAQ hDA) le_rfl).trans_eq
      (s.criticalOrbit_commutator_centralizes_residual t hfull hb hc hab hcb hne)
  have he := commutator_commutator_eq_bot_of_rotate h2 h1
  rw [commutator_comm (Ltilde R (alpha R)) A,
    s.criticalOrbit_commutator_eq_core h t hfull hb hlarge hc hab hcb,
    commutator_comm] at he
  exact he

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
