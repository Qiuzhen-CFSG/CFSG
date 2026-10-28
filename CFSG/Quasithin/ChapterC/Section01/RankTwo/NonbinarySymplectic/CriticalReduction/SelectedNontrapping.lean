module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.TrappedRootComparison

/-!
# Nontrapping for a prescribed selected seed

The terminal twist only needs the selected seed to lie in the terminal kernel.
The uniform field-sized bound on neighboring U-indices gives the same literal
terminal intersection and the full-U fixed index of the transformed pair.
The preserved commutator lies in the original critical-root commutator; duality
then forces it to vanish, contrary to its nonfixed action at the endpoint.

Thus every nonnormal selected seed gives a backward critical path under that
uniform bound. RootSelectorCompatibility applies this to the original source
selectors and discharges the bound by the strict-index alternative. The full
central attachment and the actual inverse-conjugation action are retained.
Source: MS93 (5.7)--(5.8), printed pp.919--920.
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The same prescribed nonnormal seed cannot be trapped when all neighboring
full-U indices modulo B are at most the field order. -/
theorem Input.replacement_selected_seed_not_trapped_of_uniform_bound
    {geometry : Geometry d.radical} {a z v w : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (haw : Adjacent d.radical a w) (hvw : Adjacent d.radical v w)
    (hn : ¬ Z d.radical z ≤ normalizer
      ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hbound : ∀ v w c : Vertex d.radical, color d.radical v=false →
      Adjacent d.radical v w → Adjacent d.radical c w →
      (B d.radical v (geometry.Z_normal v)).relIndex (U d.radical c) ≤ Nat.card F) :
    ¬ Z d.radical v ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) := by
  intro htrapv
  obtain ⟨x,hx,htwist,_⟩ := h.replacement_terminal_edge_residual_twist d path hb
  obtain ⟨hmap,hjoin,hfixed,hinv,hcomm,hback⟩ :=
    h.replacement_seed_twist_transport_of_uniform_bound d path hb htrapv hbound x hx
  obtain ⟨hv,hcritical,hcard,hnot⟩ :=
    h.replacement_seed_twisted_critical_pair_of_uniform_bound d path hb haw hvw hn
      htrapv hbound x hx htwist
  obtain ⟨_,hnewC⟩ := h.replacement_critical_moving_index_of_uniform_bound d
    (CriticalPath.ofPair hv hcritical) hb hbound
  let A := U d.radical z ⊓ Q d.radical a
  let D := ⁅Z d.radical v,A⁆
  let z' := act d.radical x z
  let A' := U d.radical z' ⊓ B d.radical (path.walk.getVert (path.walk.length-2)) (geometry.Z_normal _)
  have hYS : Z d.radical v ≤ stabilizer d.radical z' :=
    Z_le_stabilizer_of_dist_le v (geometry.exists_critical v hv) hcritical.1.le
  have hTS : Z d.radical (act d.radical x a) ≤ stabilizer d.radical z' :=
    Z_le_stabilizer_of_dist_le _ (geometry.exists_critical _ (path.act x).start_color)
      (path.act x).critical.1.le
  have hCa := MSCentralOrbit.C_eq_Q d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d) a path.start_color
  have hUS : U d.radical z ≤ stabilizer d.radical a :=
    (U_le_Z z).trans (path.endpoint_Z_le_start_stabilizer (by omega))
  have hfix : A = U d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) := by
    dsimp only [A]
    rw [←hCa]
    ext r
    exact ⟨fun hr => ⟨hr.1,hr.2.2⟩,fun hr => ⟨hr.1,hUS hr.1,hr.2⟩⟩
  have hfix' : A' = U d.radical z' ⊓
      centralizer (Z d.radical (act d.radical x a) : Set (FreeAmalgam d.radical)) := by
    change A.map (MulAut.conj x⁻¹).toMonoidHom=A' at hmap
    rw [←hmap,hfix,←map_inf_centralizer_of_injective _ (MulAut.conj x⁻¹).injective,
      ←U_act,←Z_act]
  have hne : ⁅Z d.radical v,A'⁆ ≠ ⊥ := by
    intro he
    apply hnot
    rw [←hback,hcomm,he]
    exact bot_le
  have hwhole : D=⁅Z d.radical v,U d.radical z'⁆ := by
    change D=⁅Z d.radical v,A'⁆ at hcomm
    refine hcomm.trans ?_
    rw [hfix'] at hne ⊢
    exact h.replacement_field_index_commutator_on_fixed_subgroup d geometry hb
      (by rw [action_preserves_color]; exact path.end_color)
      (Z d.radical v) (Z d.radical (act d.radical x a)) hYS hTS hnewC hne
  have hDmap : D.map (MulAut.conj x).toMonoidHom=D :=
    mem_normalizer_iff_map_conj_eq.mp ((Subgroup.centralizer_le_normalizer _)
      ((le_centralizer_iff.mp hfixed) hx))
  have hwholeBack : D=⁅Z d.radical (act d.radical x⁻¹ v),U d.radical z⁆ := by
    have hh := congrArg (Subgroup.map (MulAut.conj x).toMonoidHom) hwhole
    rw [hDmap,map_commutator] at hh
    have hZmap : (Z d.radical v).map (MulAut.conj x).toMonoidHom =
        Z d.radical (act d.radical x⁻¹ v) := by rw [Z_act d.radical x⁻¹ v,inv_inv]
    have hid : (MulAut.conj x).toMonoidHom.comp (MulAut.conj x⁻¹).toMonoidHom = MonoidHom.id _ := by
      apply MonoidHom.ext
      intro r
      simp [MulAut.conj_apply,mul_assoc]
    change D=⁅(Z d.radical v).map (MulAut.conj x).toMonoidHom,
      (U d.radical (act d.radical x z)).map (MulAut.conj x).toMonoidHom⁆ at hh
    rw [hZmap,U_act,map_map,hid,Subgroup.map_id] at hh
    exact hh
  have hle := h.replacement_trapped_root_commutator_le_critical d path hb haw hvw hn htrapv
  have hYback : Z d.radical (act d.radical x⁻¹ v) ≤ stabilizer d.radical z := by
    have hh := map_mono (f := (MulAut.conj x).toMonoidHom) hYS
    have hZmap : (Z d.radical v).map (MulAut.conj x).toMonoidHom =
        Z d.radical (act d.radical x⁻¹ v) := by rw [Z_act d.radical x⁻¹ v,inv_inv]
    have hSmap : (stabilizer d.radical (act d.radical x z)).map (MulAut.conj x).toMonoidHom =
        stabilizer d.radical z := by
      have hs := stabilizer_act d.radical x⁻¹ (act d.radical x z)
      rw [inv_inv,←act_mul,mul_inv_cancel,act_one] at hs
      exact hs.symm
    change (Z d.radical v).map (MulAut.conj x).toMonoidHom ≤
      (stabilizer d.radical (act d.radical x z)).map (MulAut.conj x).toMonoidHom at hh
    rwa [hZmap,hSmap] at hh
  have hTS' : Z d.radical a ≤ stabilizer d.radical z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
  have hwholeLe : ⁅Z d.radical (act d.radical x⁻¹ v),U d.radical z⁆ ≤
      ⁅Z d.radical a,U d.radical z⁆ := by
    rw [←hwholeBack]
    exact hle
  have hfixBack := h.replacement_moving_fixed_antitone_of_commutator_le d geometry hb path.end_color
    (Z d.radical (act d.radical x⁻¹ v)) (Z d.radical a) hYback hTS' hwholeLe
  have hAC : A ≤ centralizer (Z d.radical (act d.radical x⁻¹ v) : Set (FreeAmalgam d.radical)) := by
    intro r hr
    exact (hfixBack (hfix ▸ hr)).2
  have hz : ⁅Z d.radical (act d.radical x⁻¹ v),A⁆=⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hAC)
  exact hnot (hz ▸ bot_le)

/-- The local nontrapping result supplies the backward path for this very
selector, with the original first edge and every path overlap. -/
theorem Input.replacement_selected_seed_backward_of_uniform_bound
    {geometry : Geometry d.radical} {a z v w : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (haw : Adjacent d.radical a w) (hvw : Adjacent d.radical v w)
    (hn : ¬ Z d.radical z ≤ normalizer
      ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hbound : ∀ v w c : Vertex d.radical, color d.radical v=false →
      Adjacent d.radical v w → Adjacent d.radical c w →
      (B d.radical v (geometry.Z_normal v)).relIndex (U d.radical c) ≤ Nat.card F) :
    ∃ back : CriticalPath d.radical geometry v (path.walk.getVert (path.walk.length-2)),
      back.walk.getVert 1=w ∧
      ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i := by
  exact exists_backward_path_of_not_le geometry (by omega) path haw hvw
    (h.replacement_selected_seed_not_trapped_of_uniform_bound d path hb haw hvw hn hbound)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
