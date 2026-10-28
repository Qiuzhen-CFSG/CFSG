module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.OrbitCore

/-!
# The actual orbit at the opposite critical endpoint

Reverse the original critical pair and use a representative of the common
edge to move its new initial vertex back to the source vertex. Conjugating
the already constructed native critical orbit then supplies the opposite
orbit with its literal plane, core, normalization and commutator markings.
All properties use the same Source and the same original S6 projection;
there is no additional second local-group or module-model hypothesis.

Source: MS93 (3.6), the two orbits Ralpha and Ralpha-prime on printed p.871.
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

/-- Rebase the reversed critical pair at its specified common edge. -/
theorem exists_reversed_critical_coordinates (hb : s.geometry.b R = 2)
    {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b) :
    ∃ (g : FreeAmalgam R) (d : Vertex R),
      act R g (alpha R) = c ∧ act R g d = alpha R ∧ act R g (beta R) = b ∧
      CriticalPair R (alpha R) d (s.geometry.exists_critical (alpha R) rfl) ∧
      Adjacent R d (beta R) := by
  have hc0 := critical_endpoint_color R (alpha R) rfl _ hc
  obtain ⟨g,hg | hg⟩ := (adjacent_iff_exists_common R c b).mp hcb
  · rcases hg with ⟨rfl,rfl⟩
    let d := act R g⁻¹ (alpha R)
    have hga : act R g (alpha R) = mVertex R g := by simp [alpha]
    have hgb : act R g (beta R) = hVertex R g := by simp [beta]
    have hgd : act R g d = alpha R := by
      dsimp only [d]
      rw [←act_mul,inv_mul_cancel,act_one]
    have hback : act R g⁻¹ (mVertex R g) = alpha R := by simp [alpha]
    have hrev := critical_reverse R s.geometry s.edgeCentralizerCondition
      (alpha R) rfl (by change 0 < s.geometry.b R; omega) (mVertex R g) hc0 hc
    have he : ∃n, CriticalRadius R (act R g⁻¹ (mVertex R g)) n := by
      rw [hback]
      exact s.geometry.exists_critical (alpha R) rfl
    have hcrit := (criticalPair_act_iff R g⁻¹ (mVertex R g) (alpha R)
      (s.geometry.exists_critical (mVertex R g) hc0) he).mpr hrev
    have hcrit' : CriticalPair R (alpha R) d (s.geometry.exists_critical (alpha R) rfl) := by
      simpa only [hback] using hcrit
    refine ⟨g,d,hga,hgd,hgb,hcrit',?_⟩
    have hh := (adjacent_act_iff R g d (beta R)).mp
      (by rw [hgd,hgb];exact hab)
    exact hh
  · rw [hg.1] at hc0
    cases hc0

/-- The genuine orbit at the opposite endpoint, with literal graph markings. -/
theorem exists_opposite_criticalOrbit (h : NativeCentralLayer s) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b) :
    ∃ B : Subgroup (FreeAmalgam R),
      Z R c ≤ B ∧ (Z R (alpha R) ⊓ Q R c) ≤ B ∧ core R c ≤ B ∧
      B ≤ Q R c ∧ stabilizer R c ≤ normalizer (B : Set (FreeAmalgam R)) ∧
      ⁅Q R c,B⁆ ≤ Z R b ∧ ⁅⁅Q R c,B⁆,Ltilde R c⁆ = ⊥ ∧
      ⁅B,Ltilde R c⁆ = core R c := by
  have hab0 : Adjacent R (alpha R) (beta R) := base_adjacent R
  have hne : core R (alpha R) ≠ U R (alpha R) := by
    intro he
    apply hlarge
    rw [he]
    exact ((U_le_Z _).trans s.Z_le_X).trans le_sup_right
  obtain ⟨g,d,hga,hgd,hgb,hd,hdb⟩ := s.exists_reversed_critical_coordinates hb hc hab hcb
  let f := (MulAut.conj g⁻¹).toMonoidHom
  let B := (criticalOrbit R d (beta R)).map f
  have hQa : (Q R (alpha R)).map f = Q R c := by rw [←Q_act,hga]
  have hZa : (Z R (alpha R)).map f = Z R c := by rw [←Z_act,hga]
  have hZd : (Z R d).map f = Z R (alpha R) := by rw [←Z_act,hgd]
  have hZb : (Z R (beta R)).map f = Z R b := by rw [←Z_act,hgb]
  have hLa : (Ltilde R (alpha R)).map f = Ltilde R c := by rw [←Ltilde_act,hga]
  have hCa : (core R (alpha R)).map f = core R c := by rw [←core_act,hga]
  have hSa : (stabilizer R (alpha R)).map f = stabilizer R c := by rw [←stabilizer_act,hga]
  refine ⟨B,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [←hZa]
    exact map_mono (s.Z_le_criticalOrbit hb hd hab0 hdb)
  · have hp := s.criticalPlane_eq_opposite_inf_Q h t hfull hb hlarge hd hab0 hdb
    have hh := map_mono (f := f) (s.criticalPlane_le_orbit hb hd (beta R))
    rw [hp,Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective,hZd,hQa] at hh
    exact hh
  · rw [←hCa]
    exact map_mono (s.core_le_criticalOrbit h t hfull hb hlarge hd hab0 hdb)
  · rw [←hQa]
    exact map_mono ((s.criticalOrbit_le_Q_iff hb hd (beta R)).mpr
      (s.criticalPlane_le_Q_of_core_ne hb hd hab0 hdb hne))
  · rw [←hSa]
    exact (map_mono (criticalOrbit_normalized (R := R) d (beta R))).trans (le_normalizer_map f)
  · have hh := map_mono (f := f)
      (s.criticalOrbit_commutator_le_edge_Z t hfull hb hd hab0 hdb hne)
    rw [map_commutator,hQa,hZb] at hh
    exact hh
  · have hh := congrArg (Subgroup.map f)
      (s.criticalOrbit_commutator_centralizes_residual t hfull hb hd hab0 hdb hne)
    rw [map_commutator,map_commutator,hQa,hLa,Subgroup.map_bot] at hh
    exact hh
  · have hh := congrArg (Subgroup.map f)
      (s.criticalOrbit_commutator_eq_core h t hfull hb hlarge hd hab0 hdb)
    rw [map_commutator,hLa,hCa] at hh
    exact hh

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
