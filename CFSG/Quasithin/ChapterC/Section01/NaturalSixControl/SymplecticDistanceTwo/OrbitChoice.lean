module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.OrbitComparison
public import Mathlib.Order.WellFounded
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.OrbitFrattini

/-!
# Choosing the favorable pair of genuine critical orbits

Choose a critical pair minimizing the image of its native orbit modulo the
opposite kernel. Reversing and rebasing this pair gives the opposite orbit
with at least as large an image. The actual factor-two fixed-index estimate
then becomes a strict offender inequality. This justifies the without-loss
comparison in MS93 (3.6), printed p.871, with no orientation hypothesis.
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

private theorem opposite_orbit_of_minimal (h : NativeCentralLayer s) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b)
    (hmin : ∀ d e, CriticalPair R (alpha R) d (s.geometry.exists_critical (alpha R) rfl) →
      Adjacent R (alpha R) e → Adjacent R d e →
      (Q R c).relIndex (criticalOrbit R c b) ≤ (Q R d).relIndex (criticalOrbit R d e)) :
    ∃ B : Subgroup (FreeAmalgam R),
      Z R c ≤ B ∧ (Z R (alpha R) ⊓ Q R c) ≤ B ∧ core R c ≤ B ∧
      B ≤ Q R c ∧ stabilizer R c ≤ normalizer (B : Set (FreeAmalgam R)) ∧
      ⁅Q R c,B⁆ ≤ Z R b ∧ ⁅⁅Q R c,B⁆,Ltilde R c⁆ = ⊥ ∧
      ⁅B,Ltilde R c⁆ = core R c ∧
      (Q R c).relIndex (criticalOrbit R c b) ≤ (Q R (alpha R)).relIndex B ∧
      (frattini B).map B.subtype ≤ U R (alpha R) := by
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
  refine ⟨B,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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

  · have hQd : (Q R d).map f = Q R (alpha R) := by rw [←Q_act,hgd]
    change _ ≤ (Q R (alpha R)).relIndex ((criticalOrbit R d (beta R)).map f)
    rw [←hQd,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact hmin d (beta R) hd hab0 hdb
  · change (frattini ((criticalOrbit R d (beta R)).map f)).map
      ((criticalOrbit R d (beta R)).map f).subtype ≤ _
    rw [frattini_image_map _ _ (MulAut.conj g⁻¹).injective]
    have hu : (U R d).map f = U R (alpha R) := by rw [←U_act,hgd]
    rw [←hu]
    exact map_mono ((s.criticalOrbit_frattini_le_commutator hb hd hab0 hdb hne).trans
      (s.criticalOrbit_commutator_le_opposite_moving h t hfull hb hd hab0 hdb hne))

/-- A minimal critical orbit supplies the favorable comparison with its genuine
opposite orbit, and hence the strict fixed-index inequality. -/
theorem exists_strict_offending_criticalOrbit (h : NativeCentralLayer s) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R)) :
    ∃ (c b : Vertex R) (B : Subgroup (FreeAmalgam R)),
      CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl) ∧
      Adjacent R (alpha R) b ∧ Adjacent R c b ∧
      Z R c ≤ B ∧ (Z R (alpha R) ⊓ Q R c) ≤ B ∧ core R c ≤ B ∧
      B ≤ Q R c ∧ stabilizer R c ≤ normalizer (B : Set (FreeAmalgam R)) ∧
      ⁅Q R c,B⁆ ≤ Z R b ∧ ⁅⁅Q R c,B⁆,Ltilde R c⁆ = ⊥ ∧
      ⁅B,Ltilde R c⁆ = core R c ∧
      2 * (commutatorPreimage (criticalOrbit R c b) B (Z R (alpha R))).relIndex
        (criticalOrbit R c b) ≤ (Q R (alpha R)).relIndex B := by
  let P := {p : Vertex R × Vertex R //
    CriticalPair R (alpha R) p.1 (s.geometry.exists_critical (alpha R) rfl) ∧
    Adjacent R (alpha R) p.2 ∧ Adjacent R p.1 p.2}
  have : Nonempty P := by
    obtain ⟨c,hc⟩ := criticalPair_exists R (alpha R) (s.geometry.exists_critical (alpha R) rfl)
    obtain ⟨b,hab,hcb⟩ := exists_common_neighbor_of_dist_two R (alpha R) c (hc.1.trans hb)
    exact ⟨⟨(c,b),hc,hab,hcb⟩⟩
  let f : P → ℕ := fun p => (Q R p.val.1).relIndex (criticalOrbit R p.val.1 p.val.2)
  let p := Function.argmin f
  obtain ⟨hc,hab,hcb⟩ := p.property
  have hmin : ∀ d e, CriticalPair R (alpha R) d (s.geometry.exists_critical (alpha R) rfl) →
      Adjacent R (alpha R) e → Adjacent R d e →
      (Q R p.val.1).relIndex (criticalOrbit R p.val.1 p.val.2) ≤
        (Q R d).relIndex (criticalOrbit R d e) := by
    intro d e hd hae hde
    exact Function.argmin_le f ⟨(d,e),hd,hae,hde⟩
  obtain ⟨B,hZ,hP,hC,hBQ,hn,hcomm,hcent,hmove,hcomp,hphi⟩ :=
    s.opposite_orbit_of_minimal h t hfull hb hlarge hc hab hcb hmin
  exact ⟨p.val.1,p.val.2,B,hc,hab,hcb,hZ,hP,hC,hBQ,hn,hcomm,hcent,hmove,
    (s.criticalOrbit_fixed_index_mul_two_le h t hfull hb hlarge hc hab hcb B hBQ hcomm).trans hcomp⟩

/-- Keep both inequalities for the same selected original and opposite orbit.
The lower bound and the favorable comparison separately force both full images. -/
theorem exists_ordered_criticalOrbits (h : NativeCentralLayer s) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R)) :
    ∃ (c b : Vertex R) (B : Subgroup (FreeAmalgam R)),
      CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl) ∧
      Adjacent R (alpha R) b ∧ Adjacent R c b ∧
      Z R c ≤ B ∧ (Z R (alpha R) ⊓ Q R c) ≤ B ∧ core R c ≤ B ∧
      B ≤ Q R c ∧ stabilizer R c ≤ normalizer (B : Set (FreeAmalgam R)) ∧
      ⁅Q R c,B⁆ ≤ Z R b ∧ ⁅⁅Q R c,B⁆,Ltilde R c⁆ = ⊥ ∧
      ⁅B,Ltilde R c⁆ = core R c ∧
      2 * (commutatorPreimage (criticalOrbit R c b) B (Z R (alpha R))).relIndex
        (criticalOrbit R c b) ≤ (Q R c).relIndex (criticalOrbit R c b) ∧
      (Q R c).relIndex (criticalOrbit R c b) ≤ (Q R (alpha R)).relIndex B := by
  let P := {p : Vertex R × Vertex R //
    CriticalPair R (alpha R) p.1 (s.geometry.exists_critical (alpha R) rfl) ∧
    Adjacent R (alpha R) p.2 ∧ Adjacent R p.1 p.2}
  have : Nonempty P := by
    obtain ⟨c,hc⟩ := criticalPair_exists R (alpha R) (s.geometry.exists_critical (alpha R) rfl)
    obtain ⟨b,hab,hcb⟩ := exists_common_neighbor_of_dist_two R (alpha R) c (hc.1.trans hb)
    exact ⟨⟨(c,b),hc,hab,hcb⟩⟩
  let f : P → ℕ := fun p => (Q R p.val.1).relIndex (criticalOrbit R p.val.1 p.val.2)
  let p := Function.argmin f
  obtain ⟨hc,hab,hcb⟩ := p.property
  have hmin : ∀ d e, CriticalPair R (alpha R) d (s.geometry.exists_critical (alpha R) rfl) →
      Adjacent R (alpha R) e → Adjacent R d e →
      (Q R p.val.1).relIndex (criticalOrbit R p.val.1 p.val.2) ≤
        (Q R d).relIndex (criticalOrbit R d e) := by
    intro d e hd hae hde
    exact Function.argmin_le f ⟨(d,e),hd,hae,hde⟩
  obtain ⟨B,hZ,hP,hC,hBQ,hn,hcomm,hcent,hmove,hcomp,hphi⟩ :=
    s.opposite_orbit_of_minimal h t hfull hb hlarge hc hab hcb hmin
  exact ⟨p.val.1,p.val.2,B,hc,hab,hcb,hZ,hP,hC,hBQ,hn,hcomm,hcent,hmove,
    s.criticalOrbit_fixed_index_mul_two_le h t hfull hb hlarge hc hab hcb B hBQ hcomm,hcomp⟩

/-- The same favorable orbits have disjoint Frattini bounds and an elementary
intersection. Thus later kernel arguments need no whole-orbit elementary premise. -/
theorem exists_ordered_elementary_criticalOrbits (h : NativeCentralLayer s) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R)) :
    ∃ (c b : Vertex R) (B : Subgroup (FreeAmalgam R)),
      CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl) ∧
      Adjacent R (alpha R) b ∧ Adjacent R c b ∧
      Z R c ≤ B ∧ (Z R (alpha R) ⊓ Q R c) ≤ B ∧ core R c ≤ B ∧
      B ≤ Q R c ∧ stabilizer R c ≤ normalizer (B : Set (FreeAmalgam R)) ∧
      ⁅Q R c,B⁆ ≤ Z R b ∧ ⁅⁅Q R c,B⁆,Ltilde R c⁆ = ⊥ ∧
      ⁅B,Ltilde R c⁆ = core R c ∧
      2 * (commutatorPreimage (criticalOrbit R c b) B (Z R (alpha R))).relIndex
        (criticalOrbit R c b) ≤ (Q R c).relIndex (criticalOrbit R c b) ∧
      (Q R c).relIndex (criticalOrbit R c b) ≤ (Q R (alpha R)).relIndex B ∧
      (frattini B).map B.subtype ≤ U R (alpha R) ∧
      IsElementaryAbelian 2 (criticalOrbit R c b ⊓ B : Subgroup (FreeAmalgam R)) := by
  let P := {p : Vertex R × Vertex R //
    CriticalPair R (alpha R) p.1 (s.geometry.exists_critical (alpha R) rfl) ∧
    Adjacent R (alpha R) p.2 ∧ Adjacent R p.1 p.2}
  have : Nonempty P := by
    obtain ⟨c,hc⟩ := criticalPair_exists R (alpha R) (s.geometry.exists_critical (alpha R) rfl)
    obtain ⟨b,hab,hcb⟩ := exists_common_neighbor_of_dist_two R (alpha R) c (hc.1.trans hb)
    exact ⟨⟨(c,b),hc,hab,hcb⟩⟩
  let f : P → ℕ := fun p => (Q R p.val.1).relIndex (criticalOrbit R p.val.1 p.val.2)
  let p := Function.argmin f
  obtain ⟨hc,hab,hcb⟩ := p.property
  have hmin : ∀ d e, CriticalPair R (alpha R) d (s.geometry.exists_critical (alpha R) rfl) →
      Adjacent R (alpha R) e → Adjacent R d e →
      (Q R p.val.1).relIndex (criticalOrbit R p.val.1 p.val.2) ≤
        (Q R d).relIndex (criticalOrbit R d e) := by
    intro d e hd hae hde
    exact Function.argmin_le f ⟨(d,e),hd,hae,hde⟩
  obtain ⟨B,hZ,hP,hC,hBQ,hn,hcomm,hcent,hmove,hcomp,hphi⟩ :=
    s.opposite_orbit_of_minimal h t hfull hb hlarge hc hab hcb hmin
  have hne : core R (alpha R) ≠ U R (alpha R) := by
    intro he
    apply hlarge
    rw [he]
    exact ((U_le_Z _).trans s.Z_le_X).trans le_sup_right
  exact ⟨p.val.1,p.val.2,B,hc,hab,hcb,hZ,hP,hC,hBQ,hn,hcomm,hcent,hmove,
    s.criticalOrbit_fixed_index_mul_two_le h t hfull hb hlarge hc hab hcb B hBQ hcomm,
    hcomp,hphi,s.paired_orbit_intersection_elementary h t hfull hb hc hab hcb hne B hBQ hphi⟩

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
