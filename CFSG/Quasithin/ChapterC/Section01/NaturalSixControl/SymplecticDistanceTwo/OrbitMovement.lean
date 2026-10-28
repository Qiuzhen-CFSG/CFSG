module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.OrbitFixedKernel
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.OrbitKernel
public import Theory.GroupTheory.Commutator.ResidualMovementModulo
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.CriticalPlane.FullMovement

/-!
# Full movement and the corrected fixed kernel of the critical orbit

Full point-core image gives Y=[A,Zc]Zedge. Its normal orbit is therefore fully
moved by the vertex group modulo Zalpha. The finite two-group supplement can
be removed, leaving A=[A,Lalpha]Zalpha. The previously established three-
subgroups bound then makes the genuine fixed preimage D central in A.
The generating plane escapes D by nontrivial component movement. Finally,
the full edge image acts nontrivially on that plane, since its edge-fixed
subgroup is the strictly smaller Zedge.

This supplies the group-theoretic inputs to the actual A/D transitivity
contradiction in MS93 (3.6), printed p.871. Full orbit image is retained for
the active strict-offender recognition producer; no splitting is assumed.
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

theorem criticalOrbit_eq_commutator_sup_Z_of_moved_plane
    (hb : s.geometry.b R = 2) {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b)
    (hne : core R (alpha R) ≠ U R (alpha R))
    (hY : criticalPlane R c b ≤
      ⁅criticalOrbit R c b,stabilizer R (alpha R)⁆ ⊔ Z R (alpha R)) :
    criticalOrbit R c b = ⁅criticalOrbit R c b,Ltilde R (alpha R)⁆ ⊔ Z R (alpha R) := by
  let A := criticalOrbitNative R c b
  let Z0 := orbitLayer R
  have hZmap : Z0.map (embedM R) = Z R (alpha R) := by
    change ((Z R (alpha R)).comap (embedM R)).map (embedM R) = _
    rw [map_comap_eq,inf_eq_right.mpr]
    exact (Z_le_stabilizer R (alpha R)).trans_eq (stabilizer_m_base R)
  have hGa : (⊤ : Subgroup M).map (embedM R) = stabilizer R (alpha R) := by
    rw [←MonoidHom.range_eq_map]
    exact (stabilizer_m_base R).symm
  let N := ⁅A,⊤⁆ ⊔ Z0
  have hNmap : N.map (embedM R) =
      ⁅criticalOrbit R c b,stabilizer R (alpha R)⁆ ⊔ Z R (alpha R) := by
    rw [Subgroup.map_sup,map_commutator,hGa,hZmap]
    rfl
  have hfullmove : A ≤ ⁅A,⊤⁆ ⊔ Z0 := by
    apply normalClosure_le_normal
    intro y hy
    have hh : embedM R y ∈ N.map (embedM R) := hNmap.symm ▸ hY hy
    obtain ⟨z,hz,he⟩ := hh
    exact embedM_injective R he ▸ hz
  have hAp : IsPGroup 2 A := (pCore_isPGroup (p := 2) (G := M)).of_injective
    (inclusion (s.criticalOrbitNative_le_core_of_core_ne hb hc hab hcb hne)) (inclusion_injective _)
  have hle := normal_p_subgroup_moved_modulo_supplement A L R Z0 hAp s.two_group s.sup_eq_top hfullmove
  have hg := map_mono (f := embedM R) hle
  rw [Subgroup.map_sup,map_commutator,hZmap,←s.residual,←Ltilde_alpha] at hg
  apply le_antisymm hg
  exact sup_le (le_normalizer_iff_commutator_le_left.mp
    ((Ltilde_le_stabilizer (alpha R)).trans (criticalOrbit_normalized c b)))
    (s.Z_le_criticalOrbit hb hc hab hcb)

theorem criticalOrbit_eq_commutator_sup_Z_of_plane_movement
    (hb : s.geometry.b R = 2) {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b)
    (hne : core R (alpha R) ≠ U R (alpha R))
    (hY : ⁅criticalOrbit R c b,Z R c⁆ ⊔ Z R b = criticalPlane R c b) :
    criticalOrbit R c b = ⁅criticalOrbit R c b,Ltilde R (alpha R)⁆ ⊔ Z R (alpha R) := by
  apply s.criticalOrbit_eq_commutator_sup_Z_of_moved_plane hb hc hab hcb hne
  rw [←hY]
  apply sup_le_sup
  · exact commutator_mono le_rfl (critical_Z_le_stabilizer R s.geometry (alpha R) rfl
      (by change 0 < s.geometry.b R;omega) hc)
  · simpa only [Z,show color R (alpha R) = false from rfl,
      DistanceTwo.NaturalCore.edge_color hab,Bool.true_eq_false,if_true,if_false]
      using (le_iSup_of_le b (le_iSup_of_le hab (le_refl (edgeOmega R b))) :
        edgeOmega R b ≤ ⨆ u,⨆ (_ : Adjacent R (alpha R) u),edgeOmega R u)

/-- Full point-core image supplies the actual residual movement of A/Zalpha. -/
theorem criticalOrbit_eq_commutator_sup_Z_of_full_image
    (h : NativeCentralLayer s) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b)
    (himage : criticalOrbit R c b ⊔ Q R c = Q R b) :
    criticalOrbit R c b = ⁅criticalOrbit R c b,Ltilde R (alpha R)⁆ ⊔ Z R (alpha R) := by
  have hne : core R (alpha R) ≠ U R (alpha R) := by
    intro he
    apply hlarge
    rw [he]
    exact ((U_le_Z _).trans s.Z_le_X).trans le_sup_right
  exact s.criticalOrbit_eq_commutator_sup_Z_of_plane_movement hb hc hab hcb hne
    (s.criticalOrbit_opposite_commutator_sup_edge_eq_plane h t hfull hb hlarge hc hab hcb himage)

theorem criticalOrbit_fixedPreimage_centralizes_of_full_image
    (h : NativeCentralLayer s) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b)
    (himage : criticalOrbit R c b ⊔ Q R c = Q R b) :
    commutatorPreimage (criticalOrbit R c b) (Ltilde R (alpha R)) (Z R (alpha R)) ≤
      centralizer (criticalOrbit R c b : Set (FreeAmalgam R)) := by
  let D := commutatorPreimage (criticalOrbit R c b) (Ltilde R (alpha R)) (Z R (alpha R))
  have hne : core R (alpha R) ≠ U R (alpha R) := by
    intro he
    apply hlarge
    rw [he]
    exact ((U_le_Z _).trans s.Z_le_X).trans le_sup_right
  have hAQ := (s.criticalOrbit_le_Q_iff hb hc b).mpr
    (s.criticalPlane_le_Q_of_core_ne hb hc hab hcb hne)
  have hDcore : D ≤ centralizer (core R (alpha R) : Set (FreeAmalgam R)) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (s.criticalOrbit_fixedPreimage_centralizes_core h t hfull hb hlarge hc hab hcb)
  have hDZ : D ≤ centralizer (Z R (alpha R) : Set (FreeAmalgam R)) :=
    ((commutatorPreimage_le _ _ _).trans hAQ).trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q R (alpha R) rfl)))
  apply le_centralizer_iff.mpr
  have he := s.criticalOrbit_eq_commutator_sup_Z_of_full_image h t hfull hb hlarge hc hab hcb himage
  rw [s.criticalOrbit_commutator_eq_core h t hfull hb hlarge hc hab hcb] at he
  exact he.le.trans (sup_le (le_centralizer_iff.mp hDcore) (le_centralizer_iff.mp hDZ))

theorem orbitFixedKernel_centralizes_of_full_image
    (h : NativeCentralLayer s) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b)
    (himage : criticalOrbit R c b ⊔ Q R c = Q R b) :
    orbitFixedKernel L R c b ≤ centralizer (criticalOrbitNative R c b : Set M) := by
  have hZmap : (orbitLayer R).map (embedM R) = Z R (alpha R) := by
    rw [orbitLayer,map_comap_eq]
    exact inf_eq_right.mpr ((Z_le_stabilizer R (alpha R)).trans_eq (stabilizer_m_base R))
  have hLmap : L.map (embedM R) = Ltilde R (alpha R) := by rw [Ltilde_alpha,s.residual]
  have hDmap : (orbitFixedKernel L R c b).map (embedM R) ≤
      commutatorPreimage (criticalOrbit R c b) (Ltilde R (alpha R)) (Z R (alpha R)) := by
    apply le_commutatorPreimage
    · exact map_mono (orbitFixedKernel_le L R c b)
    · have hh := map_mono (f := embedM R)
        (commutator_commutatorPreimage_le (criticalOrbitNative R c b) L (orbitLayer R)
          le_normalizer_of_normal)
      rw [map_commutator,hZmap,hLmap] at hh
      exact hh
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply (map_injective (embedM_injective R))
  rw [map_commutator,Subgroup.map_bot]
  exact commutator_eq_bot_iff_le_centralizer.mpr (hDmap.trans
    (s.criticalOrbit_fixedPreimage_centralizes_of_full_image h t hfull hb hlarge hc hab hcb himage))

/-- The generating plane escapes the corrected fixed kernel, since otherwise
its normal orbit would have trivial component movement modulo Zalpha. -/
theorem criticalPlane_not_le_orbitFixedKernel
    (h : NativeCentralLayer s) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b) :
    ¬ (criticalPlane R c b).comap (embedM R) ≤ orbitFixedKernel L R c b := by
  intro hy
  have hA : criticalOrbitNative R c b ≤ orbitFixedKernel L R c b :=
    normalClosure_le_normal (fun _ hx => hy hx)
  have hcomm : ⁅criticalOrbitNative R c b,L⁆ ≤ orbitLayer R :=
    (commutator_mono hA le_rfl).trans (commutator_commutatorPreimage_le
      (criticalOrbitNative R c b) L (orbitLayer R) le_normalizer_of_normal)
  have hg := map_mono (f := embedM R) hcomm
  rw [map_commutator,orbitLayer,map_comap_eq] at hg
  have hLmap : L.map (embedM R) = Ltilde R (alpha R) := by rw [Ltilde_alpha,s.residual]
  rw [hLmap] at hg
  exact s.criticalOrbit_commutator_not_le_Z h t hfull hb hlarge hc hab hcb (hg.trans inf_le_right)

/-- The full orbit image acts nontrivially on its elementary seed. -/
theorem criticalOrbit_plane_commutator_ne_bot_of_full_image
    (h : NativeCentralLayer s) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b)
    (himage : criticalOrbit R c b ⊔ Q R c = Q R b) :
    ⁅criticalOrbit R c b,criticalPlane R c b⁆ ≠ ⊥ := by
  intro he
  have hA : criticalOrbit R c b ≤ centralizer (criticalPlane R c b : Set (FreeAmalgam R)) :=
    commutator_eq_bot_iff_le_centralizer.mp he
  have hQ : Q R c ≤ centralizer (criticalPlane R c b : Set (FreeAmalgam R)) :=
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q R c (critical_endpoint_color R (alpha R) rfl _ hc)))).trans
        (centralizer_le (criticalPlane_le_opposite c b))
  have hB : Q R b ≤ centralizer (criticalPlane R c b : Set (FreeAmalgam R)) :=
    himage ▸ sup_le hA hQ
  have hY : criticalPlane R c b ≤ Z R b := by
    rw [←s.criticalPlane_inf_edge_centralizer hb hc hab hcb]
    exact le_inf le_rfl (le_centralizer_iff.mp hB)
  exact (not_le_of_gt (s.criticalPlane_edge_strict h t hfull hb hlarge hc hab hcb)) hY

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
