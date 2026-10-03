module

public import Stellmacher.PushingUp.ShiftSharedSylow

/-!
# Normality after containing the shifted vertex stabilizer

For the distance-two shift `(a,a′,c,u)`, choose `t ∈ G_u` such that
`Z_c`, its conjugate `Z_(tc)`, and `Q_u` generate `G_u`. Let `V ≤ Q_a` be
normal in `G_a` and contain both `Z_a` and `Z_u`. If `V ≤ G_(tc)`, then
both `V` and `Z_a ⊔ Z_u` are contained and normal in `G_u`. This is the
first assertion in step (3) of the proof of Stellmacher, *Pushing up*
(1986), (2.4), conditional on the transformed-stabilizer containment supplied
by step (2).

Transport the shifted critical pair `(u,c)` along `t`. Its reverse pair gives
the Sylow supplement `Z_u Q_(tc)`; since `V` is a 2-group containing `Z_u`,
Sylow maximality places `V` in that supplement. The source commutator adapter
then gives `[V,Z_(tc)] ≤ Z_u`. The shared edge core is `Z_c Q_u` and lies in
both `G_a` and `G_u`; hence it normalizes `V` and the join of vertex centers.
The commutator bound supplies normalization by `Z_(tc)`, and generation of
`G_u` proves both normalities. No abelianness assumption on `V` is needed.
-/

namespace Stellmacher.PushingUp

open AmalgamGraph

universe u

variable {M : Type u} [Group M] [Finite M]

private theorem kernel_eq_core_of_orbit
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (x : Vertex S) (hx : InMVertexOrbit S x) :
    neighborhoodKernel S x = vertexTwoCore S x := by
  obtain ⟨g, rfl⟩ := hx
  exact mVertex_neighborhoodKernel_eq_twoCore S T hTS _ _ ⟨g, rfl⟩
    ((adjacent_act_iff S g _ _).2 (base_adjacent S))

private theorem criticalPair_act_of_fixed_left
    (S : Subgroup M) (T : Sylow 2 M)
    (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (u c : Vertex S) (hcrit : IsCriticalPair S u c)
    (hb : 0 < criticalDistance S)
    (t : FreeAmalgam S) (ht : t ∈ stabilizer S u) :
    IsCriticalPair S u (act S t c) := by
  have hc := (criticalPair_path T hTS hP hSne u c hcrit hb).opposite_inMVertexOrbit
  have hct : InMVertexOrbit S (act S t c) := by
    obtain ⟨g, rfl⟩ := hc
    exact ⟨g * t, by rw [act_mul]⟩
  refine ⟨hcrit.1, ?_, ?_⟩
  · have hdist := cosetGraph_dist_act S t u c
    rw [show act S t u = u from ht] at hdist
    exact hdist.trans hcrit.2.1
  · intro hle
    rw [kernel_eq_core_of_orbit S T hTS _ hct, vertexTwoCore_act_eq_map] at hle
    have hZuMap : (vertexZ S u).map (MulAut.conj t⁻¹).toMonoidHom = vertexZ S u := by
      rw [← vertexZ_act_eq_map, show act S t u = u from ht]
    rw [← hZuMap] at hle
    have hcore := (Subgroup.map_le_map_iff_of_injective (MulAut.conj t⁻¹).injective).mp hle
    apply hcrit.2.2
    rwa [kernel_eq_core_of_orbit S T hTS _ hc]

/-- Transformed-stabilizer containment yields both source step-(3) normalities. -/
public theorem shift_subgroup_and_centerJoin_normal
    (S : Subgroup M) (T : Sylow 2 M)
    (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two
      ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M)))
    (a a' c u : Vertex S) (hcrit : IsCriticalPair S a a')
    (hb : 6 ≤ criticalDistance S)
    (hframe : DistanceTwoShift.Frame S a a' c)
    (hshift : DistanceTwoShift.Conclusion S a a' c u)
    (t : FreeAmalgam S) (ht : t ∈ stabilizer S u)
    (hgen : vertexZ S c ⊔ (vertexZ S c).map (MulAut.conj t⁻¹).toMonoidHom ⊔
      vertexTwoCore S u = stabilizer S u)
    (V : Subgroup (FreeAmalgam S)) (hVQa : V ≤ vertexTwoCore S a)
    (hVnormal : (V.subgroupOf (stabilizer S a)).Normal)
    (hZaV : vertexZ S a ≤ V) (hZuV : vertexZ S u ≤ V)
    (hVGct : V ≤ stabilizer S (act S t c)) :
    V ≤ stabilizer S u ∧ (V.subgroupOf (stabilizer S u)).Normal ∧
      vertexZ S a ⊔ vertexZ S u ≤ stabilizer S u ∧
      ((vertexZ S a ⊔ vertexZ S u).subgroupOf (stabilizer S u)).Normal := by
  have hbpos : 0 < criticalDistance S := by omega
  have htwo : 2 < criticalDistance S := by omega
  let ct := act S t c
  let E := edgeTwoCore S u a
  let W := vertexZ S a ⊔ vertexZ S u
  have hshared := distanceTwoShift_sharedSylow S T hTS hP hSne hA a a' c u
    hcrit htwo hframe hshift
  have hEinf : E ≤ stabilizer S u ⊓ stabilizer S a := Subgroup.map_subtype_le _
  have hQaGu : vertexTwoCore S a ≤ stabilizer S u := by
    rw [← hshared.2] at hshared
    exact hshared.1.trans (hEinf.trans inf_le_left)
  have hVGu := hVQa.trans hQaGu
  have hWGu : W ≤ stabilizer S u := (sup_le hZaV hZuV).trans hVGu
  have hVGa : V ≤ stabilizer S a := hVQa.trans (Subgroup.map_subtype_le _)
  have hEgen : E ⊔ vertexZ S ct = stabilizer S u := by
    change edgeTwoCore S u a ⊔ vertexZ S (act S t c) = stabilizer S u
    rw [hshared.2, vertexZ_act_eq_map]
    simpa [sup_assoc, sup_left_comm, sup_comm] using hgen
  have hctCrit : IsCriticalPair S u ct :=
    criticalPair_act_of_fixed_left S T hTS hP hSne u c hshift.shifted_critical hbpos t ht
  obtain ⟨hVu, hctGu, hinputs⟩ :=
    criticalPair_actionInputs S T hTS hP hSne hA u ct hctCrit hbpos
  obtain ⟨hVct, huGct, hreverse⟩ := criticalPair_sl2Two S T hTS hP hSne hA ct u
    hinputs.critical.reverse_critical hbpos
  have hVtwo : IsPGroup 2 V :=
    ((pCore_isPGroup (p := 2) (G := stabilizer S a)).map (stabilizer S a).subtype).to_le hVQa
  have hVsource : V ≤ vertexZ S u ⊔ vertexTwoCore S ct :=
    le_reverse_sourceSylow S u ct V hVGct hVtwo hZuV hreverse.sourceSylow
  have hcomm : ⁅V, vertexZ S ct⁆ ≤ vertexZ S u :=
    neighborClosure_commutator_le S u ct V hVGct hVsource hinputs
  have hGaNV : stabilizer S a ≤ Subgroup.normalizer (V : Set (FreeAmalgam S)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVGa).mp hVnormal
  have hZctNV : vertexZ S ct ≤ Subgroup.normalizer (V : Set (FreeAmalgam S)) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr (hcomm.trans hZuV)
  have hGuNV : stabilizer S u ≤ Subgroup.normalizer (V : Set (FreeAmalgam S)) := by
    rw [← hEgen]
    exact sup_le ((hEinf.trans inf_le_right).trans hGaNV) hZctNV
  have hGaNZa : stabilizer S a ≤ Subgroup.normalizer (vertexZ S a : Set (FreeAmalgam S)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (vertexZ_le_stabilizer S a)).mp
      (vertexZ_normal_stabilizer S a)
  have hGuNZu : stabilizer S u ≤ Subgroup.normalizer (vertexZ S u : Set (FreeAmalgam S)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (vertexZ_le_stabilizer S u)).mp
      (vertexZ_normal_stabilizer S u)
  have hENW : E ≤ Subgroup.normalizer (W : Set (FreeAmalgam S)) :=
    (le_inf ((hEinf.trans inf_le_right).trans hGaNZa)
      ((hEinf.trans inf_le_left).trans hGuNZu)).trans
        (Subgroup.normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hZctNW : vertexZ S ct ≤ Subgroup.normalizer (W : Set (FreeAmalgam S)) := by
    apply Subgroup.le_normalizer_iff_commutator_le_left.mpr
    exact (Subgroup.commutator_mono (sup_le hZaV hZuV) le_rfl).trans
      (hcomm.trans le_sup_right)
  have hGuNW : stabilizer S u ≤ Subgroup.normalizer (W : Set (FreeAmalgam S)) := by
    rw [← hEgen]
    exact sup_le hENW hZctNW
  exact ⟨hVGu, (Subgroup.normal_subgroupOf_iff_le_normalizer hVGu).mpr hGuNV,
    hWGu, (Subgroup.normal_subgroupOf_iff_le_normalizer hWGu).mpr hGuNW⟩

end Stellmacher.PushingUp
