module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.OrbitLarge
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.OrbitEdge
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.CoreGeometry

/-!
# The critical orbit has the seed's commutator with the original core

The native point radical has elementary quotient at either incident original
vertex. Thus the critical orbit commutator lies in the opposite kernel, whose
central layer it centralizes. Critical reversal and the marked A6/S6 projection
then make this normal commutator centralize the original residual. The seed
commutator is normalized by the edge radical and centralized by that residual;
normal closure therefore introduces no additional commutator elements.

The orbit contains the entire original Z-layer because it contains one edge
seed and is normalized by the vertex group. These statements use the actual
finite vertex group and its specified embedding in the amalgam. Source:
Meierfrankenfeld--Stellmacher (1993), (3.6), printed p.871.
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

theorem residual_sup_edge_eq_stabilizer {b : Vertex R}
    (hab : Adjacent R (alpha R) b) :
    Ltilde R (alpha R) ⊔ Q R b = stabilizer R (alpha R) := by
  have hbase : Ltilde R (alpha R) ⊔ Q R (beta R) = stabilizer R (alpha R) := by
    rw [Ltilde_alpha,s.residual,Q_beta,←Subgroup.map_sup,s.sup_eq_top,←MonoidHom.range_eq_map]
    exact (stabilizer_m_base R).symm
  obtain ⟨g,hg,hgb⟩ := stabilizer_transitive_neighbors R (alpha R) (base_adjacent R) hab
  have he := congrArg (fun H : Subgroup (FreeAmalgam R) =>
    H.map (MulAut.conj g⁻¹).toMonoidHom) hbase
  change act R g (alpha R) = alpha R at hg
  change act R g (beta R) = b at hgb
  rw [Subgroup.map_sup,←Ltilde_act,←Q_act,←stabilizer_act,hg,hgb] at he
  exact he

theorem Z_le_criticalOrbit {c b : Vertex R}
    (hb : s.geometry.b R = 2)
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b) :
    Z R (alpha R) ≤ criticalOrbit R c b := by
  have hB := (s.edge_Z_le_criticalPlane hc hab hcb).trans (s.criticalPlane_le_orbit hb hc b)
  rw [Z,if_pos (show color R (alpha R) = false from rfl)]
  apply iSup_le
  intro d
  apply iSup_le
  intro hd
  obtain ⟨g,hg,hgd⟩ := stabilizer_transitive_neighbors R (alpha R) hab hd
  have hAg : (criticalOrbit R c b).map (MulAut.conj g⁻¹).toMonoidHom =
      criticalOrbit R c b := mem_normalizer_iff_map_conj_eq.mp
        (criticalOrbit_normalized (R := R) c b ((stabilizer R (alpha R)).inv_mem hg))
  have he := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hB
  rw [hAg,←Z_act,hgd] at he
  simpa only [Z,DistanceTwo.NaturalCore.edge_color hd,Bool.true_eq_false,if_false] using he

private theorem edge_core_coordinates {c b : Vertex R}
    (hc : color R c = false) (hcb : Adjacent R c b) :
    ∃i : M →* FreeAmalgam R, Function.Injective i ∧
      R.map i = Q R b ∧ (pCore 2 M).map i = Q R c := by
  obtain ⟨g,hg | hg⟩ := (adjacent_iff_exists_common R c b).mp hcb
  · rcases hg with ⟨rfl,rfl⟩
    let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM R)
    refine ⟨i,(MulAut.conj g⁻¹).injective.comp (embedM_injective R),?_,?_⟩
    · have h := Q_act R g (beta R)
      rw [Q_beta] at h
      simpa only [beta,act_hVertex,one_mul,Q_beta,map_map] using h.symm
    · have h := Q_act R g (alpha R)
      rw [Q_alpha R s.two_group s.core_le] at h
      simpa only [alpha,act_mVertex,one_mul,Q_alpha R s.two_group s.core_le,map_map] using h.symm
  · rw [hg.1] at hc
    cases hc

omit [Finite M] in
theorem radical_commutator_le_core_of_pointCore (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom) :
    ⁅R,R⁆ ≤ pCore 2 M := by
  let := pointCore_elementary
  have hAb : IsElementaryAbelian 2 (R.map s.projection) := by
    rw [hfull]
    exact IsElementaryAbelian.map _
  let := hAb
  rw [←s.projection_kernel,←Subgroup.map_eq_bot_iff,map_commutator]
  exact commutator_self_eq_bot_iff.mpr inferInstance

theorem edge_commutator_le_endpoint (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    {c b : Vertex R} (hc : color R c = false) (hcb : Adjacent R c b) :
    ⁅Q R b,Q R b⁆ ≤ Q R c := by
  obtain ⟨i,hi,hiR,hiQ⟩ := s.edge_core_coordinates hc hcb
  rw [←hiR,←hiQ,←map_commutator]
  exact map_mono (s.radical_commutator_le_core_of_pointCore t hfull)

theorem criticalOrbit_commutator_le_opposite_Q (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2) {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b)
    (hne : core R (alpha R) ≠ U R (alpha R)) :
    ⁅Q R (alpha R),criticalOrbit R c b⁆ ≤ Q R c := by
  have hAQ := (s.criticalOrbit_le_Q_iff hb hc b).mpr
    (s.criticalPlane_le_Q_of_core_ne hb hc hab hcb hne)
  have hQb := Q_le_adjacent_h R (DistanceTwo.NaturalCore.edge_color hab) hab
  exact (commutator_mono hQb (hAQ.trans hQb)).trans
    (s.edge_commutator_le_endpoint t hfull
      (critical_endpoint_color R (alpha R) rfl _ hc) hcb)

theorem criticalOrbit_commutator_centralizes_opposite_Z (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2) {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b)
    (hne : core R (alpha R) ≠ U R (alpha R)) :
    ⁅⁅Q R (alpha R),criticalOrbit R c b⁆,Z R c⁆ = ⊥ := by
  apply le_bot_iff.mp
  apply (commutator_mono (s.criticalOrbit_commutator_le_opposite_Q t hfull hb hc hab hcb hne) le_rfl).trans_eq
  rw [commutator_comm]
  exact Z_centralizes_Q R c (critical_endpoint_color R (alpha R) rfl _ hc)

theorem criticalOrbitNative_commutator_centralizes_residual (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2) {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b)
    (hne : core R (alpha R) ≠ U R (alpha R)) :
    ⁅⁅pCore 2 M,criticalOrbitNative R c b⁆,L⁆ = ⊥ := by
  let A := criticalOrbitNative R c b
  let : A.Normal := normalClosure_normal
  let B := ⁅pCore 2 M,A⁆
  let E := (Z R c).comap (embedM R)
  have hc0 := critical_endpoint_color R (alpha R) rfl _ hc
  have hrev := critical_reverse R s.geometry s.edgeCentralizerCondition
    (alpha R) rfl (by change 0 < s.geometry.b R; omega) c hc0 hc
  have hZ : Z R c ≤ (embedM R).range := by
    rw [← show stabilizer R (alpha R) = (embedM R).range from stabilizer_m_base R]
    apply Z_le_stabilizer_of_dist_two R s.geometry c hc0
    · rw [s.geometry.distance_constant c hc0]
      change 0 < s.geometry.b R
      omega
    · rw [SimpleGraph.dist_comm]
      exact hc.1.trans hb
  have hEm : E.map (embedM R) = Z R c :=
    (map_comap_eq _ _).trans (inf_eq_right.mpr hZ)
  have hE : ¬ E ≤ pCore 2 M := by
    intro hh
    apply hrev.2
    rw [←hEm,Q_alpha R s.two_group s.core_le]
    exact map_mono hh
  have hBE : ⁅B,E⁆ = ⊥ := by
    apply (map_eq_bot_iff_of_injective _ (embedM_injective R)).mp
    rw [map_commutator,hEm]
    dsimp only [B]
    rw [map_commutator,←Q_alpha R s.two_group s.core_le]
    exact s.criticalOrbit_commutator_centralizes_opposite_Z t hfull hb hc hab hcb hne
  have hEC : E ≤ centralizer (B : Set M) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hBE)
  have hLC := s.residual_le_of_not_le_core (centralizer (B : Set M))
    (fun hh => hE (hEC.trans hh))
  exact commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mpr hLC)

/-- The actual graph commutator is fixed by its original residual component. -/
theorem criticalOrbit_commutator_centralizes_residual (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2) {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b)
    (hne : core R (alpha R) ≠ U R (alpha R)) :
    ⁅⁅Q R (alpha R),criticalOrbit R c b⁆,Ltilde R (alpha R)⁆ = ⊥ := by
  rw [Q_alpha R s.two_group s.core_le,criticalOrbit,Ltilde_alpha,s.residual,
    ←map_commutator,←map_commutator,
    s.criticalOrbitNative_commutator_centralizes_residual t hfull hb hc hab hcb hne,
    Subgroup.map_bot]

omit s [Finite M] [L.Normal] [W.Normal] in
private theorem normalizes_commutator {G : Type*} [Group G]
    (P A B : Subgroup G) (hA : P ≤ normalizer A) (hB : P ≤ normalizer B) :
    P ≤ normalizer ((⁅A,B⁆ : Subgroup G) : Set G) := by
  intro p hp
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp (hA hp),
    mem_normalizer_iff_map_conj_eq.mp (hB hp)]

/-- The whole orbit has exactly the seed's commutator with the original core. -/
theorem criticalOrbit_commutator_eq_plane (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2) {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b)
    (hne : core R (alpha R) ≠ U R (alpha R)) :
    ⁅Q R (alpha R),criticalOrbit R c b⁆ = ⁅Q R (alpha R),criticalPlane R c b⁆ := by
  let B := ⁅Q R (alpha R),criticalPlane R c b⁆
  have hBbig : B ≤ ⁅Q R (alpha R),criticalOrbit R c b⁆ :=
    commutator_mono le_rfl (s.criticalPlane_le_orbit hb hc b)
  have hBL : ⁅B,Ltilde R (alpha R)⁆ = ⊥ := le_bot_iff.mp
    ((commutator_mono hBbig le_rfl).trans_eq
      (s.criticalOrbit_commutator_centralizes_residual t hfull hb hc hab hcb hne))
  have hbn : stabilizer R (alpha R) ≤ normalizer B := by
    rw [←s.residual_sup_edge_eq_stabilizer hab]
    refine sup_le ?_ ?_
    · exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hBL)).trans
        (Subgroup.centralizer_le_normalizer _)
    · exact normalizes_commutator _ _ _
        ((show Q R b ≤ stabilizer R (alpha R) from
          fun _ hx => hx.2 _ (adjacent_symm R hab)).trans (Q_normalized R (alpha R)))
        (s.criticalPlane_normalized_edge hb hc hab hcb)
  let B0 := B.comap (embedM R)
  let Y := (criticalPlane R c b).comap (embedM R)
  let : B0.Normal := by
    constructor
    intro x hx m
    change embedM R (m*x*m⁻¹) ∈ B
    rw [map_mul,map_mul,map_inv]
    apply le_normalizer_iff.mp hbn _ _ _ hx
    rw [show alpha R = mVertex R 1 from rfl,stabilizer_m_base]
    exact ⟨m,rfl⟩
  have hcomm : ⁅pCore 2 M,Y⁆ ≤ B0 := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator,←Q_alpha R s.two_group s.core_le]
    exact commutator_mono le_rfl (map_comap_le _ _)
  have hn := commutator_normalClosure_le_of_normal (pCore 2 M) Y B0 hcomm
  apply le_antisymm _ hBbig
  have hh := map_mono (f := embedM R) hn
  rw [map_commutator,←Q_alpha R s.two_group s.core_le] at hh
  exact hh.trans (map_comap_le _ _)

/-- Thus the orbit commutator stays in the actual common edge layer. -/
theorem criticalOrbit_commutator_le_edge_Z (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2) {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b)
    (hne : core R (alpha R) ≠ U R (alpha R)) :
    ⁅Q R (alpha R),criticalOrbit R c b⁆ ≤ Z R b := by
  rw [s.criticalOrbit_commutator_eq_plane t hfull hb hc hab hcb hne]
  exact s.criticalPlane_commutator_le hb hc hab hcb

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
