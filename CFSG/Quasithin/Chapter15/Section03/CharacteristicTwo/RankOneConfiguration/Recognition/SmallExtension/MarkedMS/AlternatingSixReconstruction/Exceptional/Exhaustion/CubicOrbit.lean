module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.CubicCriticalLine.Movement
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.Local

/-!
# Critical-plane orbits with the cubic kernel retained

In the cubic initial-kernel branch at distance two, the maximal critical
plane and its entire normal orbit lie in the original two-core. Frattini
detection proves this without replacing the odd extension kernel by that
core. Reversing the critical pair and applying the checked transposition
sign calculation puts the orbit commutator in the opposite two-core.
Normal generation then makes it centralize the original component; the
literal plane commutator is central in the vertex group, so normal closure
preserves its sharper bound in the common edge layer.

The final implication identifies the entire intrinsic core with the orbit's
component commutator once the source intersection bound is supplied. The
three-subgroups lemma then gives exhaustion if this same orbit is elementary
abelian. The intersection and elementary-orbit proofs, larger distances,
and final natural/exceptional assembly remain owned by the reconstruction
task. CubicOrbit.Source applies the implication to the original whole core
and the unchanged rank-two conclusion.

Source: Meierfrankenfeld--Stellmacher (1993), (3.6), pp.870--871;
Aschbacher--Smith C.1.31--32, pp.135--136. The geometric plane and orbit
lemmas are reused from Natural.Exhaustion.DistanceTwo.Geometry.Local.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.CubicAction
open Natural.Exhaustion.DistanceTwo.Geometry
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf (L ⊔ R)
local notation "T" => edge L R

include h hz hk in
/-- The retained cubic action kernel is incompatible with whole-core exhaustion. -/
theorem cubic_not_coreExhaustion (hx : CoreExhaustion L R) : False := by
  have he : extensionKernel h = pCore 2 M := hk.symm.trans (centralOmega_centralizer h hx)
  have hi := extensionKernel_core_index h hz
  have htop : pCore 2 (extensionKernel h) = ⊤ := by
    apply map_injective (extensionKernel h).subtype_injective
    rw [←MonoidHom.range_eq_map,range_subtype]
    exact (extensionKernel_twoCore h).trans he.symm
  rw [htop,index_top] at hi
  norm_num at hi

include h hz hk in
/-- The cubic branch is necessarily the non-Frattini branch of source (3.6). -/
theorem cubic_core_not_le_frattini :
    ¬ core T (alpha T) ≤
      (frattini (Q T (alpha T))).map (Q T (alpha T)).subtype ⊔ X T (alpha T) :=
  fun hx => cubic_not_coreExhaustion h hz hk (coreExhaustion_of_graph_frattini h hx)

include h e hz hk in
/-- An escaping elementary plane would exhaust the whole core; hence the literal
maximal plane lies in the original two-core. -/
theorem critical_plane_le_core (hb : sourceDistance h = 2) {c b : Vertex T}
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical _ rfl))
    (hab : Adjacent T (alpha T) b) (hcb : Adjacent T c b) :
    (criticalPlane T c b).comap (embedM T) ≤ pCore 2 M := by
  let P := (criticalPlane T c b).comap (embedM T)
  let F := (frattini (pCore 2 M)).map (pCore 2 M).subtype ⊔ centralOmega L R
  let : F.Normal := inferInstance
  have hcol := critical_endpoint_color T (alpha T) rfl _ hc
  have hZX := (sourceGeometry h).omega_bound c hcol (by
    rw [(sourceGeometry h).distance_constant c hcol]
    exact sourceDistance_pos h)
  let : IsElementaryAbelian 2 (X T c) := omegaCenter_elementary _
  let : IsElementaryAbelian 2 (criticalPlane T c b) :=
    IsElementaryAbelian.of_le ((criticalPlane_le_opposite c b).trans hZX)
  let : IsElementaryAbelian 2 P :=
    IsElementaryAbelian.comap_of_injective _ (embedM_injective T) _
  have hZb : Z T b ≤ Z T (alpha T) := by
    have hbcol := CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceTwo.NaturalCore.edge_color hab
    simp only [Z,hbcol,Bool.true_eq_false,if_false]
    exact le_iSup_of_le b (le_iSup_of_le hab le_rfl)
  have hPF : ⁅pCore 2 M,P⁆ ≤ F := by
    apply le_trans _ le_sup_right
    apply (map_le_map_iff_of_injective (embedM_injective T)).mp
    rw [map_commutator,←graph_X h,
      ←Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le]
    exact ((commutator_mono le_rfl (map_comap_le _ _)).trans
      (criticalPlane_commutator_le (sourceGeometry h) hb hc hab hcb)).trans
      (hZb.trans ((sourceGeometry h).omega_bound _ rfl (sourceDistance_pos h)))
  have hQQ : ⁅pCore 2 M,pCore 2 M⁆ ≤ F := by
    apply le_trans _ le_sup_left
    let : Fact (IsPGroup 2 (pCore 2 M)) := ⟨pCore_isPGroup⟩
    rw [←map_subtype_commutator]
    exact map_mono (commutator_le_frattini_of_isPGroup (p := 2))
  by_contra hn
  have hcore := core_le_of_two_subgroup_commutator_le h e hz F P hQQ
    (IsElementaryAbelian.isPGroup 2 P) hn hPF
  apply cubic_not_coreExhaustion h hz hk
  exact commutator_eq_of_le_frattini_sup_of_isPPerfect
    (pCore 2 M) K (centralOmega L R) pCore_isPGroup h.relative_twoPerfect
    (fun x hx => ((mem_omegaCenterIn_iff _ _).mp hx).1) hcore

include h e hz hk in
/-- Normal closure keeps the entire critical-plane orbit inside the original two-core. -/
theorem critical_orbit_le_core (hb : sourceDistance h = 2) {c b : Vertex T}
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical _ rfl))
    (hab : Adjacent T (alpha T) b) (hcb : Adjacent T c b) :
    criticalOrbitNative T c b ≤ pCore 2 M :=
  normalClosure_le_normal (critical_plane_le_core h e hz hk hb hc hab hcb)

include h e hz hk in
theorem critical_layer_commutator_le_opposite_core
    (hb : sourceDistance h = 2) (c : Vertex T)
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical _ rfl))
    (A B : Subgroup (FreeAmalgam T))
    (hA : A ≤ stabilizer T c) (hB : B ≤ stabilizer T c)
    (hcomm : ⁅A,B⁆ ≤ X T (alpha T)) : ⁅A,B⁆ ≤ Q T c := by
  have hcCol := critical_endpoint_color T (alpha T) rfl _ hc
  have hr := critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
    (alpha T) rfl (sourceDistance_pos h) c hcCol hc
  obtain ⟨g,hgc⟩ := exists_mVertex_of_color T hcCol
  have hg : act T g⁻¹ c = alpha T := by
    rw [hgc,act_mVertex,mul_inv_cancel]
    rfl
  have hgcCol : color T (act T g⁻¹ c) = false := by rw [hg];rfl
  have hc' := (criticalPair_act_iff T g⁻¹ c (alpha T)
    ((sourceGeometry h).exists_critical c hcCol)
    ((sourceGeometry h).exists_critical (act T g⁻¹ c) hgcCol)).mpr hr
  have hd : CriticalPair T (alpha T) (act T g⁻¹ (alpha T))
      ((sourceGeometry h).exists_critical _ rfl) := by simpa only [hg] using hc'
  let f := (MulAut.conj (g⁻¹)⁻¹).toMonoidHom
  let A' := A.map f
  let B' := B.map f
  have hbase (D : Subgroup (FreeAmalgam T)) (hD : D ≤ stabilizer T c) :
      D.map f ≤ (embedM T).range := by
    have hh := map_mono (f := f) hD
    change D.map f ≤ (stabilizer T c).map (MulAut.conj (g⁻¹)⁻¹).toMonoidHom at hh
    rw [←stabilizer_act,hg] at hh
    exact hh.trans_eq (stabilizer_m_base T)
  have hAm : (A'.comap (embedM T)).map (embedM T) = A' :=
    map_comap_eq_self (hbase A hA)
  have hBm : (B'.comap (embedM T)).map (embedM T) = B' :=
    map_comap_eq_self (hbase B hB)
  have hbound : ⁅A',B'⁆ ≤ X T (act T g⁻¹ (alpha T)) := by
    have hh := map_mono (f := f) hcomm
    rw [map_commutator,←X_act] at hh
    exact hh
  have hh := critical_commutator_le_base_core h e hz hk hb _ hd
    (A'.comap (embedM T)) (B'.comap (embedM T)) (by
      apply map_le_iff_le_comap.mp
      rw [map_commutator,hAm,hBm]
      exact hbound)
  have hm := map_mono (f := embedM T) hh
  rw [map_commutator,hAm,hBm,←Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le] at hm
  apply (map_le_map_iff_of_injective (f := f) (MulAut.conj (g⁻¹)⁻¹).injective).mp
  rw [map_commutator,←Q_act,hg]
  exact hm

include h e hz hk in
theorem orbit_commutator_centralizes_component
    (hb : sourceDistance h = 2) {c b : Vertex T}
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical _ rfl))
    (hab : Adjacent T (alpha T) b) (hcb : Adjacent T c b) :
    ⁅⁅pCore 2 M,criticalOrbitNative T c b⁆,K⁆ = ⊥ := by
  let A := criticalOrbitNative T c b
  let : A.Normal := normalClosure_normal
  let B := ⁅pCore 2 M,A⁆
  let E := (Z T c).comap (embedM T)
  have hcCol := critical_endpoint_color T (alpha T) rfl _ hc
  have hr := critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
    (alpha T) rfl (sourceDistance_pos h) c hcCol hc
  have hZX := (sourceGeometry h).omega_bound c hcCol (by
    rw [(sourceGeometry h).distance_constant c hcCol]
    exact sourceDistance_pos h)
  have hEm : E.map (embedM T) = Z T c := map_comap_eq_self
    ((hZX.trans (critical_X_le_vertex h e c hcCol _ hr)).trans_eq (stabilizer_m_base T))
  have hE : ¬ E ≤ pCore 2 M := by
    intro hh
    apply hr.2
    rw [←hEm,Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le]
    exact map_mono hh
  let : IsElementaryAbelian 2 (X T c) := omegaCenter_elementary _
  let : IsElementaryAbelian 2 (Z T c) := IsElementaryAbelian.of_le hZX
  let : IsElementaryAbelian 2 E :=
    IsElementaryAbelian.comap_of_injective _ (embedM_injective T) _
  have hBX : B ≤ centralOmega L R := by
    apply (map_le_map_iff_of_injective (embedM_injective T)).mp
    rw [map_commutator,←graph_X h,
      ←Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le]
    exact (criticalOrbit_commutator_le (sourceGeometry h) h.relative_radical.isPGroup
      h.relative_radical.twoCore_le hb hc hab hcb).trans
      ((sourceGeometry h).omega_bound _ rfl (sourceDistance_pos h))
  have hQB : pCore 2 M ≤ centralizer (B : Set M) := by
    intro q hq x hx
    exact (((mem_omegaCenterIn_iff _ _).mp (hBX hx)).2.1 q hq).symm
  have hBE : ⁅B,E⁆ = ⊥ := by
    apply (map_eq_bot_iff_of_injective _ (embedM_injective T)).mp
    rw [map_commutator,hEm]
    dsimp only [B]
    rw [map_commutator,←Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le]
    have hbCol := CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceTwo.NaturalCore.edge_color hab
    have hQb := Q_le_adjacent_h T hbCol hab
    have hQc : Q T (alpha T) ≤ stabilizer T c :=
      hQb.trans (fun _ hx => hx.2 c (adjacent_symm T hcb))
    have hAQ : criticalOrbit T c b ≤ Q T (alpha T) := by
      rw [criticalOrbit,Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le]
      exact map_mono (critical_orbit_le_core h e hz hk hb hc hab hcb)
    have htransfer := critical_layer_commutator_le_opposite_core h e hz hk hb c hc
      (Q T (alpha T)) (criticalOrbit T c b) hQc (hAQ.trans hQc)
      ((criticalOrbit_commutator_le (sourceGeometry h) h.relative_radical.isPGroup
        h.relative_radical.twoCore_le hb hc hab hcb).trans
        ((sourceGeometry h).omega_bound _ rfl (sourceDistance_pos h)))
    apply le_bot_iff.mp
    exact (commutator_mono htransfer le_rfl).trans_eq
      ((commutator_comm _ _).trans (Z_centralizes_Q T c hcCol))
  have hEC : E ≤ centralizer (B : Set M) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hBE)
  have hKC := component_le_normal_of_two_subgroup h e hz (centralizer (B : Set M)) E
    hQB (IsElementaryAbelian.isPGroup 2 E) hE hEC
  exact commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mpr hKC)

include h e hz hk in
theorem orbit_commutator_eq_plane
    (hb : sourceDistance h = 2) {c b : Vertex T}
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical _ rfl))
    (hab : Adjacent T (alpha T) b) (hcb : Adjacent T c b) :
    ⁅Q T (alpha T),criticalOrbit T c b⁆ = ⁅Q T (alpha T),criticalPlane T c b⁆ := by
  let D := ⁅Q T (alpha T),criticalPlane T c b⁆
  have hD : D ≤ ⁅Q T (alpha T),criticalOrbit T c b⁆ :=
    commutator_mono le_rfl (criticalPlane_le_orbit (sourceGeometry h) hb hc b)
  have hcent : ⁅⁅Q T (alpha T),criticalOrbit T c b⁆,Ltilde T (alpha T)⁆ = ⊥ := by
    rw [Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le,
      criticalOrbit,graph_component h,←map_commutator,←map_commutator,
      orbit_commutator_centralizes_component h e hz hk hb hc hab hcb,Subgroup.map_bot]
  have hG : Ltilde T (alpha T) ⊔ Q T b = stabilizer T (alpha T) := by
    have hgen : K ⊔ T = ⊤ := by
      apply top_unique
      intro g _
      obtain ⟨k,hkK,t,ht,rfl⟩ := h.relative_product g
      exact mul_mem (mem_sup_left hkK) (mem_sup_right ht)
    have hbase : Ltilde T (alpha T) ⊔ Q T (beta T) = stabilizer T (alpha T) := by
      rw [graph_component h,Q_beta,←Subgroup.map_sup,hgen,←MonoidHom.range_eq_map]
      exact (stabilizer_m_base T).symm
    obtain ⟨g,hg,hgb⟩ := stabilizer_transitive_neighbors T (alpha T) (base_adjacent T) hab
    have hh := congrArg (fun H : Subgroup (FreeAmalgam T) =>
      H.map (MulAut.conj g⁻¹).toMonoidHom) hbase
    change act T g (alpha T) = alpha T at hg
    change act T g (beta T) = b at hgb
    rw [Subgroup.map_sup,←Ltilde_act,←Q_act,←stabilizer_act,hg,hgb] at hh
    exact hh
  have hDG : D ≤ centralizer (stabilizer T (alpha T) : Set (FreeAmalgam T)) := by
    apply le_centralizer_iff.mp
    rw [←hG]
    apply sup_le
    · exact le_centralizer_iff.mp
        (hD.trans (commutator_eq_bot_iff_le_centralizer.mp hcent))
    · apply le_centralizer_iff.mp
      intro z hzD
      have hzZ := criticalPlane_commutator_le (sourceGeometry h) hb hc hab hcb hzD
      have hbCol := CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceTwo.NaturalCore.edge_color hab
      have hZb : Z T b = omegaCenter (Q T b) := by
        simp only [Z,hbCol,Bool.true_eq_false,if_false,edgeOmega]
      rw [hZb] at hzZ
      exact (mem_omegaCenter_iff.mp hzZ).2.2
  let D0 := D.comap (embedM T)
  let Y := (criticalPlane T c b).comap (embedM T)
  let : D0.Normal := by
    constructor
    intro x hx m
    change embedM T (m*x*m⁻¹) ∈ D
    rw [map_mul,map_mul,map_inv]
    have hm : embedM T m ∈ stabilizer T (alpha T) := by
      rw [show alpha T = mVertex T 1 from rfl,stabilizer_m_base]
      exact ⟨m,rfl⟩
    rw [hDG hx _ hm,mul_inv_cancel_right]
    exact hx
  have hcomm : ⁅pCore 2 M,Y⁆ ≤ D0 := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator,←Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le]
    exact commutator_mono le_rfl (map_comap_le _ _)
  have hh := map_mono (f := embedM T)
    (commutator_normalClosure_le_of_normal (pCore 2 M) Y D0 hcomm)
  rw [map_commutator,←Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le] at hh
  exact le_antisymm (hh.trans (map_comap_le _ _)) hD

include h e hz hk in
theorem orbit_commutator_le_edge
    (hb : sourceDistance h = 2) {c b : Vertex T}
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical _ rfl))
    (hab : Adjacent T (alpha T) b) (hcb : Adjacent T c b) :
    ⁅Q T (alpha T),criticalOrbit T c b⁆ ≤ Z T b := by
  rw [orbit_commutator_eq_plane h e hz hk hb hc hab hcb]
  exact criticalPlane_commutator_le (sourceGeometry h) hb hc hab hcb

include h e hz in
/-- Frattini detection removes the abelian-section restriction from the
escaping two-subgroup test. The odd covering kernel is retained. -/
theorem core_le_of_escaping_two_subgroup
    (N E : Subgroup M) [N.Normal] (hE : IsPGroup 2 E)
    (hEQ : ¬ E ≤ pCore 2 M) (hcomm : ⁅pCore 2 M,E⁆ ≤ N) :
    ⁅pCore 2 M,K⁆ ≤ N := by
  let F := (frattini (pCore 2 M)).map (pCore 2 M).subtype ⊔ N
  let : F.Normal := inferInstance
  have hQQ : ⁅pCore 2 M,pCore 2 M⁆ ≤ F := by
    apply le_trans _ le_sup_left
    let : Fact (IsPGroup 2 (pCore 2 M)) := ⟨pCore_isPGroup⟩
    rw [←map_subtype_commutator]
    exact map_mono (commutator_le_frattini_of_isPGroup (p := 2))
  exact commutator_le_of_le_frattini_sup_of_isPPerfect
    (pCore 2 M) K N pCore_isPGroup h.relative_twoPerfect
    (core_le_of_two_subgroup_commutator_le h e hz F E hQQ hE hEQ
      (hcomm.trans le_sup_right))

include h e hz in
theorem core_le_orbit_of_intersection_bound
    (hb : sourceDistance h = 2) {c b : Vertex T}
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical _ rfl))
    (hab : Adjacent T (alpha T) b) (hcb : Adjacent T c b)
    (hinter : ⁅Q T (alpha T),Z T c ⊓ Q T (alpha T)⁆ ≤ Z T b) :
    ⁅pCore 2 M,K⁆ ≤ criticalOrbitNative T c b := by
  let A := criticalOrbitNative T c b
  let : A.Normal := normalClosure_normal
  let E := (Z T c).comap (embedM T)
  have hcCol := critical_endpoint_color T (alpha T) rfl _ hc
  have hr := critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
    (alpha T) rfl (sourceDistance_pos h) c hcCol hc
  have hZX := (sourceGeometry h).omega_bound c hcCol (by
    rw [(sourceGeometry h).distance_constant c hcCol]
    exact sourceDistance_pos h)
  have hEm : E.map (embedM T) = Z T c := map_comap_eq_self
    ((hZX.trans (critical_X_le_vertex h e c hcCol _ hr)).trans_eq (stabilizer_m_base T))
  have hE : ¬ E ≤ pCore 2 M := by
    intro hh
    apply hr.2
    rw [←hEm,Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le]
    exact map_mono hh
  let : IsElementaryAbelian 2 (X T c) := omegaCenter_elementary _
  let : IsElementaryAbelian 2 (Z T c) := IsElementaryAbelian.of_le hZX
  let : IsElementaryAbelian 2 E :=
    IsElementaryAbelian.comap_of_injective _ (embedM_injective T) _
  apply core_le_of_escaping_two_subgroup h e hz A E
    (IsElementaryAbelian.isPGroup 2 E) hE
  apply (map_le_map_iff_of_injective (embedM_injective T)).mp
  rw [map_commutator,hEm,←Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le]
  apply le_trans _ (criticalPlane_le_orbit (sourceGeometry h) hb hc b)
  apply le_trans _ (le_criticalPlane_of_commutator_le _ inf_le_left hinter)
  exact le_inf
    (CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceTwo.NaturalCore.local_commutator_le_endpoint hab hcb)
    (CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceTwo.NaturalCore.local_commutator_le_Q
      (sourceGeometry h) hb hc)

include h e hz hk in
/-- Once the source intersection bound is supplied, the entire intrinsic
core is the component commutator of the literal critical-plane orbit. -/
theorem orbit_component_commutator_of_intersection_bound
    (hb : sourceDistance h = 2) {c b : Vertex T}
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical _ rfl))
    (hab : Adjacent T (alpha T) b) (hcb : Adjacent T c b)
    (hinter : ⁅Q T (alpha T),Z T c ⊓ Q T (alpha T)⁆ ≤ Z T b) :
    ⁅criticalOrbitNative T c b,K⁆ = ⁅pCore 2 M,K⁆ := by
  have hid := commutator_isPPerfect_idempotent K (pCore 2 M)
    h.relative_twoPerfect pCore_isPGroup le_normalizer_of_normal
  exact le_antisymm
    (commutator_mono (critical_orbit_le_core h e hz hk hb hc hab hcb) le_rfl)
    (hid.symm.le.trans (commutator_mono
      (core_le_orbit_of_intersection_bound h e hz hb hc hab hcb hinter) le_rfl))

include h e hz hk in
/-- The remaining plane-intersection and elementary-orbit assertions imply
exhaustion of the original whole core, not merely its initial section. -/
theorem coreExhaustion_of_elementary_orbit
    (hb : sourceDistance h = 2) {c b : Vertex T}
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical _ rfl))
    (hab : Adjacent T (alpha T) b) (hcb : Adjacent T c b)
    (hinter : ⁅Q T (alpha T),Z T c ⊓ Q T (alpha T)⁆ ≤ Z T b)
    (hel : IsElementaryAbelian 2 (criticalOrbitNative T c b)) : CoreExhaustion L R := by
  let A := criticalOrbitNative T c b
  let := hel
  let := h.relative_normal
  have hcore := core_le_orbit_of_intersection_bound h e hz hb hc hab hcb hinter
  have hcent : ⁅⁅A,K⁆,pCore 2 M⁆ = ⊥ := by
    apply commutator_commutator_eq_bot_of_rotate
    · rw [commutator_comm K]
      apply le_bot_iff.mp
      exact (commutator_mono hcore le_rfl).trans_eq (commutator_self_eq_bot_iff.mpr (inferInstance : IsMulCommutative A))
    · exact orbit_commutator_centralizes_component h e hz hk hb hc hab hcb
  rw [orbit_component_commutator_of_intersection_bound h e hz hk hb hc hab hcb hinter] at hcent
  have hCX : ⁅pCore 2 M,K⁆ ≤ centralOmega L R := by
    intro x hx
    apply (mem_omegaCenterIn_iff _ _).mpr
    exact ⟨commutator_le_left _ _ hx,
      commutator_eq_bot_iff_le_centralizer.mp hcent hx,
      elemPow_eq_one_of_isElementaryAbelian (p := 2) x (hcore hx)⟩
  apply le_antisymm
  · rw [←commutator_isPPerfect_idempotent K (pCore 2 M)
      h.relative_twoPerfect pCore_isPGroup le_normalizer_of_normal]
    exact commutator_mono hCX le_rfl
  · exact commutator_mono (fun x hx => ((mem_omegaCenterIn_iff _ _).mp hx).1) le_rfl

end AlternatingSixReconstruction.Exceptional.Exhaustion.CubicAction
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
