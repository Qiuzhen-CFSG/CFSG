module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.CriticalPlane.Coordinates
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.CriticalIntersection
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.OrbitLarge

/-!
# The maximal critical plane is the opposite kernel intersection

The source kernel is self-centralizing because it contains the faithful
natural moving layer. Thus the critical intersection identifies the fixed
space of the initial kernel on the opposite moving layer with the edge
line. On the fixed space of the nontrivial initial Z-image, the elementary
kernel image acts quadratically in dimension at most three. Its displacement
is therefore in that edge line. The decomposition Zc=Uc Zb transports this
to the whole intersection Zc intersect Qα.

The parent orbit containment gives the reverse inclusion. The genuine
core-large premise already implies core≠U, so no new contrary hypothesis
or orbit-size premise is needed in this binary native specialization.
The final application preserves the actual characteristic replacement.
Source: MS93 (3.6), printed p.871.
-/

public section
open Subgroup Theory.GroupTheory BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)
include s

private theorem plane_edge_coordinates (h : NativeCentralLayer s) {c b : Vertex R}
    (hc : color R c = false) (hcb : Adjacent R c b) :
    ∃i : M →* FreeAmalgam R, Function.Injective i ∧
      i.range = stabilizer R c ∧ R.map i = Q R b ∧
      (pCore 2 M).map i = Q R c ∧
      (omegaCenter R).map i = Z R b ∧
      (W ⊔ omegaCenter R).map i = Z R c := by
  obtain ⟨g,hg | hg⟩ := (adjacent_iff_exists_common R c b).mp hcb
  · rcases hg with ⟨rfl,rfl⟩
    let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM R)
    have hi : Function.Injective i := (MulAut.conj g⁻¹).injective.comp (embedM_injective R)
    have hiR : R.map i = Q R (hVertex R g) := by
      have he := Q_act R g (beta R)
      rw [Q_beta] at he
      simpa only [beta,act_hVertex,one_mul,Q_beta,map_map] using he.symm
    refine ⟨i,hi,?_,hiR,?_,?_,?_⟩
    · have he := stabilizer_act R g (alpha R)
      dsimp only [i]
      rw [MonoidHom.range_comp]
      change (Mbar R).map (MulAut.conj g⁻¹).toMonoidHom = _
      simpa only [alpha,act_mVertex,one_mul,stabilizer_m_base] using he.symm
    · have he := Q_act R g (alpha R)
      rw [Q_alpha R s.two_group s.core_le] at he
      simpa only [alpha,act_mVertex,one_mul,Q_alpha R s.two_group s.core_le,map_map] using he.symm
    · rw [←omegaCenter_map R i hi,hiR]
      simp only [Z,show color R (hVertex R g) = true from rfl,Bool.true_eq_false,if_false,edgeOmega]
    · have he := Z_act R g (alpha R)
      rw [SymplecticSeed.Z_eq_seedHull,s.seedHull_eq_module_sup_seed h] at he
      simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
  · rw [hg.1] at hc
    cases hc

private theorem opposite_fixed_le_X (hb : s.geometry.b R = 2) {c : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl)) :
    Z R c ⊓ centralizer (Q R (alpha R) : Set (FreeAmalgam R)) ≤ X R (alpha R) := by
  have hc0 := critical_endpoint_color R (alpha R) rfl _ hc
  have hpos : 0 < criticalDistance R (alpha R) (s.geometry.exists_critical (alpha R) rfl) := by
    change 0 < s.geometry.b R
    omega
  have hcpos : 0 < criticalDistance R c (s.geometry.exists_critical c hc0) := by
    rw [s.geometry.distance_constant c hc0]
    exact hpos
  have hZG : Z R c ≤ (embedM R).range := by
    rw [←show stabilizer R (alpha R) = (embedM R).range from stabilizer_m_base R]
    exact critical_Z_le_stabilizer R s.geometry (alpha R) rfl hpos hc
  rintro x ⟨hx,hxc⟩
  obtain ⟨m,rfl⟩ := hZG hx
  have hmc : m ∈ centralizer (pCore 2 M : Set M) := by
    intro q hq
    apply embedM_injective R
    simpa only [map_mul] using hxc (embedM R q) (by
      rw [Q_alpha R s.two_group s.core_le]
      exact mem_map_of_mem _ hq)
  have hmQ : m ∈ pCore 2 M :=
    ((centralizer_le s.module_le_core).trans_eq s.module_centralizer) hmc
  apply mem_omegaCenter_iff.mpr
  refine ⟨?_,(mem_omegaCenter_iff.mp (s.geometry.omega_bound c hc0 hcpos hx)).2.1,hxc⟩
  rw [Q_alpha R s.two_group s.core_le]
  exact mem_map_of_mem _ hmQ

/-- The entire opposite layer inside the initial kernel satisfies the
maximal-plane commutator bound. -/
theorem critical_intersection_commutator_le_edge
    (h : NativeCentralLayer s) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b) :
    ⁅Q R (alpha R),Z R c ⊓ Q R (alpha R)⁆ ≤ Z R b := by
  have hc0 := critical_endpoint_color R (alpha R) rfl _ hc
  have hb0 := DistanceTwo.NaturalCore.edge_color hab
  obtain ⟨i,hi,hir,hiR,hiQ,hiS,hiH⟩ := s.plane_edge_coordinates h hc0 hcb
  let A := (Z R (alpha R)).comap i
  let B := (Q R (alpha R)).comap i
  have hZQ : Z R (alpha R) ≤ Q R (alpha R) := s.Z_le_X.trans (omegaCenter_le _)
  have hQG := DistanceTwo.NaturalCore.Q_le_endpoint_stabilizer hab hcb
  have hAm : A.map i = Z R (alpha R) := by
    rw [map_comap_eq,hir,inf_eq_right.mpr (hZQ.trans hQG)]
  have hBm : B.map i = Q R (alpha R) := by
    rw [map_comap_eq,hir,inf_eq_right.mpr hQG]
  have hAB : A ≤ B := comap_mono hZQ
  have hBR : B ≤ R := by
    apply (map_le_map_iff_of_injective hi).mp
    rw [hBm,hiR]
    exact Q_le_adjacent_h R hb0 hab
  have hne : ¬ A ≤ pCore 2 M := by
    intro hle
    apply hc.2
    rw [←hAm,←hiQ]
    exact map_mono hle
  have hfix : W ⊓ centralizer (B : Set M) ≤ omegaCenter R := by
    rintro w ⟨hw,hwc⟩
    have hz : i w ∈ Z R c := by
      rw [←hiH]
      exact mem_map_of_mem i (mem_sup_left hw)
    have hcentral : i w ∈ centralizer (Q R (alpha R) : Set (FreeAmalgam R)) := by
      intro q hq
      obtain ⟨y,hy,rfl⟩ := hBm.ge hq
      simpa only [map_mul] using congrArg i (hwc y hy)
    have hmem : i w ∈ Z R c ⊓ X R (alpha R) := ⟨hz,s.opposite_fixed_le_X hb hc ⟨hz,hcentral⟩⟩
    rw [s.critical_Z_inf_X_eq_edge h t hfull hb hlarge hc hab hcb,←hiS] at hmem
    obtain ⟨u,hu,he⟩ := hmem
    exact hi he ▸ hu
  have hcomm := s.module_fixed_commutator_le_seed A B hAB hBR t hfull hne hfix
  apply commutator_le.mpr
  intro q hq z hz
  obtain ⟨y,hy,rfl⟩ := hBm.ge hq
  obtain ⟨x,hx,hxz⟩ := hiH.ge hz.1
  obtain ⟨w,hw,u,hu,rfl⟩ := mem_sup_of_normal_left.mp hx
  have huc : u ∈ centralizer (A : Set M) :=
    fun a ha => (mem_omegaCenter_iff.mp hu).2.2 a (hBR (hAB ha))
  have hxc : w*u ∈ centralizer (A : Set M) := by
    intro a ha
    apply hi
    have hh := Q_le_centralizer_X R (alpha R) hz.2 (i a) (s.Z_le_X ha)
    rw [←hxz] at hh
    simpa only [map_mul] using hh
  have hwc : w ∈ centralizer (A : Set M) := by
    simpa only [mul_inv_cancel_right] using
      (centralizer (A : Set M)).mul_mem hxc ((centralizer (A : Set M)).inv_mem huc)
  rw [←hxz,map_mul,commutatorElement_mul_right_eq_mul_conj]
  have hyu : Commute (i y) (i u) := by
    change i y * i u = i u * i y
    simpa only [map_mul] using congrArg i ((mem_omegaCenter_iff.mp hu).2.2 y (hBR hy))
  rw [hyu.commutator_eq]
  simp only [mul_one,mul_inv_cancel_right]
  rw [←hiS,←map_commutatorElement]
  exact mem_map_of_mem i (hcomm (commutator_mem_commutator hy ⟨hw,hwc⟩))

/-- The source's maximal plane is the literal kernel intersection. -/
theorem criticalPlane_eq_opposite_inf_Q
    (h : NativeCentralLayer s) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b) :
    criticalPlane R c b = Z R c ⊓ Q R (alpha R) := by
  have hne : core R (alpha R) ≠ U R (alpha R) := by
    intro he
    apply hlarge
    rw [he]
    exact ((U_le_Z _).trans s.Z_le_X).trans le_sup_right
  apply le_antisymm
  · exact le_inf (criticalPlane_le_opposite c b)
      (s.criticalPlane_le_Q_of_core_ne hb hc hab hcb hne)
  · exact le_criticalPlane_of_commutator_le _ inf_le_left
      (s.critical_intersection_commutator_le_edge h t hfull hb hlarge hc hab hcb)
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K]
  {L V : Subgroup K} [L.Normal] [V.Normal] {T : Sylow 2 K}
  (d : NaturalSixControl.SourceData L V T)

/-- The actual characteristic replacement uses its original projection and
relabeler, and supplies the native central layer internally. -/
theorem reducedSource_criticalPlane_eq_opposite_inf_Q (h : IntrinsicMSPair d)
    (r : CharacteristicReduction (L.subgroupOf (L ⊔ d.B))
      (d.B.subgroupOf (L ⊔ d.B)))
    (hfull : r.radical.map ((originalSource d h).reduce r).projection =
      pointCore.map (MulAut.conj d.relabeler.val⁻¹).toMonoidHom)
    (hb : ((originalSource d h).reduce r).geometry.b r.radical = 2)
    (hlarge : ¬ core r.radical (alpha r.radical) ≤
      (frattini (Q r.radical (alpha r.radical))).map (Q r.radical (alpha r.radical)).subtype ⊔
        X r.radical (alpha r.radical))
    {c b : Vertex r.radical}
    (hc : CriticalPair r.radical (alpha r.radical) c
      (((originalSource d h).reduce r).geometry.exists_critical (alpha r.radical) rfl))
    (hab : Adjacent r.radical (alpha r.radical) b) (hcb : Adjacent r.radical c b) :
    criticalPlane r.radical c b = Z r.radical c ⊓ Q r.radical (alpha r.radical) :=
  Source.criticalPlane_eq_opposite_inf_Q ((originalSource d h).reduce r)
    (reduced_nativeCentralLayer d h r) d.relabeler.val⁻¹ hfull hb hlarge hc hab hcb

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
