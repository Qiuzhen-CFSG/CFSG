module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.At.OrderTwo
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceOrbits.EarlierThirteen

/-!
# The original two-orbit and commutator-span identities

A length-three critical path has its endpoint in the original L-orbit.
The full natural action gives exactly two subgroup orbits. The resulting
commutator argument proves the central, derived and Frattini spans of
14.7.13, with only the original G,T centralizer input. These feed the
same selected rechoice in the source 14.7.72 generation consumer.
Source: Aschbacher–Smith 14.7.12–13, p.1046.
-/
public section
open Subgroup Representation
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceOrbits
open Chapter12.Section08 CriticalFusion.Source
open Subgroup.CosetGeometry.RankTwo
universe u
variable {G : Type u} [Group G] [Finite G]
 {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
 {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
 (d : Data T L V F W)

omit [Finite G] in
private theorem map_conj_mul (A : Subgroup G) (a b : G) :
    (A.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      A.map (MulAut.conj (a*b)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [mul_assoc]

include d in
 theorem three_conjugate_from_chosen
    (c : CriticalPath (L := L) F) (hb : c.b = 3) :
    ∃ l ∈ L, c.Uα = F.U.map (MulAut.conj l).toMonoidHom := by
  let Ω := geometryFamily (L := L) F
  let r : GeometryGroup T L F := inclusion (le_sup_right : F.H ≤ GeometryGroup T L F) c.rechoice
  let k : GeometryGroup T L F := c.gammaConjugator*r
  have hedge : (graph Ω).Adj (base Ω false) (k⁻¹ • base Ω true) := by
    have hp := c.path.adj_getVert_succ (i := 2) (by rw [c.length,hb]; decide)
    have hend : c.path.getVert 3 = c.gammaConjugator⁻¹ • base Ω true := by
      rw [←hb,←c.length,SimpleGraph.Walk.getVert_length]
    rw [hend] at hp
    have hh := (Subgroup.CosetGeometry.translationGraphIso Ω r⁻¹).toHom.map_adj hp
    change (graph Ω).Adj (r⁻¹ • c.path.getVert 2)
      (r⁻¹ • (c.gammaConjugator⁻¹ • base Ω true)) at hh
    rw [show r⁻¹ • c.path.getVert 2 = base Ω false from c.alignment] at hh
    simpa only [k,mul_inv_rev,mul_smul] using hh
  obtain ⟨a,ha,he⟩ := locally_transitive Ω
    (show (graph Ω).Adj (base Ω false) (base Ω true) from
      ⟨by change false ≠ true; decide,Subgroup.CosetGeometry.incident_base Ω false true⟩) hedge
  have haLT : (a : G) ∈ L ⊔ (T : Subgroup G) := by
    have ha' : a ∈ Ω false := by
      simpa only [stabilizer,base,Subgroup.CosetGeometry.stabilizer_base] using ha
    exact ha'
  have hkH : (k*a : GeometryGroup T L F) ∈ Ω true := by
    have hh : k*a ∈ MulAction.stabilizer (GeometryGroup T L F) (base Ω true) := by
      apply MulAction.mem_stabilizer_iff.mpr
      rw [mul_smul,he,smul_inv_smul]
    simpa only [base,Subgroup.CosetGeometry.stabilizer_base] using hh
  have hkn : (k : G)*(a : G) ∈ normalizer (F.U : Set G) :=
    d.conjugationSection.normalized hkH
  have heU : c.Uα = F.U.map (MulAut.conj (a : G)).toMonoidHom := by
    have hn := mem_normalizer_iff_map_conj_eq.mp hkn
    change F.U.map (MulAut.conj ((k : G)*(a : G))).toMonoidHom = F.U at hn
    have hh := congrArg (map (MulAut.conj (k : G)⁻¹).toMonoidHom) hn
    rw [map_conj_mul] at hh
    simp only [inv_mul_cancel_left] at hh
    exact hh.symm
  have ham : (a : G) ∈ (L : Set G)*(T : Set G) := by
    change (a : G) ∈ (L : Set G)*((T : Subgroup G) : Set G)
    rw [←coe_mul_of_right_le_normalizer_left L (T : Subgroup G)
      (d.natural.chosen.sylow_normalizes_component)]
    exact haLT
  obtain ⟨l,hl,t,ht,helt⟩ := ham
  have htU := mem_normalizer_iff_map_conj_eq.mp
    (d.conjugationSection.normalized (F.invariant 1 ht))
  refine ⟨l,hl,?_⟩
  rw [heU,←helt,←map_conj_mul]
  exact congrArg (fun Z : Subgroup G => Z.map (MulAut.conj l).toMonoidHom) htU


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceOrbits
public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceOrbits
open Chapter12.Section08 CriticalFusion.Source
open SourceEndgame.SteinbergRecognition
universe u
variable {G : Type u} [Group G] [Finite G]
 {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
 {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
 (d : Data T L V F W)
 (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
include d in
/-- The original U and its L-span lie in the literal Q. -/
theorem U_and_span_le_Q_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    F.U ≤ Q T L ∧ conjugateSpanBy F.U L ≤ Q T L := by
  have hU : F.U ≤ Q T L := by
    change F.U ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2
    rw [←d.natural.centralizer_LT_at structural]
    refine le_inf ((U_le_T d).trans le_sup_right) ?_
    exact (le_centralizer_iff_isMulCommutative.mpr d.abelian).trans
      (centralizer_le (Data.V_le_U F))
  exact ⟨hU,conjugateSpanBy_le hU L_normalizes_Q⟩

include d in
/-- The source two-orbit cover at the actual b=3 critical path. -/
theorem source_two_orbit_at (c : CriticalPath (L := L) F) (hb : c.b = 3) (l : L) :
    F.U.conjBy (l : G) = F.U ∨
      ∃ p : (L ⊓ F.H : Subgroup G), F.U.conjBy (l : G) = c.Uα.conjBy (p : G) :=
  two_orbit d (three_conjugate_from_chosen d c hb) (critical_ne d c) l
include d in
/-- Original 14.7.13(3), on the literal U,Q,L and S. -/
theorem central_span_at (c : CriticalPath (L := L) F) (hb : c.b = 3)
    (hc : ⁅⁅F.U,Q T L⁆,c.Uα⁆ = ⊥) :
    conjugateSpanBy ⁅F.U,Q T L⁆ L ≤ (center (S F L)).map (S F L).subtype := by
  have hEU : ⁅F.U,Q T L⁆ ≤ F.U :=
    le_normalizer_iff_commutator_le_left.mp ((Q_le_H F).trans d.conjugationSection.normalized)
  have hUU : ⁅F.U,F.U⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff_isMulCommutative.mpr d.abelian)
  have hPE : L ⊓ F.H ≤ normalizer ((⁅F.U,Q T L⁆ : Subgroup G) : Set G) := by
    intro p hp
    have heU : F.U.map (MulAut.conj p).toMonoidHom = F.U :=
      mem_normalizer_iff_map_conj_eq.mp (d.conjugationSection.normalized hp.2)
    have heQ : (Q T L).map (MulAut.conj p).toMonoidHom = Q T L :=
      mem_normalizer_iff_map_conj_eq.mp (L_normalizes_Q hp.1)
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (⁅F.U,Q T L⁆).map (MulAut.conj p).toMonoidHom = _
    rw [map_commutator,heU,heQ]
  have h := iSup_conjugates_le_center_of_two_orbits F.U ⁅F.U,Q T L⁆ c.Uα L (L ⊓ F.H)
    hEU hPE (bot_unique ((commutator_mono hEU le_rfl).trans hUU.le)) hc
    (source_two_orbit_at d c hb)
  rw [←conjugateSpanBy_eq_iSup_conj,←conjugateSpanBy_eq_iSup_conj] at h
  intro x hx
  have hh := h hx
  refine ⟨⟨x,hh.1⟩,mem_center_iff.mpr ?_,rfl⟩
  intro s
  exact Subtype.ext (hh.2 s s.property)
include d structural in
/-- Original 14.7.13(4), including the literal ambient Frattini image. -/
theorem frattini_derived_span_at (c : CriticalPath (L := L) F) (hb : c.b = 3) :
    (frattini (S F L)).map (S F L).subtype = conjugateSpanBy ⁅F.U,c.Uα⁆ L ∧
      ⁅S F L,S F L⁆ = conjugateSpanBy ⁅F.U,c.Uα⁆ L := by
  have hUQ := (U_and_span_le_Q_at d structural).1
  have hSQ := (U_and_span_le_Q_at d structural).2
  have hQU : Q T L ≤ normalizer (F.U : Set G) := (Q_le_H F).trans d.conjugationSection.normalized
  have hUU : ⁅F.U,F.U⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff_isMulCommutative.mpr d.abelian)
  have hA : ∃ a : L, c.Uα = F.U.conjBy (a : G) := by
    obtain ⟨a,ha,he⟩ := three_conjugate_from_chosen d c hb
    exact ⟨⟨a,ha⟩,he⟩
  have hd := TwoOrbitSpan.derived_span F.U c.Uα L (L ⊓ F.H) (Q T L)
    hUQ hQU L_normalizes_Q (inf_le_right.trans d.conjugationSection.normalized)
    inf_le_left hUU hA (source_two_orbit_at d c hb)
  have hp : IsPGroup 2 (conjugateSpanBy F.U L) := (isPGroup_pCoreIn 2 _).to_le hSQ
  have hPhi := TwoOrbitSpan.frattini_span F.U L hp (fun u hu => by
    let := d.U_elementary
    exact elemPow_eq_one_of_isElementaryAbelian u hu)
  exact ⟨hPhi.trans hd,hd⟩
include d structural in
/-- Discharge both earlier source implications used in 14.7.72. -/
theorem earlier_thirteen_at (c : CriticalPath (L := L) F) : SourceGeneration.EarlierThirteen c :=
  ⟨central_span_at d c,frattini_derived_span_at d structural c⟩
include d structural in
/-- The same producer applies to every permitted original-path rechoice. -/
theorem earlier_thirteen_reselect_at (c : CriticalPath (L := L) F) :
    ∀ n : Rechoice.group F L, SourceGeneration.EarlierThirteen (c.reselect n) :=
  fun n => earlier_thirteen_at d structural (c.reselect n)
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceOrbits
