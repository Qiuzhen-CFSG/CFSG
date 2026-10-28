module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceOrbits.Basic
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice
public import Theory.GroupAction.RankTwoCosetGeometry.NormalNeighborKernel

/-!
# The b=3 critical conjugate belongs to the original L-orbit

The final edge of the actual length-three path, transported by the recorded
H-rechoice, is incident with the base LT vertex. Local transitivity supplies
an LT element with the same endpoint. H normalizes U, and the original
Sylow normalization factors this element through L without changing U.

Source: Aschbacher–Smith 14.7.12(2), printed p.1046.
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
 theorem three_conjugate
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
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
      (d.natural.sylow_normalizes structural)]
    exact haLT
  obtain ⟨l,hl,t,ht,helt⟩ := ham
  have htU := mem_normalizer_iff_map_conj_eq.mp
    (d.conjugationSection.normalized (F.invariant 1 ht))
  refine ⟨l,hl,?_⟩
  rw [heU,←helt,←map_conj_mul]
  exact congrArg (fun Z : Subgroup G => Z.map (MulAut.conj l).toMonoidHom) htU

include d in
/-- The genuine critical kernel condition prevents collapse to the base U. -/
 theorem critical_ne (c : CriticalPath (L := L) F) : c.Uα ≠ F.U := by
  let := d.natural.chosen.elementary
  intro he
  let Ω := geometryFamily (L := L) F
  let N := F.U.subgroupOf (GeometryGroup T L F)
  have hker : N ≤ ballKernel Ω (base Ω true) 1 := by
    apply le_base_ballKernel_one Ω N
    · intro x hx
      exact (le_sup_right : (T : Subgroup G) ≤ L ⊔ T) (U_le_T d hx)
    · intro x hx
      exact F.U_le_H hx
    · intro x hx
      apply mem_normalizer_iff.mpr
      intro y
      exact mem_normalizer_iff.mp (d.conjugationSection.normalized hx) y
  have hkn : c.conjugator⁻¹ ∈ normalizer (F.U : Set G) :=
    mem_normalizer_iff_map_conj_eq.mpr he
  have hgn : (c.gammaConjugator : G) ∈ normalizer (F.U : Set G) := by
    have h := (normalizer (F.U : Set G)).mul_mem
      ((normalizer (F.U : Set G)).inv_mem hkn)
      ((normalizer (F.U : Set G)).inv_mem
        (d.conjugationSection.normalized c.rechoice.property))
    simpa only [CriticalPath.conjugator,inv_inv,mul_inv_cancel_right] using h
  apply c.critical
  intro v hv
  have hvg : c.gammaConjugator*v*c.gammaConjugator⁻¹ ∈ N :=
    (mem_normalizer_iff.mp hgn v).mp (Data.V_le_U F hv)
  have hh := (conj_mem_ballKernel_iff Ω c.gammaConjugator⁻¹
    (c.gammaConjugator*v*c.gammaConjugator⁻¹) (base Ω true) 1).mpr (hker hvg)
  simpa only [inv_inv,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,inv_mul_cancel,mul_one] using hh

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceOrbits
