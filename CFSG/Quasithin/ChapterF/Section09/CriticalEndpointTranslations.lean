module
public import CFSG.Quasithin.ChapterF.Section09.CriticalEndpoints

/-!
# Adjusting representatives of an F.9 critical endpoint

Right multiplication by H fixes the opposite critical vertex. Left
multiplication by the common Sylow subgroup fixes both base vertices and the
seed, preserving the distances and noncontainment that define the normalized
endpoint. These operations retain the actual ambient representatives for
independent factor markings in 14.6.13.

Source: Aschbacher--Smith F.9.17 and 14.6.13, printed pp.324 and 1032.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry.RankTwo
open Subgroup.CosetGeometry (stabilizer_base)
namespace CFSG.Quasithin.ChapterF.Section09.Setup.Hypothesis.CriticalEndpoint
open ChapterF.Section07.CriticalPairs
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {h : D.Hypothesis}

/-- Right multiplication by H leaves the normalized critical vertex unchanged. -/
def mulRight (i : h.CriticalEndpoint) (x : D.H) : h.CriticalEndpoint := by
  let y : G₀ (D := D) := ⟨x,(show D.H ≤ D.LT ⊔ D.H from le_sup_right) x.property⟩
  have hy : y • base (family (D := D)) true = base (family (D := D)) true := by
    change y ∈ stabilizer (family (D := D)) (base (family (D := D)) true)
    rw [show stabilizer (family (D := D)) (base (family (D := D)) true) = family (D := D) true from stabilizer_base _ true]
    exact x.property
  refine ⟨(i : G₀ (D := D))*y,?_⟩
  simpa only [mul_smul,hy] using i.property

theorem mulRight_representative (i : h.CriticalEndpoint) (x : D.H) :
    (i.mulRight x).representative = i.representative * (x:G) := rfl

/-- Left multiplication by the common edge group preserves both base vertices. -/
def mulLeft (i : h.CriticalEndpoint) (x : D.T) : h.CriticalEndpoint := by
  let y : G₀ (D := D) := ⟨x,(show D.H ≤ D.LT ⊔ D.H from le_sup_right) (h.T_le_H x.property)⟩
  have hy0 : y • base (family (D := D)) false = base (family (D := D)) false := by
    change y ∈ stabilizer (family (D := D)) (base (family (D := D)) false)
    rw [show stabilizer (family (D := D)) (base (family (D := D)) false) = family (D := D) false from stabilizer_base _ false]
    exact (show D.T ≤ D.LT from le_sup_right) x.property
  have hy1 : y • base (family (D := D)) true = base (family (D := D)) true := by
    change y ∈ stabilizer (family (D := D)) (base (family (D := D)) true)
    rw [show stabilizer (family (D := D)) (base (family (D := D)) true) = family (D := D) true from stabilizer_base _ true]
    exact h.T_le_H x.property
  have hnorm : h.f7Setup.seed.map (MulAut.conj y⁻¹).toMonoidHom = h.f7Setup.seed := by
    apply mem_normalizer_iff_map_conj_eq.mp
    apply h.f7Setup.seed_normalized
    change (y⁻¹:G₀ (D := D)) ∈ family (D := D) false
    exact (family (D := D) false).inv_mem ((show D.T ≤ D.LT from le_sup_right) x.property)
  refine ⟨y*(i : G₀ (D := D)),?_,?_,?_⟩
  · rw [mul_smul]
    calc
      _ = (graph (family (D := D))).dist (y • base (family (D := D)) false) (y • ((i : G₀ (D := D)) • base (family (D := D)) true)) := congrArg (fun v => (graph (family (D := D))).dist v _) hy0.symm
      _ = _ := (dist_smul _ _ _ _).trans i.property.1
  · rw [mul_smul]
    have he := dist_smul (family (D := D)) y (base (family (D := D)) true) ((i : G₀ (D := D)) • base (family (D := D)) true)
    rw [hy1] at he
    exact (congrArg (· + 1) he).trans i.property.2.1
  · intro hh
    have hm := map_mono (f := (MulAut.conj y⁻¹).toMonoidHom) hh
    rw [hnorm,← ballKernel_translate,mul_smul,inv_smul_smul] at hm
    exact i.property.2.2 hm

theorem mulLeft_representative (i : h.CriticalEndpoint) (x : D.T) :
    (i.mulLeft x).representative = (x:G)*i.representative := rfl
end CFSG.Quasithin.ChapterF.Section09.Setup.Hypothesis.CriticalEndpoint
