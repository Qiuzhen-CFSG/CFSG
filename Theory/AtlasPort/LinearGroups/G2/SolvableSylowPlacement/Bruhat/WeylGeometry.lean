module

public import Theory.AtlasPort.LinearGroups.G2.SolvableSylowPlacement.Bruhat.VectorReduction
public import Mathlib.Algebra.CharP.Two

/-!
# Concrete Weyl representatives for the six singular-vector cells

The alternating words of lengths zero through five ending in `S` send the
first vector to the six coordinate pivots. Their products with `R` give the
other six published representatives, with the last equality checked directly
on octonion coordinates. Conjugation carries the root `E` into positive roots
`E, B, A, A, B, E`, respectively. Singular-vector reduction therefore gives
six cells modulo the full long parabolic, ready for its two-cell refinement.

Source: the concrete existence part of GLS III, Theorem 2.3.5
(`refs/KGroup/GLS3/chapter2.tex`). Weyl and root formulas are from the licensed
ATLAS port; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

namespace Atlas.G2.SolvableSylowPlacement.BruhatGeometry
open Atlas.SplitOctonion Explicit
variable {F : Type*} [Field F] [CharP F 2]

/-- Shortest representatives modulo the long simple reflection. -/
def pointRep (i : Fin 6) : Model F :=
  ![1,weylS,weylR*weylS,weylS*weylR*weylS,
    weylR*weylS*weylR*weylS,weylS*weylR*weylS*weylR*weylS] i

/-- Published index of a point representative. -/
def pointWeylIndex : Fin 6 → Fin 12 := ![0,2,3,6,7,10]
/-- Published index after adjoining the long reflection. -/
def extendedWeylIndex : Fin 6 → Fin 12 := ![1,4,5,8,9,11]

omit [CharP F 2] in
/-- The six representatives are among the published twelve. -/
theorem pointRep_eq_weylRep (i : Fin 6) :
    pointRep (F := F) i = weylRep (pointWeylIndex i) := by
  fin_cases i <;> rfl

/-- Appending the long reflection gives the other six published cells. -/
theorem pointRep_mul_weylR (i : Fin 6) :
    pointRep (F := F) i * weylR = weylRep (extendedWeylIndex i) := by
  fin_cases i
  · simp [pointRep,extendedWeylIndex,weylRep]
  · rfl
  · rfl
  · rfl
  · rfl
  · apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    funext j
    fin_cases j <;>
      simp [pointRep,extendedWeylIndex,weylRep,weylR,weylREquiv,weylRLinear,weylRApply,
        weylS,weylSEquiv,weylSLinear,weylSApply,CharTwo.neg_eq]

/-- The six Weyl maps carry the first vector to the six coordinate pivots. -/
theorem pointRep_first (i : Fin 6) :
    (pointRep (F := F) i).val (basisVector 0) = basisVector (vectorIndex i) := by
  fin_cases i <;> funext j <;> fin_cases j <;>
    simp [pointRep,vectorIndex,weylR,weylREquiv,weylRLinear,weylRApply,
      weylS,weylSEquiv,weylSLinear,weylSApply,basisVector,CharTwo.neg_eq]

private def transportedRoot (i : Fin 6) (a : F) : Model F :=
  ![rootE a,rootB a,rootA a,rootA a,rootB a,rootE a] i

omit [CharP F 2] in
private theorem transportedRoot_mem (i : Fin 6) (a : F) :
    transportedRoot i a ∈ unipotent := by
  fin_cases i <;> apply Subgroup.subset_closure <;> simp [transportedRoot]

private theorem pointRep_rootE_eq (i : Fin 6) (a : F) :
    pointRep i * rootE a = transportedRoot i a * pointRep i := by
  fin_cases i <;> apply Subtype.ext <;> apply LinearEquiv.ext <;> intro x <;>
    funext j <;> fin_cases j <;>
    simp [pointRep,transportedRoot,weylR,weylREquiv,weylRLinear,weylRApply,
      weylS,weylSEquiv,weylSLinear,weylSApply,rootA,rootAEquiv,rootALinear,rootAApply,
      rootB,rootBEquiv,rootBLinear,rootBApply,rootE,rootEEquiv,rootELinear,rootEApply,
      CharTwo.neg_eq,CharTwo.sub_eq_add]

/-- The remaining simple positive root stays positive under each point representative. -/
theorem pointRep_rootE (i : Fin 6) (a : F) :
    ∃ u ∈ unipotent, pointRep i * rootE a = u * pointRep i :=
  ⟨transportedRoot i a,transportedRoot_mem i a,pointRep_rootE_eq i a⟩

/-- Singular-vector elimination gives six cells modulo the full point stabilizer. -/
theorem point_cells (g : Model F) :
    ∃ i : Fin 6, ∃ u ∈ unipotent, ∃ p ∈ parabolic, g = u * pointRep i * p := by
  have ht : trace (g.val (basisVector 0)) = 0 := by
    rw [automorphism_trace]
    simp [trace,basisVector]
  have hn : SplitOctonion.norm (g.val (basisVector 0)) = 0 := by
    rw [automorphism_norm]
    simp [SplitOctonion.norm,basisVector]
  have hx : g.val (basisVector 0) ≠ 0 := by
    intro h
    exact first_basis_ne_zero (g.val.injective (h.trans (map_zero g.val).symm))
  obtain ⟨u,hu,i,a,ha,he⟩ := unipotent_vector_reduction _ ht hn hx
  let p := (pointRep i)⁻¹ * u * g
  have hp : p ∈ parabolic := by
    rw [parabolic_eq_pointStabilizer]
    apply (mem_pointStabilizer_iff p).mpr
    refine ⟨Units.mk0 a ha, ?_⟩
    change (pointRep i).val.symm (u.val (g.val (basisVector 0))) = a • basisVector 0
    rw [he, ← pointRep_first i, map_smul, LinearEquiv.symm_apply_apply]
  refine ⟨i,u⁻¹,unipotent.inv_mem hu,p,hp,?_⟩
  dsimp [p]
  group

end Atlas.G2.SolvableSylowPlacement.BruhatGeometry
