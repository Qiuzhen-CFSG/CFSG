module
public import Theory.GroupTheory.PResidual.CyclicImageCentralKernel
public import Theory.GroupTheory.CentralizerModulo.ConjugateSpan
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# Cyclic images of residuals of relative conjugate spans

Restricting to the actual conjugating subgroup identifies its normal
closure with the ambient conjugate span. The cyclic-image transfer theorem
then makes its two-residual faithful whenever the seed two-subgroup
centralizes the action kernel.

This is the relative version needed by the literal O²(M₀)T orbit in
Aschbacher--Smith15.2.3(1), printed p.1105. It avoids replacing that orbit
by the full local group.
-/

public section
open Subgroup
namespace Subgroup
variable {G D : Type*} [Group G] [Finite G] [Group D]

/-- Cyclic residual images are faithful on the actual relative conjugate span. -/
theorem disjoint_twoResidual_conjugateSpan_ker_of_cyclic_image
    (f : G →* D) (R B : Subgroup G) (hRB : R ≤ B) (hR : IsPGroup 2 R)
    (hc : R ≤ centralizer (f.ker : Set G))
    [IsCyclic (((pResidual 2 (conjugateSpanBy R B)).map
      (conjugateSpanBy R B).subtype).map f)] :
    Disjoint ((pResidual 2 (conjugateSpanBy R B)).map
      (conjugateSpanBy R B).subtype) f.ker := by
  let N := normalClosure (R.subgroupOf B : Set B)
  let E := (pResidual 2 N).map N.subtype
  let g := f.comp B.subtype
  have hN : N.map B.subtype = conjugateSpanBy R B := by
    dsimp only [N]
    rw [normalClosure_subgroupOf_eq_conjugateSpanBy _ _ hRB,
      map_subgroupOf_eq_of_le (conjugateSpanBy_le_self hRB)]
  have hE : E.map B.subtype = (pResidual 2 (conjugateSpanBy R B)).map
      (conjugateSpanBy R B).subtype := by
    rw [map_embedded_pResidual, hN]
  have hgC : R.subgroupOf B ≤ centralizer (g.ker : Set B) := by
    intro r hr k hk
    exact Subtype.ext (hc hr (k : G) hk)
  have hcyclic : IsCyclic (E.map g) := by
    change IsCyclic (E.map (f.comp B.subtype))
    rw [← map_map, hE]
    infer_instance
  let := hcyclic
  have hd : Disjoint E g.ker :=
    disjoint_twoResidual_normalClosure_ker_of_cyclic_image g (R.subgroupOf B)
      hR.comap_subtype hgC
  rw [← hE]
  apply disjoint_def.mpr
  rintro x ⟨y, hy, rfl⟩ hx
  exact congrArg B.subtype (disjoint_def.mp hd hy hx)
end Subgroup
