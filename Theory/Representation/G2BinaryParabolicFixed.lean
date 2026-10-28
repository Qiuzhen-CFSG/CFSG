module

public import Theory.Representation.FirstCohomologyG2Natural.BinaryPair
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.ResidualAction
public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.GroupTheory.SylowKernelCore

/-!
# Fixed vectors of the binary G₂ first parabolic residual core

The right quaternion generator in the actual two-residual acts on the six
natural coordinates with fixed vectors supported on the first two positions.
Projection onto these positions therefore embeds its fixed space in F₂².
The right quaternion subgroup is normal in the residual and is a two-group,
so the same bound applies to the core of that residual. Conjugation and
restriction to the genuine derived group preserve the calculated fixed space.

This computes O₂(O²(P)), keeping it distinct from the larger O₂(P).
The chapter consumer is the marked-core exclusion in the final proof of
Aschbacher–Smith 15.3.1, printed p.1155 of `refs/quasithin.pdf`.
The actual residual identification is `BinaryParabolicPair.ResidualAction`;
root coordinates come from the licensed ATLAS port through the imports.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open Atlas.G2 Atlas.G2.Explicit Atlas.G2.Natural Atlas.G2.BinaryCore
open Atlas.G2.BinaryParabolicPair

namespace Atlas.G2.Natural.BinaryParabolicFixed

private theorem rightI_apply (x : Atlas.SplitOctonion.Carrier (ZMod 2)) :
    (embedding rightI).val x =
      ![x 0+x 2+x 3+x 4+x 7, x 1+x 2+x 3+x 4+x 5+x 7, x 2+x 6,
        x 3+x 6+x 7, x 4+x 6+x 7, x 5+x 6+x 7, x 6, x 7] := by
  ext i
  fin_cases i <;>
    simp [embedding, parameters, rightI, unipotentProduct,
      rootA, rootB, rootC, rootD, rootE, rootF,
      rootAEquiv, rootBEquiv, rootCEquiv, rootDEquiv, rootEEquiv, rootFEquiv,
      rootALinear, rootBLinear, rootCLinear, rootDLinear, rootELinear, rootFLinear,
      rootAApply, rootBApply, rootCApply, rootDApply, rootEApply, rootFApply,
      sub_eq_add_neg, CharTwo.neg_eq] <;> ring_nf
  all_goals reduce_mod_char!

private theorem coordinates_rightI (v : Space (ZMod 2)) :
    binaryCoordinates (ZMod 2) (action (ZMod 2) (embedding rightI) v) =
      ![binaryCoordinates (ZMod 2) v 0 + binaryCoordinates (ZMod 2) v 2 + binaryCoordinates (ZMod 2) v 5,
        binaryCoordinates (ZMod 2) v 1 + binaryCoordinates (ZMod 2) v 2 + binaryCoordinates (ZMod 2) v 3 + binaryCoordinates (ZMod 2) v 5,
        binaryCoordinates (ZMod 2) v 2 + binaryCoordinates (ZMod 2) v 4,
        binaryCoordinates (ZMod 2) v 3 + binaryCoordinates (ZMod 2) v 4 + binaryCoordinates (ZMod 2) v 5,
        binaryCoordinates (ZMod 2) v 4, binaryCoordinates (ZMod 2) v 5] := by
  obtain ⟨x,rfl⟩ := mk_surjective (ZMod 2) v
  have ht : x.val 3 + x.val 4 = 0 := x.property
  simp only [action_mk, binaryCoordinates_mk, traceZeroAction_val, rightI_apply]
  ext i
  fin_cases i <;> simp <;> linear_combination ht

private theorem coordinates_fixed (v : Space (ZMod 2))
    (hv : action (ZMod 2) (embedding rightI) v = v) :
    binaryCoordinates (ZMod 2) v 2 = 0 ∧
      binaryCoordinates (ZMod 2) v 3 = 0 ∧
      binaryCoordinates (ZMod 2) v 4 = 0 ∧
      binaryCoordinates (ZMod 2) v 5 = 0 := by
  have h := coordinates_rightI v
  rw [hv] at h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h0 h1 h2 h3
  have h4 : binaryCoordinates (ZMod 2) v 4 = 0 := by linear_combination -h2
  have h5 : binaryCoordinates (ZMod 2) v 5 = 0 := by linear_combination -h3 - h4
  have h2' : binaryCoordinates (ZMod 2) v 2 = 0 := by linear_combination -h0 - h5
  have h3' : binaryCoordinates (ZMod 2) v 3 = 0 := by linear_combination -h1 - h2' - h5
  exact ⟨h2',h3',h4,h5⟩

theorem fixed_finrank_le_two (B : Subgroup (Model (ZMod 2)))
    (hB : embedding rightI ∈ B) :
    Module.finrank (ZMod 2) (fixedSpace (g2Natural (ZMod 2)) B) ≤ 2 := by
  let C := fixedSpace (g2Natural (ZMod 2)) B
  let f : C →ₗ[ZMod 2] (Fin 2 → ZMod 2) :=
    LinearMap.pi (fun i => (LinearMap.proj (i.castLE (by decide))).comp
      ((binaryCoordinates (ZMod 2)).comp C.subtype))
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro v hv
    have hz : f v = 0 := hv
    have h0 : binaryCoordinates (ZMod 2) v.val 0 = 0 := congrFun hz 0
    have h1 : binaryCoordinates (ZMod 2) v.val 1 = 0 := congrFun hz 1
    have hx := coordinates_fixed v.val (v.property ⟨embedding rightI, hB⟩)
    have hc : binaryCoordinates (ZMod 2) v.val = 0 := by
      ext i
      fin_cases i
      · exact h0
      · exact h1
      · exact hx.1
      · exact hx.2.1
      · exact hx.2.2.1
      · exact hx.2.2.2
    apply Subtype.ext
    exact (binaryCoordinates_injective (ZMod 2)).eq_iff.mp (by simpa using hc)
  simpa using LinearMap.finrank_le_finrank_of_injective hf

/-- The quaternion factor belongs to the core of the actual two-residual,
not merely to the larger parabolic core. -/
theorem right_le_residual_core : ResidualAction.right.range ≤ ResidualAction.K.pCoreIn 2 :=
  le_pCoreIn_of_normalizes
    (IsPGroup.of_card (show Nat.card ResidualAction.right.range = 2^3 from
      ResidualAction.card_right)) le_sup_left ResidualAction.K_normalizes_right

private theorem rightI_mem_right : embedding rightI ∈ ResidualAction.right.range := by
  refine ⟨QuaternionGroup.a 1, ?_⟩
  change embedding (rightEmbedding (QuaternionGroup.a 1)) = embedding rightI
  congr 1

/-- The true first residual core fixes at most two dimensions. -/
theorem residual_core_fixed_finrank_le_two :
    Module.finrank (ZMod 2) (fixedSpace (g2Natural (ZMod 2))
      (ResidualAction.K.pCoreIn 2)) ≤ 2 :=
  fixed_finrank_le_two _ (right_le_residual_core rightI_mem_right)

/-- The same bound for every conjugate of the actual first residual. -/
theorem conjugate_residual_core_fixed_finrank_le_two (g : Model (ZMod 2)) :
    Module.finrank (ZMod 2) (fixedSpace (g2Natural (ZMod 2))
      ((ResidualAction.K.map (MulAut.conj g).toMonoidHom).pCoreIn 2)) ≤ 2 := by
  rw [← map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective,
    ← (fixedSpaceConjEquiv (g2Natural (ZMod 2)) (ResidualAction.K.pCoreIn 2) g).finrank_eq]
  exact residual_core_fixed_finrank_le_two

/-- Restriction to the genuine derived carrier does not change the fixed
space of a subgroup with this ambient residual marking. -/
theorem derived_residual_core_fixed_finrank_le_two
    (L : Subgroup (commutator (Model (ZMod 2)))) (g : Model (ZMod 2))
    (hL : L.map (commutator (Model (ZMod 2))).subtype =
      ResidualAction.K.map (MulAut.conj g).toMonoidHom) :
    Module.finrank (ZMod 2) (fixedSpace (g2DerivedNatural (ZMod 2)) (L.pCoreIn 2)) ≤ 2 := by
  change Module.finrank (ZMod 2)
    (fixedSpace ((g2Natural (ZMod 2)).comp (commutator (Model (ZMod 2))).subtype)
      (L.pCoreIn 2)) ≤ 2
  rw [fixedSpace_comp_map, map_pCoreIn_of_injective 2 L _
    (commutator (Model (ZMod 2))).subtype_injective, hL]
  exact conjugate_residual_core_fixed_finrank_le_two g

end Atlas.G2.Natural.BinaryParabolicFixed
