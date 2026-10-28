module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveSourceAudit.Model
import Theory.SpecificGroups.PSL3.ProjectionKernel
import Theory.GroupTheory.NormalizingInvolutionCard
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Checked matrices, actor orders, and weak-closure movement in PSL₃(5):2

The faithful central projection identifies the literal matrix witnesses inside
`Model`. A trace calculation separates inverse transpose from the inner
subgroup. The original actor is the direct product of its four diagonal signs
with inverse transpose, so it has order eight and its inner intersection has
order four.

For the stated matrix q, Lean's left conjugation by inner(q⁻¹) sends the second
original sign to the signed swap u, the first to u times the second sign, and
graph to inner(diag(1,3,2)) times graph. These are computations on the literal
carrier; the order of the decoded GAP generators is not used. A monomial
three-cycle y makes u(yuy⁻¹) a nonidentity element of order three. Consequently,
if the conjugate actor lies in a Sylow two-subgroup T, y moves its weak closure.
No exact computation of that weak closure or subgroup census is required.

Solvability of `monomialOvergroup` and simultaneous ambient Sylow placement of
the original and conjugated actors remain separate obligations.

Source: the matrix diagnostic in `FiveSourceAudit/source/README.md`, and
Aschbacher--Smith E.1.1--5 and E.1.14(7), printed pp.209--214. Matrix carriers
and the simplicity input are imported from the attributed ATLAS development;
its license is retained at `LICENSES/ATLAS.txt`.
-/

public section
open Subgroup
open scoped MatrixGroups Matrix Pointwise
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveSourceAudit
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : IsSimpleGroup PSL(3, ZMod 5) := Atlas.psl_simple_high_rank 3 (by decide)

private theorem proj_inj : Function.Injective (Matrix.PSL3.projection (ZMod 5)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply Subgroup.eq_bot_of_card_eq
  rw [Matrix.PSL3.card_projectionKernel, Nat.card_zmod]
  decide

/-- The matrix embedding into the literal graph extension is faithful. -/
theorem innerSL_injective : Function.Injective innerSL :=
  Subtype.val_injective.comp ((innerPartEquiv (ZMod 5)).injective.comp proj_inj)

/-- The matrix embedding is the actual inner automorphism of its projective image. -/
theorem innerSL_val (x : SL(3, ZMod 5)) :
    (innerSL x).val = MulAut.conj (Matrix.PSL3.projection (ZMod 5) x) :=
  innerPartEquiv_apply_coe _ _

/-- The embedding has precisely the marked inner subgroup as its range. -/
theorem innerSL_range : innerSL.range = inner := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact (innerPartEquiv (ZMod 5) (Matrix.PSL3.projection (ZMod 5) x)).property
  · intro x hx
    obtain ⟨d, hd⟩ := Matrix.PSL3.projection_surjective (ZMod 5)
      ((innerPartEquiv (ZMod 5)).symm ⟨x, hx⟩)
    refine ⟨d, ?_⟩
    change ((innerPartEquiv (ZMod 5)) (Matrix.PSL3.projection (ZMod 5) d)).val = x
    rw [hd, MulEquiv.apply_symm_apply]

/-- Inverse transpose acts on the embedded matrices by inverse transpose. -/
theorem graph_innerSL (x : SL(3, ZMod 5)) :
    graphElement * innerSL x =
      innerSL ((Matrix.SpecialLinearGroup.transpose x)⁻¹) * graphElement := by
  apply Subtype.ext
  change Matrix.PSL3.OuterSolvable.graph (ZMod 5) * (innerSL x).val =
    (innerSL ((Matrix.SpecialLinearGroup.transpose x)⁻¹)).val * Matrix.PSL3.OuterSolvable.graph (ZMod 5)
  rw [innerSL_val, innerSL_val]
  ext z
  change Matrix.PSL3.OuterSolvable.graph (ZMod 5)
    (Matrix.PSL3.projection (ZMod 5) x * z * (Matrix.PSL3.projection (ZMod 5) x)⁻¹) =
      Matrix.PSL3.projection (ZMod 5) x.transpose⁻¹ *
        Matrix.PSL3.OuterSolvable.graph (ZMod 5) z * (Matrix.PSL3.projection (ZMod 5) x.transpose⁻¹)⁻¹
  rw [map_mul, map_mul, map_inv]
  rfl

/-- The diagnostic matrix q; the corresponding actor uses left conjugation by q⁻¹. -/
@[expose] def witnessConjugator : SL(3, ZMod 5) :=
  ⟨!![0,1,2;4,0,0;0,1,3], by decide +kernel⟩
/-- The involution u which will lie in the weak closure. -/
@[expose] def witnessSwap : SL(3, ZMod 5) :=
  ⟨!![4,0,0;0,0,2;0,3,0], by decide +kernel⟩
/-- The coordinate three-cycle which moves the weak closure. -/
@[expose] def witnessCycle : SL(3, ZMod 5) :=
  ⟨!![0,1,0;0,0,1;1,0,0], by decide +kernel⟩
/-- The diagonal factor in the conjugated graph generator. -/
@[expose] def witnessDiagonal : SL(3, ZMod 5) :=
  ⟨!![1,0,0;0,3,0;0,0,2], by decide +kernel⟩

/-- The exact image of the first original diagonal involution. -/
theorem conjugate_first : witnessConjugator⁻¹ * Matrix.SL3.standardInvolution (ZMod 5) *
    witnessConjugator = witnessSwap * secondDiagonal := by decide +kernel
/-- The exact image of the second original diagonal involution. -/
theorem conjugate_second : witnessConjugator⁻¹ * secondDiagonal * witnessConjugator = witnessSwap := by decide +kernel
/-- The inner factor of the conjugated graph element. -/
theorem conjugate_graph_matrix : witnessConjugator⁻¹ * (Matrix.SpecialLinearGroup.transpose witnessConjugator)⁻¹ = witnessDiagonal := by decide +kernel
private theorem witness_product_cube : (witnessSwap * (witnessCycle * witnessSwap * witnessCycle⁻¹)) ^ 3 = 1 := by decide +kernel
private theorem witness_product_ne_one : witnessSwap * (witnessCycle * witnessSwap * witnessCycle⁻¹) ≠ 1 := by decide +kernel
/-- The moving element lies in the actual coordinate-axis stabilizer. -/
theorem witnessCycle_mem_linear : witnessCycle ∈ Matrix.SL3.SplitMonomial.linear (ZMod 5) := by
  change witnessCycle ∈ MulAction.stabilizer _ (Matrix.SL3.SplitMonomial.coordinateVectors (ZMod 5))
  rw [MulAction.mem_stabilizer_iff]
  apply Set.Subset.antisymm
  · apply Set.smul_set_subset_iff.mpr
    dsimp [Matrix.SL3.SplitMonomial.coordinateVectors]
    decide +kernel
  · rw [Set.subset_smul_set_iff]
    apply Set.smul_set_subset_iff.mpr
    dsimp [Matrix.SL3.SplitMonomial.coordinateVectors]
    decide +kernel

private def traceWitness : SL(3, ZMod 5) :=
  ⟨!![2,0,0;0,2,0;0,0,4], by decide +kernel⟩

/-- The graph element is genuinely outside the marked inner subgroup. -/
theorem graphElement_not_mem_inner : graphElement ∉ inner := by
  intro h
  rw [← innerSL_range] at h
  obtain ⟨g, hg⟩ := h
  have he := congrArg (fun a : Model => a.val (Matrix.PSL3.projection (ZMod 5) traceWitness)) hg
  rw [innerSL_val, MulAut.conj_apply] at he
  change Matrix.PSL3.projection (ZMod 5) g * Matrix.PSL3.projection (ZMod 5) traceWitness *
      (Matrix.PSL3.projection (ZMod 5) g)⁻¹ =
    Matrix.PSL3.projection (ZMod 5) (Matrix.SpecialLinearGroup.transpose traceWitness)⁻¹ at he
  have he' : g * traceWitness * g⁻¹ = (Matrix.SpecialLinearGroup.transpose traceWitness)⁻¹ :=
    proj_inj (by simpa only [map_mul, map_inv] using he)
  have ht := congrArg (fun a : SL(3, ZMod 5) => Matrix.trace a.val) he'
  have hc : Matrix.trace (g * traceWitness * g⁻¹).val = Matrix.trace traceWitness.val := by
    change Matrix.trace (g.val * traceWitness.val * (g⁻¹).val) = _
    rw [Matrix.trace_mul_cycle]
    change Matrix.trace ((g⁻¹ * g) * traceWitness).val = _
    rw [inv_mul_cancel, one_mul]
  rw [hc] at ht
  revert ht
  decide +kernel

private def signPair (x : Multiplicative (ZMod 2 × ZMod 2)) : SL(3, ZMod 5) :=
  Matrix.SL3.standardInvolution (ZMod 5) ^ x.toAdd.1.val * secondDiagonal ^ x.toAdd.2.val

private def signHom : Multiplicative (ZMod 2 × ZMod 2) →* SL(3, ZMod 5) where
  toFun := signPair
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

private theorem signHom_injective : Function.Injective signHom := by decide +kernel

private noncomputable def actorInnerFour : Subgroup Model := signHom.range.map innerSL

private theorem signHom_mem_actor (x : Multiplicative (ZMod 2 × ZMod 2)) :
    innerSL (signHom x) ∈ actor := by
  change innerSL (Matrix.SL3.standardInvolution (ZMod 5) ^ x.toAdd.1.val *
    secondDiagonal ^ x.toAdd.2.val) ∈ actor
  rw [map_mul, map_pow, map_pow]
  apply actor.mul_mem
  · exact actor.pow_mem (subset_closure (by simp)) _
  · exact actor.pow_mem (subset_closure (by simp)) _

private theorem actorInnerFour_le_actor : actorInnerFour ≤ actor := by
  rintro _ ⟨x, ⟨a, rfl⟩, rfl⟩
  exact signHom_mem_actor a

private theorem actorInnerFour_le_inner : actorInnerFour ≤ inner := by
  rw [← innerSL_range]
  exact map_le_range _ _

private theorem card_actorInnerFour : Nat.card actorInnerFour = 4 := by
  rw [actorInnerFour, card_map_of_injective innerSL_injective]
  rw [← Nat.card_congr (MonoidHom.ofInjective signHom_injective).toEquiv]
  change Nat.card (ZMod 2 × ZMod 2) = 4
  simp

private theorem actor_eq_innerFour_sup_graph : actor = actorInnerFour ⊔ zpowers graphElement := by
  apply le_antisymm
  · rw [actor, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · apply Subgroup.mem_sup_left
      exact ⟨signHom (Multiplicative.ofAdd (1,0)), ⟨_, rfl⟩,
        congrArg innerSL (by decide +kernel)⟩
    · apply Subgroup.mem_sup_left
      exact ⟨signHom (Multiplicative.ofAdd (0,1)), ⟨_, rfl⟩,
        congrArg innerSL (by decide +kernel)⟩
    · exact Subgroup.mem_sup_right (mem_zpowers _)
  · exact sup_le actorInnerFour_le_actor (zpowers_le.mpr (subset_closure (by simp)))

open scoped IsMulCommutative in
private theorem graph_normalizes_actorInnerFour : graphElement ∈ normalizer (actorInnerFour : Set Model) := by
  apply centralizer_le_normalizer
  intro x hx
  exact congrArg Subtype.val (mul_comm (⟨x, actorInnerFour_le_actor hx⟩ : actor)
    ⟨graphElement, subset_closure (by simp)⟩)

/-- The literal actor has order eight. -/
theorem card_actor : Nat.card actor = 8 := by
  rw [actor_eq_innerFour_sup_graph,
    card_sup_zpowers_of_normalizing_involution _ _
      (show graphElement ^ 2 = 1 from Subtype.ext (Matrix.PSL3.OuterSolvable.graph_sq (ZMod 5)))
      (fun h => graphElement_not_mem_inner (actorInnerFour_le_inner h))
      graph_normalizes_actorInnerFour, card_actorInnerFour]

/-- The marked inner intersection has exactly the four diagonal sign elements. -/
theorem card_actor_inf_inner : Nat.card (actor ⊓ inner : Subgroup Model) = 4 := by
  have hD : actorInnerFour ≤ actor ⊓ inner :=
    le_inf actorInnerFour_le_actor actorInnerFour_le_inner
  have h4 : 4 ≤ Nat.card (actor ⊓ inner : Subgroup Model) := by
    simpa only [card_actorInnerFour] using card_le_of_le hD
  have h8 : Nat.card (actor ⊓ inner : Subgroup Model) ≤ 8 := by
    simpa only [card_actor] using card_le_of_le (inf_le_left : actor ⊓ inner ≤ actor)
  have hd : 4 ∣ Nat.card (actor ⊓ inner : Subgroup Model) := by
    simpa only [card_actorInnerFour] using card_dvd_of_le hD
  have hne : Nat.card (actor ⊓ inner : Subgroup Model) ≠ 8 := by
    intro hc
    have he : actor ⊓ inner = actor := eq_of_le_of_card_ge inf_le_left (by rw [hc, card_actor])
    exact graphElement_not_mem_inner ((he ▸ inf_le_right) (subset_closure (by simp)))
  omega

/-- The literal conjugate, with Lean's left-conjugation convention. -/
@[expose] noncomputable def movedActor : Subgroup Model :=
  actor.map (MulAut.conj (innerSL witnessConjugator⁻¹)).toMonoidHom

/-- The chosen actor belongs to the full original conjugacy family. -/
theorem movedActor_mem_family : movedActor ∈ family := ⟨_, rfl⟩

/-- The first original involution becomes the swap times the other sign. -/
theorem moved_first :
    MulAut.conj (innerSL witnessConjugator⁻¹) (innerSL (Matrix.SL3.standardInvolution (ZMod 5))) =
      innerSL witnessSwap * innerSL secondDiagonal := by
  change innerSL witnessConjugator⁻¹ * innerSL (Matrix.SL3.standardInvolution (ZMod 5)) *
    (innerSL witnessConjugator⁻¹)⁻¹ = _
  rw [← map_inv, inv_inv, ← map_mul, ← map_mul, conjugate_first, map_mul]

/-- The second original involution becomes the signed swap. -/
theorem moved_second :
    MulAut.conj (innerSL witnessConjugator⁻¹) (innerSL secondDiagonal) =
      innerSL witnessSwap := by
  change innerSL witnessConjugator⁻¹ * innerSL secondDiagonal *
    (innerSL witnessConjugator⁻¹)⁻¹ = _
  rw [← map_inv, inv_inv, ← map_mul, ← map_mul, conjugate_second]

/-- With left conjugation, the outer generator has diagonal factor (1,3,2). -/
theorem moved_graph :
    MulAut.conj (innerSL witnessConjugator⁻¹) graphElement =
      innerSL witnessDiagonal * graphElement := by
  change innerSL witnessConjugator⁻¹ * graphElement * (innerSL witnessConjugator⁻¹)⁻¹ = _
  rw [← map_inv, inv_inv, mul_assoc, graph_innerSL, ← mul_assoc,
    ← map_mul, conjugate_graph_matrix]

private theorem map_three_generator_le {G H : Type*} [Group G] [Group H]
    (f : G →* H) (a b c : G) (P : Subgroup H)
    (ha : f a ∈ P) (hb : f b ∈ P) (hc : f c ∈ P) :
    (closure ({a,b,c} : Set G)).map f ≤ P := by
  rw [map_le_iff_le_comap, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact hc

/-- A subgroup containing these three literal generators contains the full
conjugate actor, including its outer generator. -/
theorem movedActor_le_of_generators {P : Subgroup Model}
    (hu : innerSL witnessSwap ∈ P) (hs : innerSL secondDiagonal ∈ P)
    (hg : innerSL witnessDiagonal * graphElement ∈ P) : movedActor ≤ P :=
  map_three_generator_le (MulAut.conj (innerSL witnessConjugator⁻¹)).toMonoidHom
    (innerSL (Matrix.SL3.standardInvolution (ZMod 5))) (innerSL secondDiagonal) graphElement P
    (moved_first.symm ▸ P.mul_mem hu hs) (moved_second.symm ▸ hu) (moved_graph.symm ▸ hg)

/-- The signed swap is an element of the actual conjugate actor. -/
theorem swap_mem_movedActor : innerSL witnessSwap ∈ movedActor := by
  refine ⟨innerSL secondDiagonal, subset_closure (by simp), ?_⟩
  exact moved_second

/-- The coordinate three-cycle moves the weak closure whenever the actual
conjugate actor lies in the ambient Sylow. -/
theorem monomial_motion_of_movedActor_le (T : Sylow 2 Model)
    (hAT : movedActor ≤ (T : Subgroup Model)) :
    ¬ monomialOvergroup ≤ normalizer (weakClosure (T : Subgroup Model) family : Set Model) := by
  let W := weakClosure (T : Subgroup Model) family
  have hAW : movedActor ≤ W := le_sSup ⟨movedActor_mem_family, hAT⟩
  have hWT : W ≤ (T : Subgroup Model) := sSup_le (fun _ h => h.2)
  have hu : innerSL witnessSwap ∈ W := hAW swap_mem_movedActor
  have hy : innerSL witnessCycle ∈ monomialOvergroup :=
    Subgroup.mem_sup_left ⟨_, witnessCycle_mem_linear, rfl⟩
  intro h
  have hv : innerSL (witnessCycle * witnessSwap * witnessCycle⁻¹) ∈ W := by
    simp only [map_mul, map_inv]
    exact ((h hy) _).mp hu
  let c : T := ⟨innerSL (witnessSwap * (witnessCycle * witnessSwap * witnessCycle⁻¹)), by
    rw [map_mul]
    exact T.mul_mem (hWT hu) (hWT hv)⟩
  have hc3 : c ^ 3 = 1 := by
    apply Subtype.ext
    change innerSL (witnessSwap * (witnessCycle * witnessSwap * witnessCycle⁻¹)) ^ 3 = 1
    rw [← map_pow, witness_product_cube, map_one]
  have hc : c = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (T.isPGroup'.orderOf_coprime (by decide : Nat.Coprime 2 3) c)
      dvd_rfl (orderOf_dvd_of_pow_eq_one hc3))
  apply witness_product_ne_one
  apply innerSL_injective
  have he : innerSL (witnessSwap * (witnessCycle * witnessSwap * witnessCycle⁻¹)) = (1 : Model) :=
    congrArg (fun x : T => (x : Model)) hc
  simpa only [map_one] using he

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveSourceAudit
