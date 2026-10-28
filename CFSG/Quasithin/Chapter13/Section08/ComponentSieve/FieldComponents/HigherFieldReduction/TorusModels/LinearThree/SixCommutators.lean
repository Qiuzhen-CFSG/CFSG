module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.Residuals
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.LinearThree.Borels
public import Theory.SpecificGroups.PSL3.CartanActions.SixCommutators.PureActors
public import Theory.SpecificGroups.PSL3.CartanActions.SixCommutators.StandardBounds
public import Theory.GroupAction.CyclicCommutatorTransport

/-!
# Degree-six outer commutators for the intrinsic linear-three Borel

For SL₃ and PSL₃ over a field of order 64, every outer two-element preserving
any specified Sylow two-subgroup has cyclic commutator C with the intrinsic
residual B satisfying |C/O₂(C)| > 3. The final two theorems retain the given
automorphism two-subgroup A, its Sylow stability and its inner-Sylow containment.
No torus-fixation assumption or involution restriction is imposed.

The permitted earlier classification input is stated as universal coverage
by literal GL₃ conjugations, field automorphisms and the opposition graph
representative. All quotient actions are computed. Upper triangular GL₃
conjugation is trivial on the Borel quotient; the field and graph-field
images have order at least nine and twenty-one, respectively, after retaining
the cubic scalar kernel in PSL₃. The remaining pure linear two-elements are
inner. Actual Sylow conjugacy transports the commutator and its two-core.

The source-theorem owner must instantiate the explicit raw automorphism
coverage inputs. No local action, commutator bound or exceptional-degree
centralizer theorem is included in those inputs.
Source: Aschbacher–Smith, proof of 13.8.20, printed p.954 (PDF p.971);
GLS3 Theorem 2.5.12 and §2.7 for the raw matrix automorphism factorization.
-/

public section

open scoped MatrixGroups
open Subgroup Matrix.PSL3.LinearThree Matrix.PSL3.OuterSolvable
open Matrix.PSL3.OuterSolvable.OddPrimeCoverage
open Matrix.PSL3.CartanActions.BorelQuotient
open Matrix.PSL3.CartanActions.SixCommutators
open Theory.GroupAction.OddCommutatorImage
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.LinearThree
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The source commutator bound for every nontrivial pure SL₃ field actor. -/
theorem special_standard_field_commutator (hF : Nat.card F = 2 ^ 6)
    (σ : F ≃+* F) (hσ : σ ≠ 1) :
    let S := unipotentSLSylow F (by decide : 0 < 6) hF
    let C := commutatorSubgroup (zpowers (Atlas.fieldEquivSL 3 σ)) SL(3,F)
      (intrinsicResidual S)
    3 < Nat.card (C ⧸ pCore 2 C) := by
  dsimp only
  have hB : intrinsicResidual (unipotentSLSylow F (by decide : 0 < 6) hF) = borelSL F :=
    (special_residual_eq hF (by decide) _).trans (normalizer_unipotentSL F)
  rw [hB]
  exact special_pure_field_bound F σ hF hσ

/-- The source commutator bound for every nontrivial pure PSL₃ field actor. -/
theorem projective_standard_field_commutator (hF : Nat.card F = 2 ^ 6)
    (σ : F ≃+* F) (hσ : σ ≠ 1) :
    let S := unipotentSylow F (by decide : 0 < 6) hF
    let C := commutatorSubgroup (zpowers (fieldAction F σ)) PSL(3,F)
      (intrinsicResidual S)
    3 < Nat.card (C ⧸ pCore 2 C) := by
  dsimp only
  have hB : intrinsicResidual (unipotentSylow F (by decide : 0 < 6) hF) = borel F :=
    (projective_residual_eq hF (by decide) _).trans
      (normalizer_unipotent F (by decide : 0 < 6) hF)
  rw [hB]
  exact projective_pure_field_bound F σ hF hσ

omit [CharP F 2] in
/-- Graph and mixed field-graph actors on the standard SL₃ Borel. -/
theorem special_standard_graph_commutator (hF : Nat.card F = 2 ^ 6)
    (σ : F ≃+* F) :
    let S := unipotentSLSylow F (by decide : 0 < 6) hF
    let α := Atlas.fieldEquivSL 3 σ * oppositionGraphSL F
    let C := commutatorSubgroup (zpowers α) SL(3,F) (intrinsicResidual S)
    3 < Nat.card (C ⧸ pCore 2 C) := by
  dsimp only
  have hB : intrinsicResidual (unipotentSLSylow F (by decide : 0 < 6) hF) = borelSL F :=
    (special_residual_eq hF (by decide) _).trans (normalizer_unipotentSL F)
  rw [hB]
  exact special_pure_graph_bound F σ hF

omit [CharP F 2] in
/-- Graph and mixed field-graph actors on the standard PSL₃ Borel. -/
theorem projective_standard_graph_commutator (hF : Nat.card F = 2 ^ 6)
    (σ : F ≃+* F) :
    let S := unipotentSylow F (by decide : 0 < 6) hF
    let α := fieldAction F σ * oppositionGraph F
    let C := commutatorSubgroup (zpowers α) PSL(3,F) (intrinsicResidual S)
    3 < Nat.card (C ⧸ pCore 2 C) := by
  dsimp only
  have hB : intrinsicResidual (unipotentSylow F (by decide : 0 < 6) hF) = borel F :=
    (projective_residual_eq hF (by decide) _).trans
      (normalizer_unipotent F (by decide : 0 < 6) hF)
  rw [hB]
  exact projective_pure_graph_bound F σ hF

/-- Every Sylow-preserving outer two-element satisfies the SL₃ bound. -/
theorem special_outer_sylow_bound (hF : Nat.card F = 2 ^ 6)
    (hcover : SpecialCoverage F) (S : Sylow 2 SL(3,F)) (α : MulAut SL(3,F))
    (hS : (S : Subgroup SL(3,F)).map α.toMonoidHom = S)
    (hα : ∃ k : ℕ, α ^ (2 ^ k) = 1) (ho : α ∉ MulAut.innerSubgroup SL(3,F)) :
    let C := commutatorSubgroup (zpowers α) SL(3,F) (intrinsicResidual S)
    3 < Nat.card (C ⧸ pCore 2 C) := by
  obtain ⟨g,hg,hgB⟩ := sylowSL_normalizer_conjugate F (by decide : 0 < 6) hF S
  let e : SL(3,F) ≃* SL(3,F) := (MulAut.conj g).symm
  let β := MulAut.congr e α
  have hU : (unipotentSL F).map β.toMonoidHom = unipotentSL F :=
    congr_symm_stabilizes (MulAut.conj g) α (unipotentSL F) S hg hS
  have hbound := special_standard_outer_bound F hF hcover β hU
    (congr_two_power e α hα) (congr_outer e α ho)
  have hB : (intrinsicResidual S).map e.toMonoidHom = borelSL F := by
    rw [special_residual_eq hF (by decide)]
    exact map_symm_of_map_eq (MulAut.conj g) _ _ hgB
  dsimp only
  rw [card_cyclic_commutator_quotient e α (intrinsicResidual S),hB]
  exact hbound

/-- Every Sylow-preserving outer two-element satisfies the PSL₃ bound. -/
theorem projective_outer_sylow_bound (hF : Nat.card F = 2 ^ 6)
    (hcover : ProjectiveCoverage F) (S : Sylow 2 PSL(3,F)) (α : MulAut PSL(3,F))
    (hS : (S : Subgroup PSL(3,F)).map α.toMonoidHom = S)
    (hα : ∃ k : ℕ, α ^ (2 ^ k) = 1) (ho : α ∉ MulAut.innerSubgroup PSL(3,F)) :
    let C := commutatorSubgroup (zpowers α) PSL(3,F) (intrinsicResidual S)
    3 < Nat.card (C ⧸ pCore 2 C) := by
  obtain ⟨g,hg,hgB⟩ := sylow_normalizer_conjugate F (by decide : 0 < 6) hF S
  let e : PSL(3,F) ≃* PSL(3,F) := (MulAut.conj g).symm
  let β := MulAut.congr e α
  have hU : (unipotent F).map β.toMonoidHom = unipotent F :=
    congr_symm_stabilizes (MulAut.conj g) α (unipotent F) S hg hS
  have hbound := projective_standard_outer_bound F hF hcover β hU
    (congr_two_power e α hα) (congr_outer e α ho)
  have hB : (intrinsicResidual S).map e.toMonoidHom = borel F := by
    rw [projective_residual_eq hF (by decide)]
    exact map_symm_of_map_eq (MulAut.conj g) _ _ hgB
  dsimp only
  rw [card_cyclic_commutator_quotient e α (intrinsicResidual S),hB]
  exact hbound

/-- The degree-six SL₃ commutator assertion with the source automorphism
subgroup hypotheses; only raw earlier automorphism coverage remains an input. -/
theorem special_six_outer_commutator (hF : Nat.card F = 2 ^ 6)
    (hcover : SpecialCoverage F) (S : Sylow 2 SL(3,F))
    (A : Subgroup (MulAut SL(3,F))) (hA : IsPGroup 2 A)
    (hS : StabilizesSylow A S) (_hinner : innerSylow S ≤ A)
    (α : MulAut SL(3,F)) (hα : α ∈ A) (ho : α ∉ MulAut.innerSubgroup SL(3,F)) :
    let B := intrinsicResidual S
    let C := commutatorSubgroup (zpowers α) SL(3,F) B
    3 < Nat.card (C ⧸ pCore 2 C) := by
  apply special_outer_sylow_bound hF hcover S α (hS α hα) _ ho
  obtain ⟨k,hk⟩ := hA ⟨α,hα⟩
  exact ⟨k,congrArg Subtype.val hk⟩

/-- The degree-six PSL₃ commutator assertion with its actual cubic scalar
quotient and the source automorphism subgroup hypotheses. -/
theorem projective_six_outer_commutator (hF : Nat.card F = 2 ^ 6)
    (hcover : ProjectiveCoverage F) (S : Sylow 2 PSL(3,F))
    (A : Subgroup (MulAut PSL(3,F))) (hA : IsPGroup 2 A)
    (hS : StabilizesSylow A S) (_hinner : innerSylow S ≤ A)
    (α : MulAut PSL(3,F)) (hα : α ∈ A) (ho : α ∉ MulAut.innerSubgroup PSL(3,F)) :
    let B := intrinsicResidual S
    let C := commutatorSubgroup (zpowers α) PSL(3,F) B
    3 < Nat.card (C ⧸ pCore 2 C) := by
  apply projective_outer_sylow_bound hF hcover S α (hS α hα) _ ho
  obtain ⟨k,hk⟩ := hA ⟨α,hα⟩
  exact ⟨k,congrArg Subtype.val hk⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.LinearThree
