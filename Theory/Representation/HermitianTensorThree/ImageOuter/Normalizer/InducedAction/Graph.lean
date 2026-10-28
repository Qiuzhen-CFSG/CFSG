module

public import Theory.Representation.HermitianTensorThree.ImageOuter.Normalizer.Contracts
public import Theory.SpecificGroups.PSL3.OuterSolvable.Actions
public import Theory.LinearAlgebra.SemilinearTrace
/-!
# Excluding graph intertwiners on the descended Hermitian tensor

The binary companion matrix of t³+t+1 has descended trace zero; its inverse
transpose has descended trace one. Both traces are computed on the literal
Hermitian space using its three fixed-field diagonal coordinates and three
extension-field off-diagonal coordinates. The only nonzero diagonal block
in the first calculation is the field involution on E. Its trace over F is
zero: in characteristic two its difference from the identity is nilpotent,
and [E:F]=2.

Semilinear conjugation transports trace by its coefficient automorphism,
which fixes zero and one. Thus inverse transpose has no semilinear
intertwiner. This computation works for every positive half-degree,
including those for which binary traces alone would lose the distinction.
No change of carrier or scalar-extension assertion is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.4.2 setup,
printed p.380. The matrix description of the A₂ graph automorphism is
GLS3, Theorem 2.5.12 and §2.7.
-/

public section
noncomputable section
namespace Representation.HermitianTensorThree.ImageOuter
open Matrix.PSL3.OuterSolvable
variable (n : ℕ) [NeZero n]

private def traceWitness : Cover n := ⟨!![0,0,1;1,0,1;0,1,0], by
  simp [Matrix.det_fin_three]⟩
private def graphWitness : Cover n := ⟨!![1,0,1;1,0,0;0,1,0], by
  simp [Matrix.det_fin_three]⟩
omit [NeZero n] in
private theorem graph_traceWitness : graphSL (E n) (traceWitness n) = graphWitness n := by
  change (Matrix.SpecialLinearGroup.transpose (traceWitness n))⁻¹ = graphWitness n
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  change (traceWitness n).val.transpose * (graphWitness n).val = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [traceWitness, graphWitness, Matrix.mul_apply, Fin.sum_univ_succ, CharTwo.add_self_eq_zero]

private theorem trace_prod_diag {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (f : (V × W) →ₗ[K] (V × W)) :
    LinearMap.trace K _ f =
      LinearMap.trace K V ((LinearMap.fst K V W).comp (f.comp (LinearMap.inl K V W))) +
      LinearMap.trace K W ((LinearMap.snd K V W).comp (f.comp (LinearMap.inr K V W))) := by
  have h : f = (f.comp (LinearMap.inl K V W)).comp (LinearMap.fst K V W) +
      (f.comp (LinearMap.inr K V W)).comp (LinearMap.snd K V W) := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.inl_apply,
      LinearMap.inr_apply, LinearMap.fst_apply, LinearMap.snd_apply, ← map_add]
    simp
  conv_lhs => rw [h, map_add]
  exact congrArg₂ (· + ·) (LinearMap.trace_comp_comm' _ _) (LinearMap.trace_comp_comm' _ _)

private theorem trace_pi_diag {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : (Fin 3 → V) →ₗ[K] (Fin 3 → V)) :
    LinearMap.trace K _ f = ∑ i : Fin 3,
      LinearMap.trace K V ((LinearMap.proj i).comp (f.comp (LinearMap.single K (fun _ : Fin 3 => V) i))) := by
  have h : f = ∑ i : Fin 3,
      (f.comp (LinearMap.single K (fun _ : Fin 3 => V) i)).comp (LinearMap.proj i) := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.single_apply,
      LinearMap.proj_apply, ← map_sum]
    congr 1
    ext j
    simp
  conv_lhs => rw [h, map_sum]
  exact Finset.sum_congr rfl (fun i _ => LinearMap.trace_comp_comm' _ _)

private theorem trace_sigma :
    LinearMap.trace (F n) (E n) (sigmaAlg n).toLinearMap = 0 := by
  have hn : IsNilpotent ((sigmaAlg n).toLinearMap - (1 : Module.End (F n) (E n))) := by
    refine ⟨2, ?_⟩
    ext x
    simp only [pow_two, Module.End.mul_apply, LinearMap.sub_apply,
      Module.End.one_apply, map_sub]
    change sigma n (sigma n x) - sigma n x - (sigma n x - x) = 0
    rw [sigma_involutive]
    simp only [CharTwo.sub_eq_add]
    calc
      _ = (x + x) + (sigma n x + sigma n x) := by abel
      _ = 0 := by simp [CharTwo.add_self_eq_zero]
  have ht := (LinearMap.isNilpotent_trace_of_isNilpotent hn).eq_zero
  rw [map_sub, LinearMap.trace_one, finrank_E] at ht
  have h2 : (2 : F n) = 0 := by simpa only [one_add_one_eq_two] using (CharTwo.add_self_eq_zero (1 : F n))
  change LinearMap.trace (F n) (E n) (sigmaAlg n).toLinearMap - (2 : F n) = 0 at ht
  rwa [h2, sub_zero] at ht

private abbrev Coords := (Fin 3 → F n) × (Fin 3 → E n)
private def coordAction (a : Cover n) : Module.End (F n) (Coords n) :=
  (coordinates n).conj (action n a)

private def diagBlock (a : Cover n) (i : Fin 3) : Module.End (F n) (F n) :=
  (LinearMap.proj i).comp ((LinearMap.fst (F n) _ _).comp
    ((coordAction n a).comp ((LinearMap.inl (F n) _ _).comp
      (LinearMap.single (F n) (fun _ : Fin 3 => F n) i))))
private def offBlock (a : Cover n) (i : Fin 3) : Module.End (F n) (E n) :=
  (LinearMap.proj i).comp ((LinearMap.snd (F n) _ _).comp
    ((coordAction n a).comp ((LinearMap.inr (F n) _ _).comp
      (LinearMap.single (F n) (fun _ : Fin 3 => E n) i))))

private theorem trace_blocks (a : Cover n) :
    LinearMap.trace (F n) (Space n) (action n a) =
      (∑ i : Fin 3, LinearMap.trace (F n) (F n) (diagBlock n a i)) +
      (∑ i : Fin 3, LinearMap.trace (F n) (E n) (offBlock n a i)) := by
  rw [← LinearMap.trace_conj' _ (coordinates n)]
  change LinearMap.trace (F n) (Coords n) (coordAction n a) = _
  rw [trace_prod_diag, trace_pi_diag, trace_pi_diag]
  rfl

private theorem witness_diag (i : Fin 3) : diagBlock n (traceWitness n) i = 0 := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  change ((traceWitness n).val * ((coordinates n).symm (Pi.single i c, 0)).val *
    adjoint n (traceWitness n).val) i i = 0
  fin_cases i <;>
    simp [coordinates, traceWitness, Matrix.mul_apply, adjoint, Fin.sum_univ_succ]

private theorem witness_off (i : Fin 3) : offBlock n (traceWitness n) i =
    if i = 2 then (sigmaAlg n).toLinearMap else 0 := by
  apply LinearMap.ext
  intro c
  let X := ((coordinates n).symm (0, Pi.single i c)).val
  let Y := (traceWitness n).val * X * adjoint n (traceWitness n).val
  change ![Y 0 1, Y 0 2, Y 1 2] i = _
  fin_cases i <;>
    simp [Y, X, coordinates, traceWitness, Matrix.vecMul, dotProduct, adjoint, Fin.sum_univ_succ]
  rfl

private theorem graph_diag (i : Fin 3) : diagBlock n (graphWitness n) i =
    if i = 0 then 1 else 0 := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  let X := ((coordinates n).symm (Pi.single i c, 0)).val
  change ((graphWitness n).val * X * adjoint n (graphWitness n).val) i i = _
  fin_cases i <;>
    simp [X, coordinates, graphWitness, Matrix.mul_apply, adjoint, Fin.sum_univ_succ]

private theorem graph_off (i : Fin 3) : offBlock n (graphWitness n) i = 0 := by
  apply LinearMap.ext
  intro c
  let X := ((coordinates n).symm (0, Pi.single i c)).val
  let Y := (graphWitness n).val * X * adjoint n (graphWitness n).val
  change ![Y 0 1, Y 0 2, Y 1 2] i = 0
  fin_cases i <;>
    simp [Y, X, coordinates, graphWitness, Matrix.vecMul, dotProduct, adjoint, Fin.sum_univ_succ]

private theorem trace_witness : LinearMap.trace (F n) (Space n) (action n (traceWitness n)) = 0 := by
  rw [trace_blocks]
  simp [witness_diag, witness_off, trace_sigma, Fin.sum_univ_succ]

private theorem trace_graph_witness :
    LinearMap.trace (F n) (Space n) (action n (graphSL (E n) (traceWitness n))) = 1 := by
  rw [graph_traceWitness, trace_blocks]
  simp [graph_diag, graph_off, LinearMap.trace_one, Fin.sum_univ_succ]

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- Inverse transpose cannot be implemented by a fixed-field semilinear equivalence
on the actual descended Hermitian representation. -/
theorem graph_not_implemented_semilinear
    (e : Space n ≃ₗ[ZMod 2] Space n) (τ : F n ≃+* F n)
    (hτ : ∀ (c : F n) (X : Space n), e (c • X) = τ c • e X)
    (h : ∀ a : Cover n, e * binaryActionHom n a * e⁻¹ =
      binaryActionHom n (graphSL (E n) a)) : False := by
  let es : LinearEquiv (σ' := (τ.symm : F n →+* F n)) (τ : F n →+* F n) (Space n) (Space n) := {
    __ := e.toAddEquiv
    map_smul' := hτ }
  have hconj (a : Cover n) : es.conj (action n a) = action n (graphSL (E n) a) := by
    apply LinearMap.ext
    intro X
    exact congrArg (fun f : Space n ≃ₗ[ZMod 2] Space n => f X) (h a)
  have ht := LinearMap.trace_conj_semilinear τ (action n (traceWitness n)) es
  rw [hconj, trace_graph_witness, trace_witness, map_zero] at ht
  exact one_ne_zero ht

end Representation.HermitianTensorThree.ImageOuter
