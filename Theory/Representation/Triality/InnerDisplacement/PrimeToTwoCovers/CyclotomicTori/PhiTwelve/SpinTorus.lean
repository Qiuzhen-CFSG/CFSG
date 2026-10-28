module

public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiTwelve.Coordinates
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.GraphField
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.PointGeneration.CorootReflection
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.Diagram.Torus

/-!
# The twelfth-cyclotomic torus on actual Spin points

The literal simple-coroot product realizes the scalar coordinates from
`Coordinates`. Inverse conjugation by `n₁ n₀` acts by the first-arm reflection
after the central reflection. Composing this with graph-field Frobenius fixes
the one-parameter family `(z, z^(q³+1), z^q, z^(q²))` of order q⁴−q²+1.
Faithfulness of the published coroot parametrization makes this a genuine
embedding into the Spin point group. `Descent` conjugates it into the ordinary
fixed group and transports it to the original finite carrier.

Source: GLS3 1.12.1 and §2.2, with `h(t) = n(1)⁻¹ n(t)` and the forward
three-arm graph action. The normalizer multiplication order is explicit.
-/

@[expose] public section

noncomputable section
namespace Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiTwelve
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open Triality.SimplyConnected.Pinning.CorootTorus
open Theory.AlgebraicGroup.StandardRootSystem
variable (k : Type*) [Field k] [IsAlgClosed k] [CharP k 2]

private def reflected (i : Fin 4) (t : Fin 4 → kˣ) : Fin 4 → kˣ :=
  (List.ofFn fun j : Fin 4 => Pi.mulSingle j (t j) *
    Pi.mulSingle i (t j ^ (-typeDCartanMatrix 2 j i))).prod

private theorem parameter_reflected (i : Fin 4) (t : Fin 4 → kˣ) :
    parameter k (reflected k i t) =
      (simpleNormalizer k i)⁻¹ * parameter k t * simpleNormalizer k i := by
  have hs (j : Fin 4) (u : kˣ) : parameter k (Pi.mulSingle j u) = simpleCoroot k j u :=
    parameter_single k j u
  let f := MulAut.conj ((simpleNormalizer k i)⁻¹)
  have hj (j : Fin 4) :
      parameter k (Pi.mulSingle j (t j) *
          Pi.mulSingle i (t j ^ (-typeDCartanMatrix 2 j i))) =
        f (simpleCoroot k j (t j)) := by
    rw [parameter_mul, hs, hs]
    simpa only [f, MulAut.conj_apply, inv_inv] using
      (simpleNormalizer_simpleCoroot_conjugation k i j (t j)).symm
  have h : parameter k (reflected k i t) = f (parameter k t) := by
    unfold reflected
    change CorootTorus.pointHom k _ = f (parameter k t)
    rw [map_list_prod, parameter, map_list_prod]
    simp only [List.map_ofFn]
    congr 2
    funext j
    exact hj j
  simpa only [f, MulAut.conj_apply, inv_inv] using h

omit [IsAlgClosed k] [CharP k 2] in
private theorem reflected_apply (i j : Fin 4) (t : Fin 4 → kˣ) :
    reflected k i t j = t j * (if j = i then
      ∏ l : Fin 4, t l ^ (-typeDCartanMatrix 2 l i) else 1) := by
  simp only [reflected, List.prod_ofFn, Finset.prod_apply, Pi.mul_apply,
    Finset.prod_mul_distrib]
  congr 1
  · simp [Pi.mulSingle_apply]
  · by_cases h : j = i <;> simp [h]

omit [IsAlgClosed k] [CharP k 2] in
private theorem reflected_zero (t : Fin 4 → kˣ) :
    reflected k 0 t = ![t 1 / t 0, t 1, t 2, t 3] := by
  have hC : ∀ j : Fin 4, typeDCartanMatrix 2 j 0 = ![2, -1, 0, 0] j := by decide +kernel
  funext i
  rw [reflected_apply]
  simp only [hC]
  fin_cases i <;>
    norm_num [Fin.prod_univ_four, Matrix.cons_val_two, Matrix.cons_val_three,
      div_eq_mul_inv, pow_two, mul_assoc, mul_comm, mul_left_comm] <;> rfl

omit [IsAlgClosed k] [CharP k 2] in
private theorem reflected_one (t : Fin 4 → kˣ) :
    reflected k 1 t = ![t 0, t 0 * t 2 * t 3 / t 1, t 2, t 3] := by
  have hC : ∀ j : Fin 4, typeDCartanMatrix 2 j 1 = ![-1, 2, -1, -1] j := by decide +kernel
  funext i
  rw [reflected_apply]
  simp only [hC]
  fin_cases i
  · change t 0 * 1 = t 0
    exact mul_one _
  · change t 1 * (∏ l : Fin 4, t l ^ (- ![-1, 2, -1, -1] l)) =
      t 0 * t 2 * t 3 / t 1
    rw [Fin.prod_univ_four]
    change t 1 * (t 0 ^ (1 : ℤ) * t 1 ^ (-2 : ℤ) * t 2 ^ (1 : ℤ) * t 3 ^ (1 : ℤ)) = _
    simp only [zpow_one, zpow_neg, zpow_two, mul_inv_rev, div_eq_mul_inv]
    calc
      _ = (t 1 * (t 1)⁻¹) * (t 0 * t 2 * t 3 * (t 1)⁻¹) := by ac_rfl
      _ = _ := by rw [mul_inv_cancel, one_mul]
  · change t 2 * 1 = t 2
    exact mul_one _
  · change t 3 * 1 = t 3
    exact mul_one _

omit [IsAlgClosed k] [CharP k 2] in
private theorem reflected_graph (q : ℕ) (t : Fin 4 → kˣ) :
    reflected k 0 (reflected k 1
      (fun i => (t (typeD4DiagramPermutation.symm i)) ^ q)) = twist q t := by
  rw [reflected_zero, reflected_one]
  funext i
  fin_cases i <;>
    simp [typeD4DiagramPermutation, twist, div_eq_mul_inv, mul_pow, mul_assoc,
      mul_comm, mul_left_comm]

/-- This exact normalizer order realizes the two reflections by inverse conjugation. -/
def normalizerWord : Points k := simpleNormalizer k 1 * simpleNormalizer k 0

/-- The proposed cyclotomic coordinates have the stated action on actual Spin points. -/
theorem normalizer_graphField_parameter (n : ℕ) (t : Fin 4 → kˣ) :
    (normalizerWord k)⁻¹ * GraphField.sigma k n (parameter k t) * normalizerWord k =
      parameter k (twist (2 ^ n) t) := by
  have hg : Diagram.pinnedAut k (parameter k t) =
      parameter k (Diagram.permutedParameters k t) :=
    (Diagram.pinnedAut_isPinned k).parameter k t
  rw [GraphField.sigma_apply, hg, GraphField.frobenius_parameter]
  rw [← reflected_graph k, parameter_reflected, parameter_reflected]
  simp only [normalizerWord, mul_inv_rev, mul_assoc, Diagram.permutedParameters, Function.comp_apply]

/-- A faithful cyclic torus in the inner-twisted graph-field fixed group. -/
def spinEmbedding (n : ℕ) : Parameters k n →* Points k :=
  (CorootTorus.pointHom k).comp ((expand (2 ^ n)).comp (rootsOfUnity _ k).subtype)

theorem spinEmbedding_injective (n : ℕ) : Function.Injective (spinEmbedding k n) :=
  (parameter_injective k).comp ((expand_injective _).comp Subtype.val_injective)

theorem spinEmbedding_twisted (n : ℕ) (z : Parameters k n) :
    (normalizerWord k)⁻¹ * GraphField.sigma k n (spinEmbedding k n z) * normalizerWord k =
      spinEmbedding k n z := by
  change (normalizerWord k)⁻¹ * GraphField.sigma k n (parameter k (expand (2 ^ n) (z : kˣ))) * normalizerWord k = _
  rw [normalizer_graphField_parameter, expand_fixed (one_le_pow₀ (by decide)) _ z.property]
  rfl

end Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiTwelve
