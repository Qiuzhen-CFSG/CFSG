module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.TensorSecondReflection

/-!
# The second reflection on the entire U₄ Cartan

The A and C weights determine a fixed-product torus parameter in
characteristic two: the A weight determines the SL₂ coroot, and the C
weight determines the fixed scalar. A reflection exchanging the same A
and C coordinates therefore sends (a,b) to (a,bar(b)⁻¹). Surjectivity of
the constructed Cartan supplies the parameter of its actual conjugate;
no labelled Cartan equation is assumed.

TensorEquationApplication applies this to the normalized original-source
coordinates. The argument includes the fields of orders two and four.
Source: Fong--Seitz II (8B), pp.201--202, the common-field normalization
(8.7)--(8.9); the exact torus convention is FourCells.turnParameter.
-/

@[expose] public noncomputable section
open Subgroup
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
namespace FourCartan
variable (E : Type*) [Field E] [Finite E] [CharP E 2] (σ : E ≃+* E)

theorem parameter_ext_AC (p q : FourWeyl.torusParameters E σ)
    (hA : (p.val.1 : E) / (p.val.2 : E) = (q.val.1 : E) / (q.val.2 : E))
    (hC : (p.val.1 : E) * σ (p.val.2 : E) = (q.val.1 : E) * σ (q.val.2 : E)) : p = q := by
  have hu : coroot E σ p = coroot E σ q := by
    apply Units.ext
    apply CharTwo.sq_injective
    simpa only [coroot_weight] using hA
  have hr : halfDeterminant E σ p = halfDeterminant E σ q := by
    apply Units.ext
    apply CharTwo.sq_injective
    have hc (x : FourWeyl.torusParameters E σ) :
        (x.val.1 : E) * σ (x.val.2 : E) =
          (halfDeterminant E σ x : E)^2 *
            ((coroot E σ x : E) * σ (↑((coroot E σ x)⁻¹) : E)) := by
      rw [first_factor E σ x,second_factor E σ x,map_mul,halfDeterminant_fixed]
      ring
    rw [hc p,hc q,hu] at hC
    exact mul_right_cancel₀ (mul_ne_zero (coroot E σ q).ne_zero
      ((map_ne_zero σ).mpr (coroot E σ q)⁻¹.ne_zero)) hC
  apply Subtype.ext
  apply Prod.ext <;> apply Units.ext
  · rw [first_factor E σ p,first_factor E σ q,hu,hr]
  · rw [second_factor E σ p,second_factor E σ q,hu,hr]

omit [Finite E] [CharP E 2] in
theorem turnParameter_weights (hσ : Function.Involutive σ) (p : FourWeyl.torusParameters E σ) :
    let q := FourCells.turnParameter E σ hσ p
    (q.val.1 : E) / (q.val.2 : E) = (p.val.1 : E) * σ (p.val.2 : E) ∧
    (q.val.1 : E) * σ (q.val.2 : E) = (p.val.1 : E) / (p.val.2 : E) := by
  dsimp only [FourCells.turnParameter]
  simp only [Units.val_inv_eq_inv_val,Units.coe_map]
  change (p.val.1 : E) / (σ (p.val.2 : E))⁻¹ = _ ∧
    (p.val.1 : E) * σ ((σ (p.val.2 : E))⁻¹) = _
  simp only [map_inv₀,hσ (p.val.2 : E),div_eq_mul_inv,inv_inv,and_self]
end FourCartan

open RootCoordinates HexagonStructure
variable {X E : Type*} [Group X] [Field E] [Finite E] [CharP E 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (σ : E ≃+* E) (hσ : Function.Involutive σ)
  (R : PositiveMaps (X ⧸ Q.D) (Multiplicative E)
    (Multiplicative (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.FixedField E σ))
    (Multiplicative E)
    (Multiplicative (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.FixedField E σ)))
  (cartan : FourWeyl.torusParameters E σ →* X ⧸ Q.D)
  (ht : cartan.range = Q.tits.B ⊓ Q.tits.N)
  (hAi : Function.Injective R.A) (hCi : Function.Injective R.C)
  (hwA : ∀ (p : FourWeyl.torusParameters E σ) (a : E),
    cartan p * R.A (.ofAdd a) * (cartan p)⁻¹ = R.A (.ofAdd (((p.val.1 : E)/(p.val.2 : E))*a)))
  (hwC : ∀ (p : FourWeyl.torusParameters E σ) (c : E),
    cartan p * R.C (.ofAdd c) * (cartan p)⁻¹ = R.C (.ofAdd (((p.val.1 : E)*σ (p.val.2 : E))*c)))
  (t : Q.tits.N) (ht2 : (t : X ⧸ Q.D)*(t : X ⧸ Q.D) = 1)
  (htA : ∀ a : E, (t : X ⧸ Q.D)*R.A (.ofAdd a)*t = R.C (.ofAdd a))
  (htC : ∀ c : E, (t : X ⧸ Q.D)*R.C (.ofAdd c)*t = R.A (.ofAdd c))

include ht hAi hCi hwA hwC ht2 htA htC in
theorem secondReflection_cartan (p : FourWeyl.torusParameters E σ) :
    (t : X ⧸ Q.D)*cartan p*t = cartan (FourCells.turnParameter E σ hσ p) := by
  have htinv : (t : X ⧸ Q.D)⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hp : cartan p ∈ Q.tits.B ⊓ Q.tits.N := ht ▸ ⟨p,rfl⟩
  have hm : (t : X ⧸ Q.D)*cartan p*t ∈ cartan.range := by
    rw [ht]
    simpa only [ReeSource.normalizerCartanAction_apply,htinv] using
      (ReeSource.normalizerCartanAction Q t ⟨cartan p,hp⟩).property
  obtain ⟨q,hq⟩ := hm
  have hswap (f g : E → X ⧸ Q.D)
      (hf : ∀ a, (t : X ⧸ Q.D)*f a*t = g a)
      (hg : ∀ a, (t : X ⧸ Q.D)*g a*t = f a)
      (c : E) (hc : cartan p*g 1*(cartan p)⁻¹ = g c) :
      cartan q*f 1*(cartan q)⁻¹ = f c := by
    rw [hq]
    calc
      _ = (t : X ⧸ Q.D)*(cartan p*((t : X ⧸ Q.D)*f 1*t)*(cartan p)⁻¹)*t := by
        simp only [mul_inv_rev,htinv]
        group
      _ = _ := by rw [hf,hc,hg]
  have hA : (q.val.1 : E)/(q.val.2 : E) = (p.val.1 : E)*σ (p.val.2 : E) := by
    have hh := hswap (fun a => R.A (.ofAdd a)) (fun c => R.C (.ofAdd c)) htA htC
      ((p.val.1 : E)*σ (p.val.2 : E)) (by simpa only [mul_one] using hwC p 1)
    rw [hwA,mul_one] at hh
    exact Multiplicative.ofAdd.injective (hAi hh)
  have hC : (q.val.1 : E)*σ (q.val.2 : E) = (p.val.1 : E)/(p.val.2 : E) := by
    have hh := hswap (fun c => R.C (.ofAdd c)) (fun a => R.A (.ofAdd a)) htC htA
      ((p.val.1 : E)/(p.val.2 : E)) (by simpa only [mul_one] using hwA p 1)
    rw [hwC,mul_one] at hh
    exact Multiplicative.ofAdd.injective (hCi hh)
  have he : q = FourCells.turnParameter E σ hσ p :=
    FourCartan.parameter_ext_AC E σ q _
      (hA.trans (FourCartan.turnParameter_weights E σ hσ p).1.symm)
      (hC.trans (FourCartan.turnParameter_weights E σ hσ p).2.symm)
  exact hq.symm.trans (congrArg cartan he)
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
