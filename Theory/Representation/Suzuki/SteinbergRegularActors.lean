module
public import Theory.Representation.Suzuki.SmallDegree.Classification.SimpleDistinct.FixedLine
public import Theory.Representation.PGroupRegularCoordinates
public import Theory.Representation.TwistedRegularActor

/-!
# Regular coordinates and displacement for the Suzuki Steinberg tensor

The full Frobenius tensor has the order of the literal upper root subgroup
as its dimension and a unique root-fixed line. The p-group coefficient map
therefore gives its regular coordinates over every coefficient extension.
The companion actor calculation shows that an involutory twisted regular
actor moving at most eighteen dimensions fixes this entire module.

The bound eighteen is twice the terminal actor rank bound nine; establishing
that rank bound on an original actor and constructing its isotypic coordinates
remain separate source inputs. Source: Aschbacher–Smith §13.6, printed p.935,
and GLS3 2.8.2–2.8.9 for the concrete Steinberg tensor.
-/

public noncomputable section
open Module Representation
open Representation.BinaryOffender.NaturalTensor
namespace Representation.SuzukiSmallDegree
open BenderSuzuki.MatrixGroups SuzukiNatural

/-- The full Suzuki Steinberg tensor is the regular module on its literal
upper root subgroup, over every defining-characteristic coefficient extension. -/
theorem full_tensor_regular_coordinates (m : ℕ) (hm : 1 ≤ m)
    (K : Type*) [Field K] [Algebra (F m) K] :
    ∃ e : TensorSpace m K Finset.univ ≃ₗ[K] (SuzukiRootSubgroup m → K),
      ∀ (g : SuzukiRootSubgroup m) v x,
        e (tensorRep m K Finset.univ g.val v) x = e v (g⁻¹ * x) := by
  classical
  let : Fintype (SuzukiRootSubgroup m) := Fintype.ofFinite _
  let : CharP K 2 := charP_of_injective_algebraMap (algebraMap (F m) K).injective 2
  let ρ := (tensorRep m K Finset.univ).comp (SuzukiRootSubgroup m).subtype
  apply TwistedRegular.exists_regular_coordinates ρ
    (z := tensorHighestVector m K Finset.univ)
  · have hchar : ringChar K = 2 := ringChar.eq K 2
    rw [hchar]; decide
  · rw [ringChar.eq K 2]
    exact suzukiRootSubgroup_isPGroup m (by omega)
  · exact tensorHighestVector_ne_zero m K _
  · intro v hv
    exact tensor_fixed_root m hm K Finset.univ v (fun g hg => hv ⟨g,hg⟩)
  · rw [finrank_tensorSpace, Fintype.card_eq_nat_card, suzukiRootSubgroup_card m (by omega)]
    simp only [Finset.card_univ, Fintype.card_fin]
    rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul, ← pow_mul, Nat.mul_comm]
/-- On a nonzero Steinberg multiplicity space, an involutory actor with
at most eighteen moved dimensions has trivial full action. -/
theorem twisted_root_action_trivial_of_small_displacement
    (m : ℕ) (hm : 1 ≤ m) {K A M : Type*} [Field K] [Group A]
    [AddCommGroup M] [Module K M] [FiniteDimensional K M] [Nontrivial M]
    (φ : A →* SuzukiRootSubgroup m) (τ : Representation K A M)
    (σ : Representation K A (SuzukiRootSubgroup m → M))
    (hσ : ∀ a f x, σ a f x = τ a (f ((φ a)⁻¹ * x)))
    (hinvol : ∀ a : A, a * a = 1)
    (hsmall : ∀ a, operatorFixedCodim (σ a) ≤ 18) :
    ∀ a, σ a = 1 := by
  classical
  let : Fintype (SuzukiRootSubgroup m) := Fintype.ofFinite _
  have hsize : 64 ≤ Fintype.card (SuzukiRootSubgroup m) := by
    rw [Fintype.card_eq_nat_card, suzukiRootSubgroup_card m (by omega)]
    rw [← pow_mul]
    change 2 ^ 6 ≤ 2 ^ ((2 * m + 1) * 2)
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hdim : 1 ≤ finrank K M := Module.finrank_pos
  intro a
  have hphi : φ a = 1 := by
    by_contra hne
    have hs := TwistedRegular.shift_dimension_le_twice_displacement φ τ σ hσ a hne
      (by rw [← map_mul, hinvol, map_one])
    have h := hsmall a
    nlinarith
  have hmult (v : M) : τ a v = v := by
    by_contra hne
    have hs := TwistedRegular.card_le_displacement_of_pure_multiplicity
      φ τ σ hσ a hphi ⟨v,hne⟩
    have h := hsmall a
    omega
  apply LinearMap.ext
  intro f
  funext x
  rw [hσ, hphi, inv_one, one_mul, hmult]
  rfl
/-- The placed quadratic actor fixes its Steinberg isotypic part under the
terminal small-ratio inequality, retaining the cardinality of the full actor. -/
theorem twisted_root_action_trivial_of_small_ratio
    (m : ℕ) (hm : 1 ≤ m) {K A M : Type*} [Field K] [Group A]
    [AddCommGroup M] [Module K M] [FiniteDimensional K M] [Nontrivial M]
    (φ : A →* SuzukiRootSubgroup m) (τ : Representation K A M)
    (σ : Representation K A (SuzukiRootSubgroup m → M))
    (hσ : ∀ a f x, σ a f x = τ a (f ((φ a)⁻¹ * x)))
    (hinvol : ∀ a : A, a * a = 1)
    (hquad : ∀ a b v, σ a (σ b v - v) = σ b v - v)
    (hker : Nat.card φ.ker ≤ 256)
    (hsmall : ∀ a, operatorFixedCodim (σ a) ≤ 2 * Nat.log 2 (Nat.card A)) :
    ∀ a, σ a = 1 := by
  have hr := TwistedRegular.quadratic_actor_rank_le_nine φ τ σ hσ hquad hker
  apply twisted_root_action_trivial_of_small_displacement m hm φ τ σ hσ hinvol
  intro a
  have h := hsmall a
  omega
end Representation.SuzukiSmallDegree
