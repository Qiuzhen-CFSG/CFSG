module
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.ExchangedProductDisplacement
public import Theory.Representation.SchurLinearOperator
public import Theory.Representation.ReeF4.BinaryDegree.SchurDescent
public import Theory.Representation.BinaryOffender.SchurNormalizerDisplacement
public import Theory.Representation.SL2.SchurTensorDisplacement

/-!
# Degree bounds for exchanged binary products

Faithful tensor factors have the degree lower bound supplied by the actual
factor action, so their irreducible product has at least the square of that
degree. An involution exchanging the factors moves at least `k.choose 2`
dimensions when every faithful absolute factor has degree at least `k`.

The exact symmetric tensor calculation applies over the original Schur field.
If the exchanger acts nontrivially on that field, its displacement is at least
half the entire binary degree, which gives the same lower bound. No linearity
hypothesis on the exchanger over the Schur field is retained.

The odd prime-field PSL₂ square is the consumer in `SL2.OddSquareExchange`.
Source: Aschbacher--Smith D.3.7, printed pp.197--198.
-/

public noncomputable section
open scoped TensorProduct MonoidAlgebra
open Module Representation
open Representation.QuadraticFourGroup.TensorClassification
namespace Representation.ExchangedProduct
variable {F G V : Type*} [Field F] [Group G]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]

omit [FiniteDimensional F V] in
private theorem factors_faithful
    (ρ : Representation F (G × G) V) (hf : Function.Injective ρ)
    {d e : ℕ} (τ : Representation F G (Fin d → F))
    (μ : Representation F G (Fin e → F))
    (E : ρ.Equiv (externalTensor τ μ)) :
    Function.Injective τ ∧ Function.Injective μ := by
  constructor
  · intro a b hab
    apply (show (a, (1 : G)) = (b,1) → a = b from congrArg Prod.fst)
    apply hf
    ext v
    apply E.injective
    have he (g : G × G) : E (ρ g v) = externalTensor τ μ g (E v) :=
      LinearMap.congr_fun (E.isIntertwining' g) v
    change E (ρ (a,1) v) = E (ρ (b,1) v)
    rw [he,he,externalTensor_apply,externalTensor_apply,hab]
  · intro a b hab
    apply (show ((1 : G),a) = (1,b) → a = b from congrArg Prod.snd)
    apply hf
    ext v
    apply E.injective
    have he (g : G × G) : E (ρ g v) = externalTensor τ μ g (E v) :=
      LinearMap.congr_fun (E.isIntertwining' g) v
    change E (ρ (1,a) v) = E (ρ (1,b) v)
    rw [he,he,externalTensor_apply,externalTensor_apply,hab]

variable [IsAlgClosed F]
theorem square_finrank_ge_of_factor_degree
    (ρ : Representation F (G × G) V) [ρ.IsIrreducible]
    (hf : Function.Injective ρ) (k : ℕ)
    (hd : ∀ (d : ℕ) (τ : Representation F G (Fin d → F)),
      Function.Injective τ → k ≤ d) : k*k ≤ finrank F V := by
  obtain ⟨d,e,τ,μ,_,_,⟨E⟩⟩ := ProductFactors.exists_irreducible_externalTensor_factors ρ
  have hfaith := factors_faithful ρ hf τ μ E
  have hlow := Nat.mul_le_mul (hd d τ hfaith.1) (hd e μ hfaith.2)
  rw [E.toLinearEquiv.finrank_eq,Module.finrank_tensorProduct]
  simpa using hlow

variable [CharP F 2]
theorem exchange_displacement_ge_of_factor_degree
    (ρ : Representation F (G × G) V) [ρ.IsIrreducible]
    (hf : Function.Injective ρ) (k : ℕ)
    (hd : ∀ (d : ℕ) (τ : Representation F G (Fin d → F)),
      Function.Injective τ → k ≤ d)
    (T : Module.End F V) (h2 : T*T=1)
    (hT : ∀ g v, T (ρ g v) = ρ (g.2,g.1) (T v)) :
    k.choose 2 ≤ finrank F (T-1).range := by
  obtain ⟨d,τ,_,⟨E⟩,hr⟩ := exists_symmetric_tensor ρ T h2 hT
  rw [hr]
  exact Nat.choose_le_choose 2 (hd d τ (factors_faithful ρ hf τ τ E).1)
end Representation.ExchangedProduct

namespace Representation.ExchangedProduct
open FrobeniusTensor BinaryOffender Subgroup
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) (G × G) V) [ρ.IsIrreducible]

/-- The degree of each faithful absolute factor bounds the original binary square. -/
theorem binary_square_finrank_ge_of_factor_degree
    (hf : Function.Injective ρ) (k : ℕ)
    (hd : ∀ (d : ℕ) (τ : Representation (Closure ρ) G (Fin d → Closure ρ)),
      Function.Injective τ → k ≤ d) : k*k ≤ finrank (ZMod 2) V :=
  (square_finrank_ge_of_factor_degree (absoluteRep ρ)
    (absoluteRep_injective ρ hf) k hd).trans (absolute_finrank_le_binary ρ)

/-- The exact exchange bound descends to binary dimension, including operators
that act nontrivially on the actual Schur field. -/
theorem binary_exchange_displacement_ge_of_factor_degree
    (hf : Function.Injective ρ) (k : ℕ)
    (hd : ∀ (d : ℕ) (τ : Representation (Closure ρ) G (Fin d → Closure ρ)),
      Function.Injective τ → k ≤ d)
    (T : Module.End (ZMod 2) V) (h2 : T*T=1)
    (hT : ∀ g v, T (ρ g v) = ρ (g.2,g.1) (T v)) :
    k.choose 2 ≤ finrank (ZMod 2) (T-1).range := by
  let u : (Module.End (ZMod 2) V)ˣ := ⟨T,T,h2,h2⟩
  have hu2 : u*u=1 := Units.ext h2
  have huinv : u⁻¹=u := inv_eq_of_mul_eq_one_left hu2
  have hconj (g : G × G) : u * ρ.asGroupHom g * u⁻¹ = ρ.asGroupHom (g.2,g.1) := by
    apply Units.ext
    apply LinearMap.ext
    intro v
    change T (ρ g (T v)) = ρ (g.2,g.1) v
    rw [hT]
    exact congrArg (ρ (g.2,g.1)) (LinearMap.congr_fun h2 v)
  have hu : u ∈ linearNormalizer ρ := by
    apply mem_normalizer_iff.mpr
    intro x
    constructor
    · rintro ⟨g,rfl⟩
      exact ⟨(g.2,g.1),(hconj g).symm⟩
    · rintro ⟨g,hg⟩
      have hh := congrArg (fun z => u*z*u⁻¹) hg
      rw [hconj] at hh
      have hround : u*(u*x*u⁻¹)*u⁻¹=x := by
        rw [huinv]
        calc
          u*(u*x*u)*u = (u*u)*x*(u*u) := by group
          _ = x := by rw [hu2,one_mul,mul_one]
      rw [hround] at hh
      exact ⟨(g.2,g.1),hh⟩
  let a : linearNormalizer ρ := ⟨u,hu⟩
  by_cases hs : SchurNormalizer.IsSchurLinear ρ a
  · let E := SchurField ρ
    let F := Closure ρ
    let S := SchurOperator.linear ρ T hs
    let R := S.baseChange F
    have hS2 : S*S=1 := SchurOperator.linear_square ρ T hs h2
    have hR2 : R*R=1 := by
      rw [←LinearMap.baseChange_mul,hS2,LinearMap.baseChange_one]
    have hS (g : G × G) : S * ρ.endFieldRep g = ρ.endFieldRep (g.2,g.1) * S := by
      ext v
      exact SchurOperator.linear_intertwines ρ T hs MulEquiv.prodComm hT g v
    have hR (g : G × G) (v) : R (absoluteRep ρ g v) =
        absoluteRep ρ (g.2,g.1) (R v) := by
      have h := congrArg (fun f : Module.End E ρ.asModule => f.baseChange F) (hS g)
      rw [LinearMap.baseChange_mul,LinearMap.baseChange_mul] at h
      exact LinearMap.congr_fun h v
    have hb := exchange_displacement_ge_of_factor_degree (absoluteRep ρ)
      (absoluteRep_injective ρ hf) k hd R hR2 hR
    change k.choose 2 ≤ finrank F (S.baseChange F - 1).range at hb
    rw [SL2.SchurTensorDisplacement.displacement_rank_baseChange] at hb
    change k.choose 2 ≤ finrank (ZMod 2) (T-LinearMap.id).range
    rw [SchurOperator.displacement_eq_schur_mul ρ T hs]
    exact hb.trans (Nat.le_mul_of_pos_left _ (schurField_finrank_pos ρ))
  · have hb := SchurNormalizer.finrank_le_twice_fixedCodim ρ a hs
    rw [fixedCodim_zpowers_eq_displacement_rank] at hb
    change finrank (ZMod 2) V ≤ 2 * finrank (ZMod 2) (T-1).range at hb
    have hlo := binary_square_finrank_ge_of_factor_degree ρ hf k hd
    have hc : ∀ n : ℕ, 2 * n.choose 2 + n = n*n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [Nat.choose_succ_succ,Nat.choose_one_right]; nlinarith
    have hh := hc k
    omega
end Representation.ExchangedProduct
