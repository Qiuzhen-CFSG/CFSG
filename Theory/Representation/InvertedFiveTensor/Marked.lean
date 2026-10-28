module

public import Theory.Representation.InvertedFiveTensor
public import Mathlib.Algebra.Module.TransferInstance

/-!
# Marked binary sections in the inverted-five tensor

An injective binary map into the inverter-fixed space is onto that space
when the ambient binary dimension is twice its domain dimension. Transport
of the constructed F₄ scalars along this specific map makes the original
domain the tensor factor, preserving its original commuting group action.
The explicit pure-tensor formula retains the given inclusion.

Source: Aschbacher–Smith 8.2.8(5), printed pp.718–719. The Chapter 8 consumer
uses the actual B/U → P/U quotient inclusion and supplies fixedness from an
inverter lift in the original elementary abelian V.
-/

public section
open scoped TensorProduct
namespace InvertedFiveTensor
variable {V B : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup B] [Module (ZMod 2) B] [Finite V] [Finite B]
  (σ : Representation (ZMod 2) D V) (hf : ∀ v, σ rot v = v → v = 0)
  (ι : B →ₗ[ZMod 2] V) (hi : Function.Injective ι)
  (hfix : ∀ b, σ invt (ι b) = ι b)
  (hd : Module.finrank (ZMod 2) V = 2 * Module.finrank (ZMod 2) B)

@[expose] noncomputable def markedFixedEquiv : letI := fieldModule σ hf
    letI := fieldTower σ hf
    B ≃ₗ[ZMod 2] fixedSpace (fieldRepresentation σ hf) := by
  letI := fieldModule σ hf
  letI := fieldTower σ hf
  let ρ := fieldRepresentation σ hf
  let j : B →ₗ[ZMod 2] fixedSpace ρ :=
    { toFun := fun b => ⟨ι b, hfix b⟩
      map_add' := fun x y => Subtype.ext (ι.map_add x y)
      map_smul' := fun a b => Subtype.ext (ι.map_smul a b) }
  have hj : Function.Injective j := fun x y h => hi (congrArg Subtype.val h)
  have he := ((pairEquiv ρ (omega_smul σ hf)).restrictScalars (ZMod 2)).finrank_eq
  rw [Module.finrank_prod, hd] at he
  have he' : Module.finrank (ZMod 2) B = Module.finrank (ZMod 2) (fixedSpace ρ) := by omega
  exact LinearEquiv.ofBijective j ⟨hj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank he').mp hj⟩

theorem markedFixedEquiv_coe (b : B) :
    (markedFixedEquiv σ hf ι hi hfix hd b : V) = ι b := rfl


include hi hfix hd in
/-- Recover field scalars and equivariant tensor coordinates on the specified domain. -/
theorem marked_tensor {K : Type*} [Group K]
    (κ : Representation (ZMod 2) K V) (τ : Representation (ZMod 2) K B)
    (hc : ∀ k g v, κ k (σ g v) = σ g (κ k v))
    (he : ∀ k b, ι (τ k b) = κ k (ι b)) :
    let := fieldModule σ hf
    ∃ mB : Module F B, letI := mB
      IsScalarTower (ZMod 2) F B ∧
      ∃ τF : Representation F K B, (∀ k b, τF k b = τ k b) ∧
      ∃ e : (Fin 2 → F) ⊗[F] B ≃ₗ[F] V,
        (∀ n b, e (n ⊗ₜ[F] b) = n 0 • ι b + n 1 • σ rot (ι b)) ∧
        ∀ k g z, e (TensorProduct.map (natural g) (τF k) z) = κ k (σ g (e z)) := by
  let := fieldModule σ hf
  let := fieldTower σ hf
  let ρ := fieldRepresentation σ hf
  have hq : ∀ v, omega • v = ρ rot v + (ρ rot ^ 4) v := omega_smul σ hf
  let eB := markedFixedEquiv σ hf ι hi hfix hd
  let mB := eB.toAddEquiv.module F
  let := eB.isScalarTower F
  let φ : B ≃ₗ[F] fixedSpace ρ := eB.toAddEquiv.linearEquiv F
  have hφ (b : B) : (φ b : V) = ι b := markedFixedEquiv_coe σ hf ι hi hfix hd b
  have hι (a : F) (b : B) : ι (a • b) = a • ι b := by
    rw [← hφ, φ.map_smul, ← hφ]
    rfl
  have hcr (k : K) : Commute (κ k) (σ rot) := LinearMap.ext (hc k rot)
  let κF := commutingFieldRepresentation σ hf κ hcr
  have hκ (k : K) (a : F) (v : V) : κ k (a • v) = a • κ k v :=
    (κF k).map_smul a v
  let τF : Representation F K B :=
    { toFun := fun k => { (τ k).toAddHom with
        map_smul' := fun a b => by
          apply hi
          change ι (τ k (a • b)) = ι (a • τ k b)
          rw [he, hι, hκ, hι, he] }
      map_one' := by ext b; exact LinearMap.congr_fun τ.map_one b
      map_mul' := by intro k l; ext b; exact LinearMap.congr_fun (τ.map_mul k l) b }
  let e : (Fin 2 → F) ⊗[F] B ≃ₗ[F] V :=
    (TensorProduct.congr (LinearEquiv.refl F _) φ).trans
      (tensorEquiv ρ hq)
  have ht (n : Fin 2 → F) (b : B) :
      e (n ⊗ₜ[F] b) = n 0 • ι b + n 1 • σ rot (ι b) := by
    change tensorEquiv ρ hq (n ⊗ₜ[F] φ b) = _
    rw [tensorEquiv_tmul, hφ]
    rfl
  refine ⟨mB, inferInstance, τF, fun _ _ => rfl, e, ht, ?_⟩
  intro k g z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul n b =>
    have hdih (b : B) : e (natural g n ⊗ₜ[F] b) = σ g (e (n ⊗ₜ[F] b)) := by
      change tensorEquiv ρ hq (natural g n ⊗ₜ[F] φ b) =
        ρ g (tensorEquiv ρ hq (n ⊗ₜ[F] φ b))
      exact tensorEquiv_dihedral ρ hq g n (φ b)
    have hk : e (n ⊗ₜ[F] τF k b) = κ k (e (n ⊗ₜ[F] b)) := by
      rw [ht, ht, map_add, hκ, hκ]
      change n 0 • ι (τ k b) + n 1 • σ rot (ι (τ k b)) = _
      rw [he, hc]
    rw [TensorProduct.map_tmul, hdih, hk, hc]

end InvertedFiveTensor
