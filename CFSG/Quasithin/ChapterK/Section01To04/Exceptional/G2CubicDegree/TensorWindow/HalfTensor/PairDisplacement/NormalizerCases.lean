module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.TensorWindow.HalfTensor.Model
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.TensorWindow.HalfTensor.PairDisplacement.Intertwiners
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.InnerFieldCoverage
public import Theory.Representation.IrreducibleSimpleFaithful

/-!
# Inner and Frobenius-exchange cases for the concrete G₂ pair

An involution intertwining the irreducible natural pair induces a square-one
abstract automorphism. Indeed the pair is faithful: G₂(F) is simple for
`|F| = 2^(2*s)`, `s > 0`, and an irreducible representation of dimension 36
cannot have full kernel. The faithful inner-field action then makes the field
component square to one. Finite-field Frobenius has order `2*s`, so this
component is either the identity or the actual half-degree Frobenius.

In the inner case the representative itself squares to one. In the other case,
Frobenius periodicity exchanges the literal natural actions at `i` and `i+s`.
The inner representative acts on each factor, giving an explicit exchange
intertwiner. Its square equation is retained; no trivialization of that inner
twist or assumption about preservation of tensor factors is needed. The last
theorem supplies precisely the structural alternative used by the separate
pair-displacement assembly.

This argument uses the permitted irreducibility hypothesis and does not require
recognition of arbitrary modules or comparison with a tensor word. The position
bound `i < s`, nontriviality of the involution, and algebraic closure of the
coefficient field are unnecessary for this structural conclusion.

Source: Guralnick–Malle, Classification of 2F-modules II, §3.5 and Lemma 8.5,
manuscript pp.20,55–56; see `G2CubicDegree/Source.md`. The finite-field calculation
uses Mathlib's Frobenius generator theorem; the actual G₂ inner-field coverage
is provided by the licensed ATLAS port imported above.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.TensorWindow.HalfTensor
open Atlas.G2 Atlas.G2.LieAutomorphismExtensions
variable (F K : Type*) [Field F] [Finite F] [CharP F 2]
  [Field K] [Algebra F K]

private theorem field_square_cases {s : ℕ} (hs : 0 < s)
    (hF : Nat.card F = 2 ^ (2 * s)) (σ : F ≃+* F) (hσ : σ * σ = 1) :
    σ = 1 ∨ σ = iterateFrobeniusEquiv F 2 s := by
  let := ZMod.algebra F 2
  have hdim : Module.finrank (ZMod 2) F = 2 * s := by
    let := Fintype.ofFinite F
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    have hc := Module.card_eq_pow_finrank (K := ZMod 2) (V := F)
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod, hF] using hc.symm
  let σ' : F ≃ₐ[ZMod 2] F := AlgEquiv.ofRingEquiv (f := σ) (fun t =>
    DFunLike.congr_fun (Subsingleton.elim
      (σ.toRingHom.comp (algebraMap (ZMod 2) F))
      (algebraMap (ZMod 2) F)) t)
  have hσ' : σ' ^ 2 = 1 := by
    apply AlgEquiv.ext
    intro x
    exact DFunLike.congr_fun hσ x
  obtain ⟨k, hk⟩ :=
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod 2) F).surjective σ'
  change FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) F ^ k.val = σ' at hk
  have hklt : k.val < 2 * s := hdim ▸ k.isLt
  have hd0 : orderOf (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) F) ∣
      2 * k.val := by
    rw [orderOf_dvd_iff_pow_eq_one, Nat.mul_comm 2, pow_mul, hk]
    exact hσ'
  have hd : (2 * s) ∣ 2 * k.val := by
    simpa only [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic, hdim] using hd0
  have hd' : s ∣ k.val := Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 2) hd
  have hkcases : k.val = 0 ∨ k.val = s := by
    obtain ⟨m, hm⟩ := hd'
    have hm2 : m < 2 := by
      apply (Nat.mul_lt_mul_left hs).mp
      simpa only [← hm, Nat.mul_comm s 2] using hklt
    have hm01 : m = 0 ∨ m = 1 := by omega
    rcases hm01 with rfl | rfl
    · exact Or.inl (by simpa using hm)
    · exact Or.inr (by simpa using hm)
  let forget : (F ≃ₐ[ZMod 2] F) →* (F ≃+* F) := {
    toFun := AlgEquiv.toRingEquiv
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hf : forget (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) F) =
      frobeniusEquiv F 2 := by
    apply RingEquiv.ext
    intro t
    change t ^ Fintype.card (ZMod 2) = t ^ 2
    rw [ZMod.card]
  have hforget : forget σ' = σ := rfl
  have he : frobeniusEquiv F 2 ^ k.val = σ := by
    simpa only [map_pow, hf, hforget] using congrArg forget hk
  rcases hkcases with hk0 | hks
  · exact Or.inl (by simpa only [hk0, pow_zero] using he.symm)
  · exact Or.inr (by simpa only [hks, iterateFrobeniusEquiv_eq_pow] using he.symm)

omit [Field F] [Finite F] [CharP F 2] in
private theorem field_card_gt_two {s : ℕ} (hs : 0 < s)
    (hF : Nat.card F = 2 ^ (2 * s)) : 2 < Nat.card F := by
  rw [hF]
  calc 2 = 2 ^ 1 := by decide
       _ < 2 ^ (2 * s) := Nat.pow_lt_pow_right (by decide) (by omega)

variable (i s : ℕ)
  [Representation.IsIrreducible (k := K) (G := Model F)
    (V := PairSpace F K) (pairRep F K i s)]

/-- The irreducible 36-dimensional pair is faithful over a defining field of even degree. -/
theorem pairRep_injective (hs : 0 < s) (hF : Nat.card F = 2 ^ (2 * s)) :
    Function.Injective (pairRep F K i s) := by
  let := Atlas.G2.isSimple (field_card_gt_two F hs hF)
  exact Representation.injective_of_simple_of_irreducible_of_one_lt_finrank
    (F := K) (G := Model F) (V := PairSpace F K) (pairRep F K i s) (by rw [finrank_pairSpace]; omega)

/-- Faithfulness transports the linear involution equation to the induced group automorphism. -/
theorem pair_normalizer_square (hs : 0 < s) (hF : Nat.card F = 2 ^ (2 * s))
    (T : Module.End K (PairSpace F K)) (α : MulAut (Model F))
    (hT2 : T * T = 1)
    (hT : ∀ h, T * pairRep F K i s h = pairRep F K i s (α h) * T) :
    α * α = 1 := by
  apply MulEquiv.ext
  intro h
  apply pairRep_injective F K i s hs hF
  change pairRep F K i s (α (α h)) = pairRep F K i s h
  calc
    pairRep F K i s (α (α h)) = pairRep F K i s (α (α h)) * (T * T) := by
      rw [hT2, mul_one]
    _ = (pairRep F K i s (α (α h)) * T) * T := (mul_assoc _ _ _).symm
    _ = (T * pairRep F K i s (α h)) * T := by rw [hT (α h)]
    _ = T * (pairRep F K i s (α h) * T) := mul_assoc _ _ _
    _ = T * (T * pairRep F K i s h) := by rw [hT h]
    _ = pairRep F K i s h := by rw [← mul_assoc, hT2, one_mul]

omit [Representation.IsIrreducible (k := K) (G := Model F)
    (V := PairSpace F K) (pairRep F K i s)] in
private theorem frobenius_add (a b : ℕ) :
    Restricted.frobeniusAutomorphism F (a + b) =
      Restricted.frobeniusAutomorphism F a * Restricted.frobeniusAutomorphism F b := by
  change fieldAction (iterateFrobeniusEquiv F 2 (a + b)) =
    fieldAction (iterateFrobeniusEquiv F 2 a) * fieldAction (iterateFrobeniusEquiv F 2 b)
  simp only [iterateFrobeniusEquiv_eq_pow, pow_add, map_mul]

omit [Representation.IsIrreducible (k := K) (G := Model F)
    (V := PairSpace F K) (pairRep F K i s)] in
private theorem naturalTwist_half (hF : Nat.card F = 2 ^ (2 * s)) (h : Model F) :
    naturalTwist F K i (Restricted.frobeniusAutomorphism F s h) =
        naturalTwist F K (i + s) h ∧
      naturalTwist F K (i + s) (Restricted.frobeniusAutomorphism F s h) =
        naturalTwist F K i h := by
  have h1 (j : ℕ) : naturalTwist F K j (Restricted.frobeniusAutomorphism F s h) =
      naturalTwist F K (j + s) h := by
    unfold naturalTwist
    rw [frobenius_add]
    rfl
  constructor
  · exact h1 i
  · rw [h1, show i + s + s = i + (2 * s) by omega]
    unfold naturalTwist
    rw [TensorClassification.frobeniusAutomorphism_period F hF]

omit [Representation.IsIrreducible (k := K) (G := Model F)
    (V := PairSpace F K) (pairRep F K i s)] in
/-- The actual invertible natural action of a model element at one Frobenius position. -/
@[expose] def naturalTwistActionEquiv (j : ℕ) (x : Model F) :
    NaturalScalarSpace F K ≃ₗ[K] NaturalScalarSpace F K :=
  { toLinearMap := naturalTwist F K j x
    invFun := naturalTwist F K j x⁻¹
    left_inv := fun v => by
      change (naturalTwist F K j x⁻¹ * naturalTwist F K j x) v = v
      rw [← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    right_inv := fun v => by
      change (naturalTwist F K j x * naturalTwist F K j x⁻¹) v = v
      rw [← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] }

omit [Representation.IsIrreducible (k := K) (G := Model F)
    (V := PairSpace F K) (pairRep F K i s)] in
/-- Half-degree Frobenius exchanges the literal factors; the inner multiplier
acts on them by its two actual natural actions. -/
theorem pair_frobenius_exchange (hF : Nat.card F = 2 ^ (2 * s)) (x : Model F) :
    ∀ h, (pairExchange F K (naturalTwistActionEquiv F K i x)
        (naturalTwistActionEquiv F K (i + s) x)).toLinearMap * pairRep F K i s h =
      pairRep F K i s ((MulAut.conj x * Restricted.frobeniusAutomorphism F s) h) *
        (pairExchange F K (naturalTwistActionEquiv F K i x)
          (naturalTwistActionEquiv F K (i + s) x)).toLinearMap := by
  intro h
  apply TensorProduct.ext'
  intro u v
  change naturalTwist F K i x (naturalTwist F K (i + s) h v) ⊗ₜ[K]
      naturalTwist F K (i + s) x (naturalTwist F K i h u) =
    naturalTwist F K i (x * Restricted.frobeniusAutomorphism F s h * x⁻¹)
        (naturalTwist F K i x v) ⊗ₜ[K]
      naturalTwist F K (i + s) (x * Restricted.frobeniusAutomorphism F s h * x⁻¹)
        (naturalTwist F K (i + s) x u)
  have he (j : ℕ) (w : NaturalScalarSpace F K) :
      naturalTwist F K j (x * Restricted.frobeniusAutomorphism F s h * x⁻¹)
          (naturalTwist F K j x w) =
        naturalTwist F K j x (naturalTwist F K j (Restricted.frobeniusAutomorphism F s h) w) := by
    change (naturalTwist F K j (x * Restricted.frobeniusAutomorphism F s h * x⁻¹) *
      naturalTwist F K j x) w =
      (naturalTwist F K j x * naturalTwist F K j (Restricted.frobeniusAutomorphism F s h)) w
    rw [← map_mul, ← map_mul]
    congr 2
    simp [mul_assoc]
  rw [he, he, (naturalTwist_half F K i s hF h).1, (naturalTwist_half F K i s hF h).2]


/-- A normalizing involution has either a square-one inner representative or
an inner twist of the literal half-degree Frobenius. In the latter case the
inner factor satisfies its exact square equation, and its two natural actions
supply an exchange intertwiner. -/
theorem pair_normalizer_inner_or_half_frobenius
    (hs : 0 < s) (hF : Nat.card F = 2 ^ (2 * s))
    (T : Module.End K (PairSpace F K)) (α : MulAut (Model F))
    (hT2 : T * T = 1)
    (hT : ∀ h, T * pairRep F K i s h = pairRep F K i s (α h) * T) :
    (∃ x : Model F, x * x = 1 ∧ α = MulAut.conj x) ∨
      ∃ x : Model F,
        α = MulAut.conj x * Restricted.frobeniusAutomorphism F s ∧
        x * Restricted.frobeniusAutomorphism F s x = 1 ∧
        ∀ h, (pairExchange F K (naturalTwistActionEquiv F K i x)
            (naturalTwistActionEquiv F K (i + s) x)).toLinearMap * pairRep F K i s h =
          pairRep F K i s (α h) *
            (pairExchange F K (naturalTwistActionEquiv F K i x)
              (naturalTwistActionEquiv F K (i + s) x)).toLinearMap := by
  have hq := field_card_gt_two F hs hF
  have hα2 := pair_normalizer_square F K i s hs hF T α hT2 hT
  obtain ⟨x, σ, hα⟩ := exists_inner_field hq α
  let z : Model F ⋊[fieldAction] (F ≃+* F) := ⟨x, σ⟩
  have hz2 : z * z = 1 := by
    apply semilinearAction_injective hq
    rw [map_mul, map_one]
    change (MulAut.conj x * fieldAction σ) * (MulAut.conj x * fieldAction σ) = 1
    rw [← hα]
    exact hα2
  have hσ2 : σ * σ = 1 := congrArg SemidirectProduct.right hz2
  have hx2 : x * fieldAction σ x = 1 := congrArg SemidirectProduct.left hz2
  rcases field_square_cases F hs hF σ hσ2 with hσ | hσ
  · left
    refine ⟨x, ?_, ?_⟩
    · simpa only [hσ, map_one, MulAut.one_apply] using hx2
    · simpa only [hσ, map_one, mul_one] using hα
  · right
    have he : α = MulAut.conj x * Restricted.frobeniusAutomorphism F s := by
      change α = MulAut.conj x * fieldAction (iterateFrobeniusEquiv F 2 s)
      rw [← hσ]
      exact hα
    refine ⟨x, he, ?_, ?_⟩
    · change x * fieldAction (iterateFrobeniusEquiv F 2 s) x = 1
      rw [← hσ]
      exact hx2
    · rw [he]
      exact pair_frobenius_exchange F K i s hF x

/-- The actual inner-or-exchange alternative consumed by
`pair_displacement_of_inner_bound_and_cases`. Faithfulness, the automorphism
square, and the inner representative's square are derived in the proof. -/
theorem pair_normalizer_cases
    (hs : 0 < s) (hF : Nat.card F = 2 ^ (2 * s))
    (T : Module.End K (PairSpace F K)) (α : MulAut (Model F))
    (hT2 : T * T = 1)
    (hT : ∀ h, T * pairRep F K i s h = pairRep F K i s (α h) * T) :
    (∃ x : Model F, x * x = 1 ∧ α = MulAut.conj x) ∨
      ∃ f g : NaturalScalarSpace F K ≃ₗ[K] NaturalScalarSpace F K,
        ∀ h, (pairExchange F K f g).toLinearMap * pairRep F K i s h =
          pairRep F K i s (α h) * (pairExchange F K f g).toLinearMap := by
  rcases pair_normalizer_inner_or_half_frobenius F K i s hs hF T α hT2 hT with
    hi | ⟨x, _, _, hx⟩
  · exact Or.inl hi
  · exact Or.inr ⟨naturalTwistActionEquiv F K i x, naturalTwistActionEquiv F K (i + s) x, hx⟩

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.TensorWindow.HalfTensor
