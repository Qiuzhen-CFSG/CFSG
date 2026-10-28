module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Parameters
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.Rational
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.RootOperators
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.WeightAction
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.BasicFactors
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.TensorStep

/-!
# The algebraic exceptional tensor-product theorem

Prepending a basic factor `B` to the exceptional pullback of an irreducible
factor `C` gives a rational irreducible representation. Polynomial root
expansions and basic short-root density discharge the hypotheses of the
one-step irreducibility theorem. The tensor of the two nonzero highest vectors
has coroot weight `basicCoefficient b + exceptionalWeight a`.

Starting with the one-dimensional trivial representation, induction constructs
the entire tensor and its highest weight. Tensor associativity and pullback
equivalences identify this construction with the exact existing `pointTensor`,
including its initial unit factor and cyclic indexing. No composition factor
is substituted for the tensor. The previous rationality and root-action APIs
remain re-exported.

`exists_pointTensor_factor` supplies the algebraic tensor contract for the
Steinberg assembly. Its explicit remaining premises are universality of the
literal F₄ carrier, raw highest-weight uniqueness, and a surjective algebraic
endomorphism with the exceptional root formula. Existence of these inputs and
finite restriction are separate results.

Sources: GLS3, Theorem 2.8.5, Remark 2.8.4 and Corollary 2.8.6(b);
Steinberg, *Representations of Algebraic Groups*, Nagoya Math. J. 22 (1963),
Theorem 5.1 and §11, DOI 10.1017/S0027763000011016; *Endomorphisms of Linear
Algebraic Groups*, §§13.1–13.2.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open scoped TensorProduct
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]

private noncomputable def congrTensor {G : Type*} [Group G]
    {V W X Y : Type*}
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]
    {ρ : Representation F G V} {σ : Representation F G W}
    {τ : Representation F G X} {π : Representation F G Y}
    (e : Representation.Equiv ρ σ) (f : Representation.Equiv τ π) :
    Representation.Equiv (ρ.tprod τ) (σ.tprod π) :=
  .mk (TensorProduct.congr e.toLinearEquiv f.toLinearEquiv)
    (e.toIntertwiningMap.tensor f.toIntertwiningMap).2

private noncomputable def prefixHead {G : Type*} [Group G]
    (V : ℕ → FDRep F G) (n : ℕ) :
    Representation.Equiv (tensorPrefix V (n + 1)).ρ
      (Representation.tprod (V 0).ρ (tensorPrefix (fun i => V (i + 1)) n).ρ) := by
  induction n with
  | zero =>
    exact (Representation.TensorProduct.lid F (V 0).ρ).trans
      (Representation.TensorProduct.rid F (V 0).ρ).symm
  | succ n ih =>
    exact (congrTensor ih (Representation.Equiv.refl (V (n + 1)).ρ)).trans
      (Representation.TensorProduct.assoc _ _ _)

private noncomputable def prefixCongr {G : Type*} [Group G]
    (V W : ℕ → FDRep F G) (n : ℕ)
    (h : ∀ i, i < n → Nonempty (Representation.Equiv (V i).ρ (W i).ρ)) :
    Representation.Equiv (tensorPrefix V n).ρ (tensorPrefix W n).ρ := by
  induction n with
  | zero => exact Representation.Equiv.refl _
  | succ n ih =>
    exact congrTensor (ih (fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self n)))) (h n (Nat.lt_succ_self n)).some

private theorem exists_unit_factor :
    ∃ A : AlgebraicFactor F, HasHighestWeight A 0 ∧
      Nonempty (Representation.Equiv (A.restrict (MonoidHom.id _)).ρ
        (Representation.trivial F (PointGroup F) F)) := by
  let ρ : RationalRepresentation (F4Chevalley.Carrier (k := F)) F := ⟨1⟩
  have hr : IsRationalRepresentation ρ := by
    let e := Module.finBasis F F
    let c : Fin (Module.finrank F F) → Fin (Module.finrank F F) →
        (F4Chevalley.Carrier (k := F)).PolynomialFunction := fun i j =>
      algebraMap F _ (e.repr (e j) i)
    let f := generalLinearRepresentationMorphismOfInverseMatrixCoefficient e ρ.action c c
      (by intro i j g; rw [polynomialFunction_algebraMap_apply]; rfl)
      (by intro i j g; rw [polynomialFunction_algebraMap_apply]; rfl)
    exact ⟨e, f, fun g => glPointEquivOf_generalLinearRepresentationPoint e _⟩
  let A : AlgebraicFactor F :=
    { Space := F
      action := ρ
      irreducible := ⟨hr, fun W _ => eq_bot_or_eq_top W⟩ }
  refine ⟨A, ⟨1, one_ne_zero, ?_, ?_⟩, ⟨Representation.Equiv.refl _⟩⟩
  · intro r hr t
    rfl
  · intro i t
    change (1 : F) = ((t : F) ^ (0 : Weight) i) • (1 : F)
    simp

omit [IsAlgClosed F] in
private theorem tmul_nonzero {V W : Type u}
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    {v : V} {w : W} (hv : v ≠ 0) (hw : w ≠ 0) : v ⊗ₜ[F] w ≠ 0 := by
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one F hv
  intro h
  have he := congrArg (fun z => TensorProduct.lid F W (TensorProduct.map f LinearMap.id z)) h
  exact hw (by simpa [hf] using he)

set_option backward.isDefEq.respectTransparency false in
private theorem exists_prepend_factor [CharP F 2]
    (hU : IsUniversalVersion (F4Chevalley.Carrier (k := F)))
    (hhigh : ∀ (B C : AlgebraicFactor F) (a : Weight),
      HasHighestWeight B a → HasHighestWeight C a →
        AreEquivalentRepresentations B.action C.action)
    (Ψ : Theory.AlgebraicGroup.Morphism (F4Chevalley.Carrier (k := F))
      (F4Chevalley.Carrier (k := F)))
    (hsurj : Function.Surjective Ψ.onPoints) (hroot : HasExceptionalRootFormula Ψ.onPoints)
    (B C : AlgebraicFactor F) (b : BasicWeight) (a : Weight)
    (hB : HasBasicHighestWeight B b) (hC : HasHighestWeight C a) :
    ∃ A : AlgebraicFactor F, HasHighestWeight A (prependWeight b a) ∧
      Nonempty (Representation.Equiv (A.restrict (MonoidHom.id _)).ρ
        (Representation.tprod (B.restrict (MonoidHom.id _)).ρ (C.restrict Ψ.onPoints).ρ)) := by
  obtain ⟨σ, hσ, hrσ⟩ := rationalRepresentation_pullback_exists Ψ C.action C.irreducible.1
  obtain ⟨τ, hτ, hrτ⟩ := rationalRepresentation_tensorProduct_exists
    B.action σ B.irreducible.1 hrσ
  let ρ := Representation.tprod (B.restrict (MonoidHom.id _)).ρ (C.restrict Ψ.onPoints).ρ
  have heq (g : PointGroup F) : (τ.action g).val = ρ g := by
    apply TensorProduct.ext
    ext v w
    change (τ.action g).val (v ⊗ₜ[F] w) =
      (B.action.action g).val v ⊗ₜ[F] (C.action.action (Ψ.onPoints g)).val w
    rw [hτ, hσ]
  obtain ⟨p⟩ := rootExpansion_nonempty B.action B.irreducible.1
  have hp := p.hasShortRootDensity_of_basic_highestWeight hU hhigh hB
  have hirr : Representation.IsIrreducible ρ :=
    tensorStep_irreducible B C Ψ Ψ.onPoints rfl hsurj hroot p hp
  have hτirr : IsIrreducibleRepresentation τ := by
    refine ⟨hrτ, ?_⟩
    intro W hW
    let U : Subrepresentation ρ :=
      { toSubmodule := W
        apply_mem_toSubmodule := fun g w hw => by rw [← heq]; exact hW g w hw }
    exact (eq_bot_or_eq_top U).imp (congrArg Subrepresentation.toSubmodule)
      (congrArg Subrepresentation.toSubmodule)
  let A : AlgebraicFactor F :=
    { Space := B.Space ⊗[F] C.Space
      action := τ
      irreducible := hτirr }
  refine ⟨A, ?_, ⟨Representation.Equiv.mk (LinearEquiv.refl F _) ?_⟩⟩
  · obtain ⟨v, hv, hvpos, hvtor⟩ := hB
    obtain ⟨w, hw, hwpos, hwtor⟩ := hC
    refine ⟨v ⊗ₜ[F] w, tmul_nonzero hv hw, ?_, ?_⟩
    · intro r hr t
      change (τ.action _).val _ = _
      rw [hτ, hσ, hvpos r hr]
      exact congrArg (fun z => v ⊗ₜ[F] z) (exceptional_positive_fixed Ψ.onPoints hroot
        (C.restrict (MonoidHom.id _)).ρ w hwpos r hr t)
    · intro i t
      change (τ.action _).val _ = _
      rw [hτ, hσ, hvtor]
      have ht := exceptional_coroot_eigenvector Ψ.onPoints hroot
        (C.restrict (MonoidHom.id _)).ρ a w hwtor i t
      change (C.action.action (Ψ.onPoints (algebraicCorootElement
        (typeF4SimpleRootIndex i) t))).val w = _ at ht
      rw [ht]
      rw [prependWeight_eq]
      simp only [Pi.add_apply, pow_add, TensorProduct.smul_tmul,
        TensorProduct.tmul_smul, smul_smul, mul_comm]
  · intro g
    exact heq g

private theorem exists_prefix_factor [CharP F 2]
    (hU : IsUniversalVersion (F4Chevalley.Carrier (k := F)))
    (hhigh : ∀ (B C : AlgebraicFactor F) (a : Weight),
      HasHighestWeight B a → HasHighestWeight C a →
        AreEquivalentRepresentations B.action C.action)
    (Ψ : Theory.AlgebraicGroup.Morphism (F4Chevalley.Carrier (k := F))
      (F4Chevalley.Carrier (k := F)))
    (ψ : Monoid.End (PointGroup F)) (hΨ : Ψ.onPoints = ψ)
    (hsurj : Function.Surjective ψ) (hroot : HasExceptionalRootFormula ψ)
    (n : ℕ) (B : ℕ → AlgebraicFactor F) (b : ℕ → BasicWeight)
    (hB : ∀ i, i < n → HasBasicHighestWeight (B i) (b i)) :
    ∃ A : AlgebraicFactor F, HasHighestWeight A (parameterWeight n (fun i => b i.val)) ∧
      Nonempty (Representation.Equiv (A.restrict (MonoidHom.id _)).ρ
        (tensorPrefix (fun i => (B i).restrict (ψ ^ i)) n).ρ) := by
  induction n generalizing B b with
  | zero => exact exists_unit_factor
  | succ n ih =>
    obtain ⟨C, hC, ⟨eC⟩⟩ := ih (fun i => B (i + 1)) (fun i => b (i + 1))
      (fun i hi => hB (i + 1) (Nat.succ_lt_succ hi))
    obtain ⟨A, hA, ⟨eA⟩⟩ := exists_prepend_factor hU hhigh Ψ (by rwa [hΨ]) (by rwa [hΨ])
      (B 0) C (b 0) _ (hB 0 (Nat.zero_lt_succ n)) hC
    rw [hΨ] at eA
    refine ⟨A, hA, ?_⟩
    let V : ℕ → FDRep F (PointGroup F) := fun i => (B i).restrict (ψ ^ i)
    let T : ℕ → FDRep F (PointGroup F) := fun i => (B (i + 1)).restrict (ψ ^ i)
    let P : ℕ → FDRep F (PointGroup F) := fun i => FDRep.of ((T i).ρ.comp ψ)
    have hP (i : ℕ) : Nonempty (Representation.Equiv (P i).ρ (V (i + 1)).ρ) := by
      change Nonempty (Representation.Equiv
        (((B (i + 1)).restrict (ψ ^ i)).ρ.comp ψ)
        ((B (i + 1)).restrict (ψ ^ (i + 1))).ρ)
      rw [pow_succ]
      exact ⟨Representation.Equiv.refl _⟩
    let eTail : Representation.Equiv (C.restrict ψ).ρ
        (tensorPrefix (fun i => V (i + 1)) n).ρ :=
      ((pullbackEquiv eC ψ).trans (tensorPrefix_pullbackEquiv T ψ n)).trans
        (prefixCongr P (fun i => V (i + 1)) n (fun i _ => hP i))
    exact ⟨(eA.trans (congrTensor (Representation.Equiv.refl (V 0).ρ) eTail)).trans
      (prefixHead V n).symm⟩

/-- The algebraic exceptional tensor-product contract: the entire concrete
`pointTensor` is equivalent to a rational irreducible factor with the specified
highest weight. Short-root density and the one-step irreducibility premises
are discharged. Universality and raw highest-weight uniqueness remain the
explicit geometric and highest-weight inputs; reverse weight distinction is
not needed. The argument works for every `k`, hence in particular for `k ≥ 1`. -/
theorem exists_pointTensor_factor [CharP F 2]
    (hU : IsUniversalVersion (F4Chevalley.Carrier (k := F)))
    (hhigh : ∀ (B C : AlgebraicFactor F) (a : Weight),
      HasHighestWeight B a → HasHighestWeight C a →
        AreEquivalentRepresentations B.action C.action)
    (Ψ : Theory.AlgebraicGroup.Morphism (F4Chevalley.Carrier (k := F))
      (F4Chevalley.Carrier (k := F)))
    (hsurj : Function.Surjective Ψ.onPoints) (hroot : HasExceptionalRootFormula Ψ.onPoints)
    {k : ℕ} (B : ZMod (2 * k + 1) → AlgebraicFactor F)
    (b : ZMod (2 * k + 1) → BasicWeight)
    (hB : ∀ i, HasBasicHighestWeight (B i) (b i)) :
    ∃ A : AlgebraicFactor F, HasHighestWeight A (tensorWeight b) ∧
      Nonempty (Representation.Equiv (A.restrict (MonoidHom.id _)).ρ
        (pointTensor Ψ.onPoints B).ρ) := by
  obtain ⟨A, hA, ⟨eA⟩⟩ := exists_prefix_factor hU hhigh Ψ Ψ.onPoints rfl hsurj hroot
    (2 * k + 1) (fun i => B (i : ZMod (2 * k + 1)))
    (fun i => b (i : ZMod (2 * k + 1))) (fun i _ => hB _)
  refine ⟨A, hA, ⟨eA.trans (prefixCongr _ _ (2 * k + 1) ?_)⟩⟩
  intro i hi
  have hv : (i : ZMod (2 * k + 1)).val = i := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hi]
  rw [hv]
  exact ⟨Representation.Equiv.refl _⟩

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor
