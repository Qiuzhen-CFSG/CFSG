module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.TensorWindow.DegreeGap
public import Theory.Representation.BinaryOffender.SchurNormalizerDisplacement
public import Theory.Representation.Triality.OuterDisplacement.TensorCoordinates

/-!
# Schur-linear actors in the G₂ half-field case

Schur linearity constructs an endomorphism on the existing Schur carrier.
Restriction of scalars multiplies displacement by the Schur degree; scalar
extension preserves it. Nonidentity and the involution equation are retained,
as is the actual group automorphism induced by the original normalizer.
An intertwining equivalence can therefore transport an operator estimate
without replacing the actor or its group action.

For binary degree `18*r`, the Frobenius parameter theorem proves that the
Schur degree is `r/2` and the extended dimension is 36. Displacement at least
15 over the splitting field then implies the desired binary `5/12` bound.
The explicit split-rank premise remains to be discharged on the natural pair.

Source: Guralnick–Malle, Classification of 2F-modules II, §3.5 and Lemma 8.5,
manuscript pp.20,55–56; see `G2CubicDegree/Source.md`.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped MonoidAlgebra TensorProduct
open Representation Representation.BinaryOffender
open Representation.BinaryOffender.SchurNormalizer
open Representation.BinaryOffender.NaturalTensor

namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.TensorWindow.HalfTensor
variable {G V : Type*} [Group G] [AddCommGroup V]
  [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

@[expose] def schurOperator (t : linearNormalizer ρ) (hs : IsSchurLinear ρ t) :
    Module.End (Module.End (ZMod 2)[G] ρ.asModule) ρ.asModule where
  toFun v := ρ.asModuleEquiv.symm (t.val.val (ρ.asModuleEquiv v))
  map_add' x y := by simp
  map_smul' c v := by
    apply ρ.asModuleEquiv.injective
    exact (isSchurLinear_iff_endField ρ t).mp hs c v

@[simp] theorem schurOperator_apply (t : linearNormalizer ρ) (hs : IsSchurLinear ρ t)
    (v : ρ.asModule) :
    ρ.asModuleEquiv (schurOperator ρ t hs v) = t.val.val (ρ.asModuleEquiv v) := rfl

theorem schurOperator_square (t : linearNormalizer ρ) (hs : IsSchurLinear ρ t)
    (ht : t ^ 2 = 1) : schurOperator ρ t hs * schurOperator ρ t hs = 1 := by
  have hh : t.val.val * t.val.val = 1 := by
    simpa only [pow_two, Subgroup.coe_mul, Subgroup.coe_one, Units.val_mul, Units.val_one] using congrArg (fun u : linearNormalizer ρ => u.val.val) ht
  ext v
  apply ρ.asModuleEquiv.injective
  change t.val.val (t.val.val (ρ.asModuleEquiv v)) = ρ.asModuleEquiv v
  exact LinearMap.congr_fun hh (ρ.asModuleEquiv v)

theorem schurOperator_ne_one (t : linearNormalizer ρ) (hs : IsSchurLinear ρ t)
    (ht : t ≠ 1) : schurOperator ρ t hs ≠ 1 := by
  intro he
  apply ht
  apply Subtype.ext
  apply Units.ext
  ext v
  have hv := LinearMap.congr_fun he (ρ.asModuleEquiv.symm v)
  exact congrArg ρ.asModuleEquiv hv

variable [FiniteDimensional (ZMod 2) V] [IsIrreducible ρ]

theorem schurOperator_rank (t : linearNormalizer ρ) (hs : IsSchurLinear ρ t) :
    schurDegree 2 ρ * operatorFixedCodim (schurOperator ρ t hs) =
      operatorFixedCodim t.val.val := by
  let E := Module.End (ZMod 2)[G] ρ.asModule
  let T := schurOperator ρ t hs
  have he := operatorFixedCodim_eq_of_equiv (T.restrictScalars (ZMod 2))
    t.val.val ρ.asModuleEquiv (fun _ => rfl)
  rw [← he]
  change Module.finrank (ZMod 2) E * Module.finrank E (LinearMap.range (T - 1)) =
    Module.finrank (ZMod 2) (LinearMap.range (T.restrictScalars (ZMod 2) - 1))
  exact Module.finrank_mul_finrank (ZMod 2) E (LinearMap.range (T - 1))

variable (K : Type*) [Field K] [Algebra (Module.End (ZMod 2)[G] ρ.asModule) K]

theorem schurOperator_baseChange_rank (t : linearNormalizer ρ) (hs : IsSchurLinear ρ t) :
    schurDegree 2 ρ * operatorFixedCodim ((schurOperator ρ t hs).baseChange K) ≤
      fixedCodim (normalizerRepresentation ρ) (Subgroup.zpowers t) := by
  have he := Triality.OuterDisplacement.displacement_finrank_baseChange
    (schurOperator ρ t hs) K
  change operatorFixedCodim ((schurOperator ρ t hs).baseChange K) =
    operatorFixedCodim (schurOperator ρ t hs) at he
  rw [he, schurOperator_rank]
  exact operatorFixedCodim_le_fixedCodim (normalizerRepresentation ρ)
    (Subgroup.zpowers t) (Subgroup.mem_zpowers t)

theorem schurOperator_baseChange_ne_one (t : linearNormalizer ρ) (hs : IsSchurLinear ρ t)
    (ht : t ≠ 1) : (schurOperator ρ t hs).baseChange K ≠ 1 := by
  intro he
  apply schurOperator_ne_one ρ t hs ht
  ext v
  apply Module.FaithfullyFlat.tensorProduct_mk_injective
    (A := Module.End (ZMod 2)[G] ρ.asModule) (B := K) ρ.asModule
  simpa only [LinearMap.baseChange_tmul, Module.End.one_apply, TensorProduct.mk_apply] using
    LinearMap.congr_fun he ((1 : K) ⊗ₜ v)


omit [FiniteDimensional (ZMod 2) V] [IsIrreducible ρ] in
theorem exists_schurOperator_intertwining (hf : Function.Injective ρ)
    (t : linearNormalizer ρ) (hs : IsSchurLinear ρ t) :
    ∃ α : MulAut G, ∀ g,
      schurOperator ρ t hs * ρ.endFieldRep g =
        ρ.endFieldRep (α g) * schurOperator ρ t hs := by
  have hf' : Function.Injective ρ.asGroupHom := fun g h he => hf (congrArg Units.val he)
  let e : G ≃* actionImage ρ := MonoidHom.ofInjective hf'
  let α : MulAut G := (e.trans ((actionImage ρ).normalizerMonoidHom t)).trans e.symm
  refine ⟨α, ?_⟩
  intro g
  have hh : ρ.asGroupHom (α g) = t.val * ρ.asGroupHom g * t.val⁻¹ := by
    exact congrArg Subtype.val (e.apply_symm_apply
      ((actionImage ρ).normalizerMonoidHom t (e g)))
  have hh' : ρ (α g) * t.val.val = t.val.val * ρ g := by
    have hh' := congrArg Units.val hh
    change ρ (α g) = t.val.val * ρ g * (↑t.val⁻¹ : Module.End (ZMod 2) V) at hh'
    rw [hh']
    simp [mul_assoc]
  ext v
  apply ρ.asModuleEquiv.injective
  exact (LinearMap.congr_fun hh' (ρ.asModuleEquiv v)).symm

theorem exists_baseChange_intertwining (hf : Function.Injective ρ)
    (t : linearNormalizer ρ) (hs : IsSchurLinear ρ t) :
    ∃ α : MulAut G, ∀ g,
      (schurOperator ρ t hs).baseChange K * (extendScalars K ρ.endFieldRep) g =
        (extendScalars K ρ.endFieldRep) (α g) * (schurOperator ρ t hs).baseChange K := by
  obtain ⟨α, hα⟩ := exists_schurOperator_intertwining ρ hf t hs
  refine ⟨α, fun g => ?_⟩
  simpa only [LinearMap.baseChange_mul, extendScalars_apply] using congrArg (LinearMap.baseChange K) (hα g)

theorem ratio_of_baseChange (t : linearNormalizer ρ) (hs : IsSchurLinear ρ t)
    {a b : ℕ} (h : a * Module.finrank K
      (K ⊗[Module.End (ZMod 2)[G] ρ.asModule] ρ.asModule) ≤
        b * operatorFixedCodim ((schurOperator ρ t hs).baseChange K)) :
    a * Module.finrank (ZMod 2) V ≤
      b * fixedCodim (normalizerRepresentation ρ) (Subgroup.zpowers t) := by
  calc
    a * Module.finrank (ZMod 2) V = schurDegree 2 ρ *
        (a * Module.finrank K
          (K ⊗[Module.End (ZMod 2)[G] ρ.asModule] ρ.asModule)) := by
      rw [finrank_eq_schurDegree_mul 2 ρ K]
      ring
    _ ≤ schurDegree 2 ρ *
        (b * operatorFixedCodim ((schurOperator ρ t hs).baseChange K)) :=
      Nat.mul_le_mul_left _ h
    _ = b * (schurDegree 2 ρ *
        operatorFixedCodim ((schurOperator ρ t hs).baseChange K)) := by ring
    _ ≤ _ := Nat.mul_le_mul_left b (schurOperator_baseChange_rank ρ K t hs)



/-- An actual representation equivalence transports an involution estimate,
retaining the automorphism implemented by the original normalizer. -/
theorem split_rank_of_equiv {W : Type*} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (hf : Function.Injective ρ)
    (τ : Representation K G W) (e : (extendScalars K ρ.endFieldRep).Equiv τ)
    {a : ℕ}
    (hpair : ∀ (T : Module.End K W) (α : MulAut G),
      T ≠ 1 → T * T = 1 → (∀ g, T * τ g = τ (α g) * T) → a ≤ operatorFixedCodim T)
    (t : linearNormalizer ρ) (ht : t ≠ 1) (ht2 : t ^ 2 = 1)
    (hs : IsSchurLinear ρ t) :
    a ≤ operatorFixedCodim ((schurOperator ρ t hs).baseChange K) := by
  let T := (schurOperator ρ t hs).baseChange K
  let C := e.toLinearEquiv.conjRingEquiv
  obtain ⟨α, hα⟩ := exists_baseChange_intertwining ρ K hf t hs
  have hC (g : G) :
      C ((extendScalars K ρ.endFieldRep) g) = τ g := by
    apply LinearMap.ext
    intro v
    change e.toLinearEquiv ((extendScalars K ρ.endFieldRep) g (e.toLinearEquiv.symm v)) = _
    have hh := LinearMap.congr_fun (e.isIntertwining' g) (e.toLinearEquiv.symm v)
    change e.toLinearEquiv ((extendScalars K ρ.endFieldRep) g (e.toLinearEquiv.symm v)) =
      τ g (e.toLinearEquiv (e.toLinearEquiv.symm v)) at hh
    simpa only [e.toLinearEquiv.apply_symm_apply] using hh
  have hn : C T ≠ 1 := by
    intro he
    apply schurOperator_baseChange_ne_one ρ K t hs ht
    exact C.injective (he.trans C.map_one.symm)
  have hsq : C T * C T = 1 := by
    rw [← map_mul]
    have hT : T * T = 1 := by
      dsimp only [T]
      rw [← LinearMap.baseChange_mul, schurOperator_square ρ t hs ht2,
        LinearMap.baseChange_one]
    rw [hT, map_one]
  have hcov (g : G) :
      C T * τ g =
        τ (α g) * C T := by
    simpa only [map_mul, hC] using congrArg C (hα g)
  have hb := hpair (C T) α hn hsq hcov
  have he := operatorFixedCodim_eq_of_equiv T (C T) e.toLinearEquiv (by
    intro v
    change e.toLinearEquiv (T v) = e.toLinearEquiv (T (e.toLinearEquiv.symm (e.toLinearEquiv v)))
    rw [e.toLinearEquiv.symm_apply_apply])
  exact he.symm ▸ hb


section G2
omit [IsIrreducible ρ]
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
  (σ : Representation (ZMod 2) (Atlas.G2.Model F) V) [IsIrreducible σ]

theorem twice_schurDegree {r : ℕ} (hr : 2 ≤ r) (hF : Nat.card F = 2 ^ r)
    (hf : Function.Injective σ) (hd : Module.finrank (ZMod 2) V = 18 * r) :
    r = 2 * schurDegree 2 σ := by
  obtain ⟨hs, t, l, ht, _, hrt, hdim, hne, hb⟩ :=
    CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.Nonbinary.exists_basic_parameters
      σ hr hF hf
  exact (CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.TensorWindow.parameters_in_tensor_window
    l hs ht hb hne hrt hdim (by omega) (by omega)).2.2.1

theorem split_finrank {r : ℕ} (hr : 2 ≤ r) (hF : Nat.card F = 2 ^ r)
    (hf : Function.Injective σ) (hd : Module.finrank (ZMod 2) V = 18 * r)
    (L : Type*) [Field L] [Algebra (Module.End (ZMod 2)[Atlas.G2.Model F] σ.asModule) L] :
    Module.finrank L (L ⊗[Module.End (ZMod 2)[Atlas.G2.Model F] σ.asModule] σ.asModule) = 36 := by
  apply Nat.eq_of_mul_eq_mul_left (schurDegree_pos 2 σ)
  rw [← finrank_eq_schurDegree_mul 2 σ L, hd, twice_schurDegree σ hr hF hf hd]
  ring

theorem displacement_bound_of_split_rank {r : ℕ} (hr : 2 ≤ r)
    (hF : Nat.card F = 2 ^ r) (hf : Function.Injective σ)
    (hd : Module.finrank (ZMod 2) V = 18 * r)
    (L : Type*) [Field L] [Algebra (Module.End (ZMod 2)[Atlas.G2.Model F] σ.asModule) L]
    (t : linearNormalizer σ) (hs : IsSchurLinear σ t)
    (hmove : 15 ≤ operatorFixedCodim ((schurOperator σ t hs).baseChange L)) :
    5 * Module.finrank (ZMod 2) V ≤
      12 * fixedCodim (normalizerRepresentation σ) (Subgroup.zpowers t) := by
  apply ratio_of_baseChange σ L t hs
  rw [split_finrank σ hr hF hf hd L]
  omega

end G2
end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.TensorWindow.HalfTensor
