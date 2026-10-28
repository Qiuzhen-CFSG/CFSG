module
public import Theory.Representation.QuadraticFourGroup.TensorClassification.ProductFactors
public import Theory.Representation.SL2.SchurTensorDisplacement.Exchange

/-!
# Exact displacement of an exchanged irreducible product

An involution swapping two factors identifies their irreducible representations.
A nonzero block of the actual exchanger, obtained by tensor contraction, is an
intertwiner between the factors; Schur's lemma makes it an equivalence. This
constructs symmetric tensor coordinates. Scalar rigidity and the square-one
equation then reduce the actual operator to tensor interchange, with displacement
`d.choose 2`. Factors of dimension at least four give the three-eighths bound.

The Suzuki component-pair consumer uses these coordinates after passing through
the actual Schur field; it supplies no tensor-equivalence assumption.
Source: Aschbacher--Smith D.3.7, printed pp.197--198.
-/

public noncomputable section
open scoped TensorProduct MonoidAlgebra
open Module Representation
open Representation.QuadraticFourGroup.TensorClassification
namespace Representation.ExchangedProduct
variable {F G U W : Type*} [Field F] [Group G]
  [AddCommGroup U] [Module F U] [FiniteDimensional F U]
  [AddCommGroup W] [Module F W] [FiniteDimensional F W]

omit [FiniteDimensional F W] in
-- An exchanger identifies the two simple factors via an actual nonzero block.
private theorem factors_equiv (τ : Representation F G U) (μ : Representation F G W)
    [τ.IsIrreducible] [μ.IsIrreducible]
    (T : Module.End F (U ⊗[F] W)) (hT : Function.Injective T)
    (he : ∀ g z, T (externalTensor τ μ (g,1) z) = externalTensor τ μ (1,g) (T z)) :
    Nonempty (τ.Equiv μ) := by
  classical
  let : Nontrivial U := Subrepresentation.irreducible_module_nontrivial τ
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial μ
  obtain ⟨u,hu⟩ := exists_ne (0 : U)
  obtain ⟨w,hw⟩ := exists_ne (0 : W)
  let b := (Module.finBasis F U).equivFun
  let e : U ⊗[F] W ≃ₗ[F] (Fin (finrank F U) → W) :=
    (_root_.TensorProduct.comm F U W).trans ((TensorProduct.congr (LinearEquiv.refl F W) b).trans
      (TensorProduct.piScalarRight F F W _))
  have hne : e (T (u ⊗ₜ[F] w)) ≠ 0 := by
    intro hz
    have hz' : u ⊗ₜ[F] w = 0 := hT ((e.injective (by simpa using hz)).trans (map_zero T).symm)
    obtain ⟨l,hl⟩ := Module.Projective.exists_dual_eq_one F hu
    have h := congrArg (fun z => (_root_.TensorProduct.lid F W) (l.rTensor W z)) hz'
    exact hw (by simpa [hl] using h)
  obtain ⟨i,hi⟩ : ∃ i, e (T (u ⊗ₜ[F] w)) i ≠ 0 := by
    by_contra! h
    exact hne (funext h)
  have heq (g : G) (z : U ⊗[F] W) :
      e (externalTensor τ μ (1,g) z) = fun i => μ g (e z i) := by
    induction z using TensorProduct.induction_on with
    | zero => ext i; simp
    | tmul x y => simp [e,externalTensor_apply]
    | add x y hx hy => simp only [map_add,hx,hy]; ext i; exact (map_add (μ g) _ _).symm
  let f : τ.IntertwiningMap μ := {
    toLinearMap := (LinearMap.proj i).comp (e.toLinearMap.comp
      (T.comp ((TensorProduct.mk F U W).flip w)))
    isIntertwining' g := by
      ext x
      change e (T (τ g x ⊗ₜ[F] w)) i = μ g (e (T (x ⊗ₜ[F] w)) i)
      have h := congrFun ((congrArg e (he g (x ⊗ₜ[F] w))).trans (heq g _)) i
      simpa [externalTensor_apply] using h }
  have hf : f ≠ 0 := by
    intro hz
    exact hi (congrArg (fun q : τ.IntertwiningMap μ => q u) hz)
  exact ⟨f.ofBijective ((IsIrreducible.bijective_or_eq_zero f).resolve_right hf)⟩


section Algebraic
variable [IsAlgClosed F] [CharP F 2]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- An actual involution exchanging the factors of an irreducible product
representation has symmetric tensor coordinates and their exact displacement. -/
theorem exists_symmetric_tensor (ρ : Representation F (G × G) V) [ρ.IsIrreducible]
    (T : Module.End F V) (h2 : T*T = 1)
    (hT : ∀ g v, T (ρ g v) = ρ (g.2,g.1) (T v)) :
    ∃ (d : ℕ) (τ : Representation F G (Fin d → F)), τ.IsIrreducible ∧
      Nonempty (ρ.Equiv (externalTensor τ τ)) ∧
      finrank F (T-1).range = d.choose 2 := by
  obtain ⟨d₁,d₂,τ,μ,hτ,hμ,⟨e⟩⟩ := ProductFactors.exists_irreducible_externalTensor_factors ρ
  let := hτ
  let := hμ
  let S := e.toLinearEquiv.conjRingEquiv T
  have hS2 : S*S = 1 := by
    change e.toLinearEquiv.conjRingEquiv T * e.toLinearEquiv.conjRingEquiv T = 1
    rw [←map_mul,h2,map_one]
  have hSe (g : G × G) (v) : S (externalTensor τ μ g v) =
      externalTensor τ μ (g.2,g.1) (S v) := by
    obtain ⟨w,rfl⟩ := e.surjective v
    have he (g : G × G) (v) : e (ρ g v) = externalTensor τ μ g (e v) :=
      LinearMap.congr_fun (e.isIntertwining' g) v
    change e (T (e.symm (externalTensor τ μ g (e w)))) = _
    rw [←he,e.symm_apply_apply,hT,he]
    change _ = externalTensor τ μ (g.2,g.1) (e (T (e.symm (e w))))
    rw [e.symm_apply_apply]
  have hSi : Function.Injective S := by
    intro v w hvw
    have h := congrArg S hvw
    simpa only [←Module.End.mul_apply,hS2,Module.End.one_apply] using h
  obtain ⟨f⟩ := factors_equiv τ μ S hSi (fun g => hSe (g,1))
  let E := e.trans (externalTensorEquiv (Representation.Equiv.refl τ) f.symm)
  let R := E.toLinearEquiv.conjRingEquiv T
  have hR2 : R*R = 1 := by
    change E.toLinearEquiv.conjRingEquiv T * E.toLinearEquiv.conjRingEquiv T = 1
    rw [←map_mul,h2,map_one]
  have hRe (g : G × G) (v) : R (externalTensor τ τ g v) =
      externalTensor τ τ (g.2,g.1) (R v) := by
    obtain ⟨w,rfl⟩ := E.surjective v
    have he (g : G × G) (v) : E (ρ g v) = externalTensor τ τ g (E v) :=
      LinearMap.congr_fun (E.isIntertwining' g) v
    change E (T (E.symm (externalTensor τ τ g (E w)))) = _
    rw [←he,E.symm_apply_apply,hT,he]
    change _ = externalTensor τ τ (g.2,g.1) (E (T (E.symm (E w))))
    rw [E.symm_apply_apply]
  let δ : MulAut (G × G) := MulEquiv.prodComm
  have hδ : δ^2 = 1 := by ext g <;> rfl
  let π : Representation F (G × G) (Fin d₁ → F) := τ.comp (MonoidHom.fst G G)
  let : (π.tprod (π.comp δ.toMonoidHom)).IsIrreducible :=
    (RepEquiv.ofRepresentationEquiv E.symm).irreducible_of_euqiv inferInstance
  have hr := SL2.SchurTensorDisplacement.paired_involution_rank π δ hδ 1 R hR2 (by
    intro g
    apply LinearMap.ext
    intro v
    simp only [one_mul,mul_one,inv_one]
    change R (externalTensor τ τ g v) = externalTensor τ τ (g.2,g.1) (R v)
    exact hRe g v)
  have he := LinearMap.FixedSpaceTransport.finrank_range_sub_one_equiv E.toLinearEquiv T R
    (fun v => by change E (T v) = E (T (E.symm (E v))); rw [E.symm_apply_apply])
  exact ⟨d₁,τ,hτ,⟨E⟩,he.trans hr⟩

omit [IsAlgClosed F] [CharP F 2] [FiniteDimensional F V] in
/-- Faithfulness passes to the first tensor factor through the original
coordinate equivalence. -/
private theorem factor_faithful (ρ : Representation F (G × G) V)
    (hf : Function.Injective ρ) {d : ℕ} (τ : Representation F G (Fin d → F))
    (e : ρ.Equiv (externalTensor τ τ)) : Function.Injective τ := by
  intro a b hab
  have hh : ρ (a,1) = ρ (b,1) := by
    ext v
    apply e.injective
    have he (g : G × G) : e (ρ g v) = externalTensor τ τ g (e v) :=
      LinearMap.congr_fun (e.isIntertwining' g) v
    change e (ρ (a,1) v) = e (ρ (b,1) v)
    rw [he,he,externalTensor_apply,externalTensor_apply,hab]
  exact congrArg Prod.fst (hf hh)

/-- Factors of degree at least four force the stronger three-eighths
bound for the literal exchanging operator. -/
theorem three_mul_finrank_le_eight_displacement
    (ρ : Representation F (G × G) V) [ρ.IsIrreducible]
    (hf : Function.Injective ρ)
    (hdegree : ∀ (d : ℕ) (τ : Representation F G (Fin d → F)),
      τ.IsIrreducible → Function.Injective τ → 4 ≤ d)
    (T : Module.End F V) (h2 : T*T = 1)
    (hT : ∀ g v, T (ρ g v) = ρ (g.2,g.1) (T v)) :
    3 * finrank F V ≤ 8 * finrank F (T-1).range := by
  obtain ⟨d,τ,hτ,⟨e⟩,hr⟩ := exists_symmetric_tensor ρ T h2 hT
  have hd := hdegree d τ hτ (factor_faithful ρ hf τ e)
  rw [e.toLinearEquiv.finrank_eq,hr]
  change 3 * finrank F (TensorInterchange.Space F d) ≤ _
  rw [TensorInterchange.finrank_space]
  have hc : ∀ d : ℕ, 2 * d.choose 2 + d = d*d := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.choose_succ_succ,Nat.choose_one_right]; nlinarith
  have hh := hc d
  nlinarith
end Algebraic

end Representation.ExchangedProduct
