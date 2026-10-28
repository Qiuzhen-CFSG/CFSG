module
public import Theory.Representation.SL3.NaturalNormalizerFixed
public import Theory.Representation.SL3.DualLiftCentralizers
public import Theory.Representation.SemilinearInvolutionFixedCard
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Paired natural and dual fixed spaces for SL₃ normalizers

An additive normalizer on the natural three-space and an additive
normalizer on its dual, inducing the same automorphism of the full SL₃,
have the same field twist. Their pairing is preserved up to a scalar;
for linear involutions in characteristic two that scalar is one.

For an exponent-two actor group whose natural action image has order
larger than |F|, the product of the two common fixed-space orders is at
most |F|³. A nontrivial field twist gives square-root fixed-space counts
on both factors. In the linear case, displacement embeds the image into
Hom(V/X, Yᵒ), where X and Y are the actual fixed spaces. If their dimensions
sum to more than three, this hom space has dimension at most one,
contradicting the image-size hypothesis. That hypothesis is necessary:
a single root group of order |F| fixes planes on both factors.

The original MS application, retaining its literal quotient map and full
SL₃ marking, is in NonblockMSPairedFixed. This proves the sharper estimate
(+) in Aschbacher–Smith C.1.35, printed p.139, used in 4.3.11, p.617.
-/

@[expose] public section
noncomputable section
open Matrix
namespace Representation.SL3NaturalFixed
variable {F : Type*} [Field F]

/-- The additive commutant of the dual SL₃ module consists of field scalars. -/
theorem dual_centralizer_scalar
    (q : Module.Dual F (Fin 3 → F) →+ Module.Dual F (Fin 3 → F))
    (hq : ∀ a φ, q ((specialLinearNatural 3).dual a φ) =
      (specialLinearNatural 3).dual a (q φ)) :
    ∃ c : F, ∀ φ, q φ = c • φ := by
  let e := SL3ParabolicNatural.dualVectorCoordinates (F := F)
  let r := e.toAddMonoidHom.comp (q.comp e.symm.toAddMonoidHom)
  have he (a : SpecialLinearGroup (Fin 3) F) (φ : Module.Dual F (Fin 3 → F)) :
      e ((specialLinearNatural 3).dual (a.transpose)⁻¹ φ) = specialLinearNatural 3 a (e φ) := by
    rw [SL3ParabolicNatural.dualVectorCoordinates_action,inv_inv]
    rfl
  obtain ⟨c,hc⟩ := SL3OddNaturalNormalizer.centralizer_scalar r (by
    intro a v
    obtain ⟨φ,rfl⟩ := e.surjective v
    change e (q (e.symm (specialLinearNatural 3 a (e φ)))) =
      specialLinearNatural 3 a (e (q (e.symm (e φ))))
    rw [←he,e.symm_apply_apply,e.symm_apply_apply,hq,he])
  refine ⟨c,fun φ => e.injective ?_⟩
  have hh := hc (e φ)
  change e (q (e.symm (e φ))) = c • e φ at hh
  rw [e.symm_apply_apply,←map_smul] at hh
  exact hh

/-- Paired normalizers with the same SL₃ automorphism preserve evaluation up to a scalar. -/
theorem paired_semilinear_scalar
    (f : (Fin 3 → F) ≃+ (Fin 3 → F))
    (g : Module.Dual F (Fin 3 → F) ≃+ Module.Dual F (Fin 3 → F))
    (α : MulAut (SpecialLinearGroup (Fin 3) F)) (σ : F ≃+* F)
    (hσ : ∀ c v, f (c • v) = σ c • f v)
    (hf : ∀ a v, f (specialLinearNatural 3 a v) = specialLinearNatural 3 (α a) (f v))
    (hg : ∀ a φ, g ((specialLinearNatural 3).dual a φ) =
      (specialLinearNatural 3).dual (α a) (g φ)) :
    ∃ c : F, ∀ φ v, (g φ) (f v) = σ c * σ (φ v) := by
  let q : Module.Dual F (Fin 3 → F) →+ Module.Dual F (Fin 3 → F) :=
    { toFun := fun φ =>
        { toFun := fun v => σ.symm ((g φ) (f v))
          map_add' := by intro v w; simp only [map_add]
          map_smul' := by
            intro c v
            rw [hσ,map_smul]
            change σ.symm (σ c * (g φ) (f v)) = c * σ.symm ((g φ) (f v))
            rw [map_mul,σ.symm_apply_apply] }
      map_zero' := by ext v; simp
      map_add' := by intro φ ψ; ext v; simp }
  have hq : ∀ a φ, q ((specialLinearNatural 3).dual a φ) =
      (specialLinearNatural 3).dual a (q φ) := by
    intro a φ
    apply LinearMap.ext
    intro v
    change σ.symm ((g ((specialLinearNatural 3).dual a φ)) (f v)) =
      σ.symm ((g φ) (f (specialLinearNatural 3 a⁻¹ v)))
    rw [hg,hf,map_inv]
    rfl
  obtain ⟨c,hc⟩ := dual_centralizer_scalar q hq
  refine ⟨c,fun φ v => ?_⟩
  have hh := congrArg (fun ψ : Module.Dual F (Fin 3 → F) => σ (ψ v)) (hc φ)
  change σ (σ.symm ((g φ) (f v))) = σ (c * φ v) at hh
  simpa only [σ.apply_symm_apply,map_mul] using hh

/-- The dual normalizer has the same field twist as the natural normalizer. -/
theorem paired_semilinear
    (f : (Fin 3 → F) ≃+ (Fin 3 → F))
    (g : Module.Dual F (Fin 3 → F) ≃+ Module.Dual F (Fin 3 → F))
    (α : MulAut (SpecialLinearGroup (Fin 3) F)) (σ : F ≃+* F)
    (hσ : ∀ c v, f (c • v) = σ c • f v)
    (hf : ∀ a v, f (specialLinearNatural 3 a v) = specialLinearNatural 3 (α a) (f v))
    (hg : ∀ a φ, g ((specialLinearNatural 3).dual a φ) =
      (specialLinearNatural 3).dual (α a) (g φ)) :
    ∀ c φ, g (c • φ) = σ c • g φ := by
  obtain ⟨b,hb⟩ := paired_semilinear_scalar f g α σ hσ hf hg
  intro c φ
  apply LinearMap.ext
  intro v
  obtain ⟨w,rfl⟩ := f.surjective v
  change (g (c • φ)) (f w) = σ c * (g φ) (f w)
  rw [hb,hb]
  change σ b * σ (c * φ w) = σ c * (σ b * σ (φ w))
  rw [map_mul]
  ring


variable [CharP F 2]

omit [CharP F 2] in
/-- The scalar twist of an involution is itself involutive. -/
theorem semilinear_involution_scalar_involutive
    (f : (Fin 3 → F) ≃+ (Fin 3 → F)) (hff : Function.Involutive f)
    (σ : F ≃+* F) (hσ : ∀ c v, f (c • v) = σ c • f v) :
    Function.Involutive σ := by
  intro c
  have hh := hff (c • Pi.single 0 1)
  rw [hσ,hσ,hff] at hh
  simpa using congrFun hh 0

/-- A nontrivial field involution gives the exact paired fixed-space product. -/
theorem paired_involution_fixed_product
    (f : (Fin 3 → F) ≃+ (Fin 3 → F))
    (g : Module.Dual F (Fin 3 → F) ≃+ Module.Dual F (Fin 3 → F))
    (hff : Function.Involutive f) (hgg : Function.Involutive g)
    (α : MulAut (SpecialLinearGroup (Fin 3) F)) (σ : F ≃+* F)
    (hσne : σ ≠ RingEquiv.refl F)
    (hσ : ∀ c v, f (c • v) = σ c • f v)
    (hf : ∀ a v, f (specialLinearNatural 3 a v) = specialLinearNatural 3 (α a) (f v))
    (hg : ∀ a φ, g ((specialLinearNatural 3).dual a φ) =
      (specialLinearNatural 3).dual (α a) (g φ)) :
    Nat.card {v : Fin 3 → F // f v = v} *
      Nat.card {φ : Module.Dual F (Fin 3 → F) // g φ = φ} = Nat.card F ^ 3 := by
  have hs := semilinear_involution_scalar_involutive f hff σ hσ
  have h1 := SemilinearInvolution.fixed_card_sq σ hs hσne f.toAddMonoidHom hff hσ
  have h2 := SemilinearInvolution.fixed_card_sq σ hs hσne g.toAddMonoidHom hgg
    (paired_semilinear f g α σ hσ hf hg)
  change Nat.card {v : Fin 3 → F // f v = v} ^ 2 = _ at h1
  change Nat.card {φ : Module.Dual F (Fin 3 → F) // g φ = φ} ^ 2 = _ at h2
  rw [Nat.card_fun,Nat.card_fin] at h1
  rw [Nat.card_congr (SL3ParabolicNatural.dualVectorCoordinates (F := F)).toEquiv,
    Nat.card_fun,Nat.card_fin] at h2
  have he : Nat.card {v : Fin 3 → F // f v = v} =
      Nat.card {φ : Module.Dual F (Fin 3 → F) // g φ = φ} := by nlinarith
  rw [←he,←pow_two,h1]

/-- A linear involution on both factors preserves the pairing exactly. -/
theorem paired_linear_involution_pairing
    (f : (Fin 3 → F) ≃+ (Fin 3 → F))
    (g : Module.Dual F (Fin 3 → F) ≃+ Module.Dual F (Fin 3 → F))
    (hff : Function.Involutive f) (hgg : Function.Involutive g)
    (α : MulAut (SpecialLinearGroup (Fin 3) F))
    (hlin : ∀ (c : F) v, f (c • v) = c • f v)
    (hf : ∀ a v, f (specialLinearNatural 3 a v) = specialLinearNatural 3 (α a) (f v))
    (hg : ∀ a φ, g ((specialLinearNatural 3).dual a φ) =
      (specialLinearNatural 3).dual (α a) (g φ)) :
    ∀ φ v, (g φ) (f v) = φ v := by
  obtain ⟨c,hc⟩ := paired_semilinear_scalar f g α (RingEquiv.refl F) hlin hf hg
  have hc' : ∀ φ v, (g φ) (f v) = c * φ v := hc
  have hcc : c*c=1 := by
    have hh := hc' (g (LinearMap.proj 0)) (f (Pi.single 0 1))
    rw [hgg,hff,hc'] at hh
    simpa using hh.symm
  have hc1 : c=1 := by
    have hz : (c+1)^2=0 := by
      rw [CharTwo.add_sq,pow_two,hcc,one_pow,CharTwo.add_self_eq_zero]
    exact (eq_neg_of_add_eq_zero_left (sq_eq_zero_iff.mp hz)).trans (CharTwo.neg_eq 1)
  simpa only [hc1,one_mul] using hc'

omit [CharP F 2] in
private theorem displacement_card_bound [Finite F]
    {B V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (X Z : Submodule F V) (f : B → V →ₗ[F] V) (hf : Function.Injective f)
    (hfix : ∀ b v, v ∈ X → f b v = v)
    (hmove : ∀ b v, f b v - v ∈ Z) :
    Nat.card B ≤ Nat.card F ^
      (Module.finrank F (V ⧸ X) * Module.finrank F Z) := by
  let : Finite ((V ⧸ X) →ₗ[F] Z) := Module.finite_of_finite F
  let δ (b : B) : V →ₗ[F] Z := (f b - LinearMap.id).codRestrict Z (hmove b)
  let q (b : B) : (V ⧸ X) →ₗ[F] Z := X.liftQ (δ b) (by
    intro v hv
    apply Subtype.ext
    exact sub_eq_zero.mpr (hfix b v hv))
  have hq : Function.Injective q := by
    intro b c h
    apply hf
    apply LinearMap.ext
    intro v
    have hh := congrArg (fun k : (V ⧸ X) →ₗ[F] Z => (k (X.mkQ v) : V)) h
    change f b v - v = f c v - v at hh
    exact sub_left_inj.mp hh
  calc
    Nat.card B ≤ Nat.card ((V ⧸ X) →ₗ[F] Z) := Nat.card_le_card_of_injective q hq
    _ = _ := by rw [Module.natCard_eq_pow_finrank (K := F),Module.finrank_linearMap]

variable [Finite F] {H : Type*} [Group H]

/-- An action image larger than the field forces combined fixed codimension at least three. -/
theorem paired_fixed_card_le
    (β : H →* MulAut (Multiplicative (Fin 3 → F)))
    (δ : H →* MulAut (Multiplicative (Module.Dual F (Fin 3 → F))))
    (α : H →* MulAut (SpecialLinearGroup (Fin 3) F))
    (hsq : ∀ x : H, x^2=1)
    (hf : ∀ x a v, (β x (Multiplicative.ofAdd (specialLinearNatural 3 a v))).toAdd =
      specialLinearNatural 3 (α x a) ((β x (Multiplicative.ofAdd v)).toAdd))
    (hg : ∀ x a φ, (δ x (Multiplicative.ofAdd ((specialLinearNatural 3).dual a φ))).toAdd =
      (specialLinearNatural 3).dual (α x a) ((δ x (Multiplicative.ofAdd φ)).toAdd))
    (hlarge : Nat.card F < Nat.card β.range) :
    Nat.card {v : Fin 3 → F // ∀ x, (β x (Multiplicative.ofAdd v)).toAdd = v} *
      Nat.card {φ : Module.Dual F (Fin 3 → F) // ∀ x, (δ x (Multiplicative.ofAdd φ)).toAdd = φ} ≤
        Nat.card F ^ 3 := by
  classical
  let : Finite (Module.Dual F (Fin 3 → F)) :=
    Finite.of_equiv (Fin 3 → F) (SL3ParabolicNatural.dualVectorCoordinates (F := F)).symm.toEquiv
  let f (x : H) : (Fin 3 → F) ≃+ (Fin 3 → F) := (β x).toAdditive
  let g (x : H) : Module.Dual F (Fin 3 → F) ≃+ Module.Dual F (Fin 3 → F) := (δ x).toAdditive
  have hβsq (x : H) : Function.Involutive (f x) := by
    intro v
    have h : (β x)^2=1 := by rw [←map_pow,hsq,map_one]
    exact congrArg (fun a : MulAut (Multiplicative (Fin 3 → F)) =>
      (a (Multiplicative.ofAdd v)).toAdd) h
  have hδsq (x : H) : Function.Involutive (g x) := by
    intro v
    have h : (δ x)^2=1 := by rw [←map_pow,hsq,map_one]
    exact congrArg (fun a : MulAut (Multiplicative (Module.Dual F (Fin 3 → F))) =>
      (a (Multiplicative.ofAdd v)).toAdd) h
  choose σ hσ using fun x => semilinear_of_intertwines (f x) (α x) (hf x)
  by_cases hfield : ∃ x, σ x ≠ RingEquiv.refl F
  · obtain ⟨x,hx⟩ := hfield
    have hb := paired_involution_fixed_product (f x) (g x)
      (hβsq x) (hδsq x) (α x) (σ x) hx (hσ x) (hf x) (hg x)
    rw [←hb]
    exact Nat.mul_le_mul
      (Nat.card_le_card_of_injective
        (fun v : {v : Fin 3 → F // ∀ x, (f x) v = v} =>
          (⟨v.val,v.property x⟩ : {v : Fin 3 → F // (f x) v = v}))
        (fun _ _ h => Subtype.ext (congrArg (fun z : {v : Fin 3 → F // (f x) v = v} => z.val) h)))
      (Nat.card_le_card_of_injective
        (fun φ : {φ : Module.Dual F (Fin 3 → F) // ∀ x, (g x) φ = φ} =>
          (⟨φ.val,φ.property x⟩ : {φ : Module.Dual F (Fin 3 → F) // (g x) φ = φ}))
        (fun _ _ h => Subtype.ext (congrArg (fun z : {φ : Module.Dual F (Fin 3 → F) // (g x) φ = φ} => z.val) h)))
  push Not at hfield
  have hlin (x : H) (c : F) (v : Fin 3 → F) :
      (f x) (c • v) = c • (f x) v := by
    simpa only [hfield,RingEquiv.refl_apply] using hσ x c v
  have hdlin (x : H) (c : F) (φ : Module.Dual F (Fin 3 → F)) :
      (g x) (c • φ) = c • (g x) φ :=
    paired_semilinear (f x) (g x) (α x) (RingEquiv.refl F)
      (hlin x) (hf x) (hg x) c φ
  have hpair (x : H) := paired_linear_involution_pairing
    (f x) (g x) (hβsq x) (hδsq x) (α x) (hlin x) (hf x) (hg x)
  let X : Submodule F (Fin 3 → F) :=
    { carrier := {v | ∀ x, (f x) v = v}
      zero_mem' := by intro x; exact map_zero _
      add_mem' := by intro v w hv hw x; rw [map_add,hv,hw]
      smul_mem' := by intro c v hv x; rw [hlin,hv] }
  let Y : Submodule F (Module.Dual F (Fin 3 → F)) :=
    { carrier := {φ | ∀ x, (g x) φ = φ}
      zero_mem' := by intro x; exact map_zero _
      add_mem' := by intro v w hv hw x; rw [map_add,hv,hw]
      smul_mem' := by intro c v hv x; rw [hdlin,hv] }
  change Nat.card X * Nat.card Y ≤ _
  have hbound : Nat.card β.range ≤ Nat.card F ^
      (Module.finrank F ((Fin 3 → F) ⧸ X) * Module.finrank F Y.dualCoannihilator) := by
    let m (x : β.range) : (Fin 3 → F) ≃+ (Fin 3 → F) := x.val.toAdditive
    let b (x : β.range) : (Fin 3 → F) →ₗ[F] (Fin 3 → F) :=
      { (m x).toAddMonoidHom with
        map_smul' := by
          obtain ⟨a,ha⟩ := x.property
          intro c v
          change (x.val (Multiplicative.ofAdd (c • v))).toAdd = c • (x.val (Multiplicative.ofAdd v)).toAdd
          rw [←ha]
          exact hlin a c v }
    apply displacement_card_bound X Y.dualCoannihilator b
    · intro x y h
      apply Subtype.ext
      apply MulEquiv.ext
      intro v
      exact congrArg (fun t : (Fin 3 → F) →ₗ[F] (Fin 3 → F) =>
        Multiplicative.ofAdd (t v.toAdd)) h
    · intro x v hv
      obtain ⟨a,ha⟩ := x.property
      change (x.val (Multiplicative.ofAdd v)).toAdd = v
      rw [←ha]
      exact hv a
    · intro x v
      rw [Submodule.mem_dualCoannihilator]
      intro φ hφ
      obtain ⟨a,ha⟩ := x.property
      change φ ((x.val (Multiplicative.ofAdd v)).toAdd - v) = 0
      rw [←ha,map_sub,sub_eq_zero]
      have hh := hpair a φ v
      rw [hφ a] at hh
      exact hh
  have hx := X.finrank_quotient_add_finrank
  have hy := Subspace.finrank_add_finrank_dualCoannihilator_eq Y
  have hdim : Module.finrank F (Fin 3 → F) = 3 := by simp
  rw [hdim] at hx hy
  have hsum : Module.finrank F X + Module.finrank F Y ≤ 3 := by
    by_contra! hn
    have hprod : Module.finrank F ((Fin 3 → F) ⧸ X) *
        Module.finrank F Y.dualCoannihilator ≤ 1 := by
      have hx2 : Module.finrank F ((Fin 3 → F) ⧸ X) ≤ 2 := by omega
      interval_cases Module.finrank F ((Fin 3 → F) ⧸ X) <;> omega
    have hle := hbound.trans (Nat.pow_le_pow_right Nat.card_pos hprod)
    rw [pow_one] at hle
    exact (not_le_of_gt hlarge) hle
  rw [Module.natCard_eq_pow_finrank (K := F) (V := X),
    Module.natCard_eq_pow_finrank (K := F) (V := Y),←pow_add]
  exact Nat.pow_le_pow_right Nat.card_pos hsum

end Representation.SL3NaturalFixed
end
