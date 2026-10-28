module
public import Theory.Representation.SL2.EvenSquareExchange
public import Theory.SpecificGroups.PSL2.AutomorphismModel

/-!
# Small binary SL₂ squares

A faithful irreducible binary representation of SL₂(2ⁿ) × SL₂(2ⁿ), n≥3,
whose degree is at most 4(n+1) is a natural tensor on the entire space.
Its original Schur field has degree n, and both absolute factors have
degree two. No exchanging operator or Schur-linearity hypothesis is needed.

Frobenius periodicity of the product character makes the two irreducible
factor characters proportional to their twists. Linear independence of
irreducible traces makes those characters equal, so both highest weights
have the actual Schur period. Repeated binary digit blocks give degrees
s*b^t and s*c^t with n=s*t and b,c≥2. The budget forces t=1 and b=c=2.
Compatible field identifications and Noether--Deuring descent retain the
original component marking and the relative field twist in the natural tensor.

This removes the Schur-nonlinear exchange alternative in the Chapter D and
original Chapter 10 seed consumers. It does not exclude natural tensors.
Source: Steinberg's defining-characteristic SL₂ classification;
Aschbacher--Smith D.3.7, printed pp.197--199.
-/

public noncomputable section
open scoped MatrixGroups TensorProduct MonoidAlgebra
open Module Representation
open Representation.QuadraticFourGroup.TensorClassification
namespace Representation.SL2.SmallSquare
universe u

private theorem highestWeightSpan_zero_apply {K F : Type*} [Field K] [Field F]
    (e : K →+* F) (g : SL(2,K)) (v : (highestWeightSpan e 0).toSubmodule) :
    (highestWeightSpan e 0).toRepresentation g v = v := by
  apply Subtype.ext
  change polynomialAction F (Matrix.SpecialLinearGroup.map e g) v = v
  have hfix (f : MvPolynomial (Fin 2) F) (hf : f ∈ highestWeightSpan e 0) :
      polynomialAction F (Matrix.SpecialLinearGroup.map e g) f = f := by
    change f ∈ Submodule.span F _ at hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨h,rfl⟩ := hf
      simp only [pow_zero,map_one]
    | zero => exact map_zero _
    | add f h _ _ hf hh => simp only [map_add,hf,hh]
    | smul a f _ hf => simp only [map_smul,hf]
  exact hfix v v.property

private theorem weight_period_of_character_fixed
    {K F : Type*} [Field K] [Finite K] [Field F] [IsAlgClosed F] [CharP F 2]
    (e : K →+* F) (m : ℕ) (hm : m < Nat.card K) (s : ℕ)
    (hfix : ∀ g, (highestWeightSpan e m).toRepresentation.character g ^ (2^s) =
      (highestWeightSpan e m).toRepresentation.character g) :
    (Nat.card K-1) ∣ m*(2^s-1) := by
  let σ := iterateFrobeniusEquiv F 2 s
  have hχ : (highestWeightSpan e m).toRepresentation.character =
      (highestWeightSpan ((σ : F →+* F).comp e) m).toRepresentation.character := by
    funext g
    rw [highestWeightSpan_character_comp_embedding σ e m g]
    exact (hfix g).symm
  let := highestWeightSpan_isIrreducible_of_lt_card e m hm
  let := highestWeightSpan_isIrreducible_of_lt_card ((σ : F →+* F).comp e) m hm
  obtain ⟨φ⟩ := (Representation.character_eq_iff_equiv_of_irreducible _ _).mp hχ
  obtain ⟨a,ha⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hw := (highestWeightSpan_equiv_embedding_weights e ((σ : F →+* F).comp e)
    m m hm hm φ).1 a a.ne_zero
  change (e a)^m = ((e a)^(2^s))^m at hw
  rw [←pow_mul,mul_comm (2^s)] at hw
  have he : a^m = a^(m*2^s) := Units.ext (e.injective (by
    simpa only [Units.val_pow_eq_pow_val,map_pow] using hw))
  have hd := (pow_eq_pow_iff_modEq.mp he).dvd'
  rw [orderOf_eq_card_of_forall_mem_zpowers ha,Nat.card_units] at hd
  simpa only [Nat.mul_sub_left_distrib,mul_one] using hd


private theorem character_ne_zero
    {F G V : Type*} [Field F] [IsAlgClosed F] [Monoid G]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F G V) [ρ.IsIrreducible] : ρ.character ≠ 0 := by
  have h := linearIndependent_characters_of_pairwise_inequivalent
    (fun _ : Unit => V) (fun _ => ρ) (fun i j hij => (hij (Subsingleton.elim _ _)).elim)
  exact h.ne_zero ()

private theorem character_eq_of_proportional
    {F G : Type*} [Field F] [IsAlgClosed F] [Monoid G]
    {V W : Type u} [AddCommGroup V] [AddCommGroup W]
    [Module F V] [Module F W] [FiniteDimensional F V] [FiniteDimensional F W]
    (ρ : Representation F G V) (σ : Representation F G W)
    [ρ.IsIrreducible] [σ.IsIrreducible]
    (a : F) (ha : ∀ g, ρ.character g = a * σ.character g) :
    ρ.character = σ.character := by
  classical
  apply (character_eq_iff_equiv_of_irreducible ρ σ).mpr
  by_contra hne
  let M : Bool → Type u := fun b => if b then W else V
  let addM : ∀ b, AddCommGroup (M b) := fun b => by cases b <;> dsimp [M] <;> infer_instance
  let modM : ∀ b, Module F (M b) := fun b => by cases b <;> dsimp [M] <;> infer_instance
  let rep : ∀ b, Representation F G (M b) := fun b => by
    cases b
    · exact ρ
    · exact σ
  have finM : ∀ b, FiniteDimensional F (M b) := by
    intro b
    cases b <;> dsimp [M] <;> infer_instance
  have irr : ∀ b, IsIrreducible (rep b) := by
    intro b
    cases b <;> dsimp [rep] <;> infer_instance
  have hp : Pairwise fun i j => IsEmpty ((rep i).Equiv (rep j)) := by
    intro i j hij
    constructor
    intro e
    cases i <;> cases j
    · exact hij rfl
    · exact hne ⟨e⟩
    · exact hne ⟨e.symm⟩
    · exact hij rfl
  have hli := linearIndependent_characters_of_pairwise_inequivalent M rep hp
  have he : (1 : F) = 0 := (Fintype.linearIndependent_iff.mp hli)
    (fun b => if b then -a else 1) (by
      ext g
      simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte, one_smul,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      change -a * σ.character g + ρ.character g = 0
      rw [ha g]
      ring) false
  exact one_ne_zero he

private theorem factor_character_fixed
    {K F : Type*} [Field K] [Finite K] [Field F] [IsAlgClosed F] [CharP F 2]
    (e : K →+* F) (a b : ℕ) (ha : a < Nat.card K) (hb : b < Nat.card K)
    (s : ℕ)
    (h : ∀ x y,
      ((highestWeightSpan e a).toRepresentation.character x *
        (highestWeightSpan e b).toRepresentation.character y) ^ (2^s) =
      (highestWeightSpan e a).toRepresentation.character x *
        (highestWeightSpan e b).toRepresentation.character y) :
    ∀ x, (highestWeightSpan e a).toRepresentation.character x ^ (2^s) =
      (highestWeightSpan e a).toRepresentation.character x := by
  let τ := (highestWeightSpan e a).toRepresentation
  let μ := (highestWeightSpan e b).toRepresentation
  let := highestWeightSpan_isIrreducible_of_lt_card e a ha
  let := highestWeightSpan_isIrreducible_of_lt_card e b hb
  obtain ⟨y,hy⟩ : ∃ y, μ.character y ≠ 0 := by
    by_contra! hz
    exact character_ne_zero μ (funext hz)
  let f := iterateFrobeniusEquiv F 2 s
  let τ' := (highestWeightSpan (f.toRingHom.comp e) a).toRepresentation
  let := highestWeightSpan_isIrreducible_of_lt_card (f.toRingHom.comp e) a ha
  have he : τ'.character = τ.character := by
    apply character_eq_of_proportional τ' τ (μ.character y / μ.character y ^ (2^s))
    intro x
    have hh := h x y
    rw [mul_pow] at hh
    have hx := highestWeightSpan_character_comp_embedding f e a x
    change τ'.character x = τ.character x ^ (2^s) at hx
    rw [hx]
    apply (mul_right_cancel₀ (pow_ne_zero (2^s) hy))
    calc
      _ = τ.character x * μ.character y := hh
      _ = _ := by field_simp
  intro x
  have hx := highestWeightSpan_character_comp_embedding f e a x
  change τ'.character x = τ.character x ^ (2^s) at hx
  exact hx.symm.trans (congrFun he x)

private theorem small_product_degrees (n s t b c : ℕ)
    (hn : 3 ≤ n) (_hs : 0 < s) (ht : 0 < t) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hnt : n=s*t) (hbudget : s*(b^t*c^t) ≤ 4*(n+1)) :
    s=n ∧ b^t=2 ∧ c^t=2 := by
  have ht1 : t=1 := by
    by_contra hz
    have hp : ∀ t : ℕ, 2 ≤ t → 8*t ≤ 4^t := by
      intro t ht
      induction t,ht using Nat.le_induction with
      | base => decide
      | succ t ht ih => rw [pow_succ]; nlinarith
    have hlo : 8*t ≤ b^t*c^t := (hp t (by omega)).trans (by
      rw [←mul_pow]
      exact Nat.pow_le_pow_left (by nlinarith) _)
    nlinarith
  subst t
  simp only [pow_one,mul_one] at *
  subst n
  constructor
  · rfl
  · have hprod : b*c < 6 := by
      by_contra! hh
      have he := Nat.mul_le_mul_left s hh
      nlinarith
    have hb' : b=2 := by nlinarith
    have hc' : c=2 := by nlinarith
    exact ⟨hb',hc'⟩

private theorem factors_faithful
    {F G V : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V]
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

private theorem weight_pos_of_faithful
  {K F : Type*} [Field K] [Finite K] [Field F]
  (e : K →+* F) (d : ℕ) (π : Representation F SL(2,K) (Fin d → F))
    (hp : Function.Injective π) (k : Fin (Nat.card K))
    (fk : π.Equiv (highestWeightSpan e k.val).toRepresentation) : 0 < k.val := by
  by_contra! hz
  have hz : k.val=0 := Nat.eq_zero_of_le_zero hz
  have hπone (g : SL(2,K)) : π g=1 := by
    apply LinearMap.ext
    intro v
    apply fk.injective
    have hh := LinearMap.congr_fun (fk.isIntertwining' g) v
    change fk (π g v) = (highestWeightSpan e k.val).toRepresentation g (fk v) at hh
    have hzero : ∀ w : (highestWeightSpan e k.val).toSubmodule,
        (highestWeightSpan e k.val).toRepresentation g w=w := by
      have hp (j : ℕ) (hj : j=0) : ∀ w : (highestWeightSpan e j).toSubmodule,
          (highestWeightSpan e j).toRepresentation g w=w := by
        subst j
        exact highestWeightSpan_zero_apply e g
      exact hp _ hz
    exact hh.trans (hzero (fk v))
  have hh := congrArg (fun g : SL(2,K) => g 0 0)
    (hp ((hπone (cubicMatrix K)).trans (hπone 1).symm))
  simp [cubicMatrix] at hh

private theorem weight_character_fixed_of_card
  {K F : Type*} [Field K] [Finite K] [Field F] [CharP F 2] [IsAlgClosed F]
  (e : K →+* F) (n : ℕ) (hK : Nat.card K=2^n) (k : ℕ) (x : SL(2,K)) :
    (highestWeightSpan e k).toRepresentation.character x ^ (2^n) =
      (highestWeightSpan e k).toRepresentation.character x := by
  let z := iterateFrobeniusEquiv F 2 n
  have he : (z : F →+* F).comp e=e := by
    ext x
    change (e x)^(2^n)=e x
    rw [←map_pow,←hK]
    congr 1
    let : Fintype K := Fintype.ofFinite K
    simpa only [Nat.card_eq_fintype_card] using FiniteField.pow_card x
  have hh := highestWeightSpan_character_comp_embedding z e k x
  rw [he] at hh
  exact hh.symm

private theorem degree_pow_of_period
    {K F : Type*} [Field K] [Finite K] [Field F] [CharP F 2]
    (e : K →+* F) (n : ℕ) (hK : Nat.card K=2^n)
    (s t : ℕ) (hs : 0<s) (ht : 0<t) (hnt : n=s*t)
    (d : ℕ) (π : Representation F SL(2,K) (Fin d → F)) (hf : Function.Injective π)
    (a : Fin (Nat.card K)) (f : π.Equiv (highestWeightSpan e a.val).toRepresentation)
    (hper : (Nat.card K-1) ∣ a.val*(2^s-1)) :
    ∃ b : ℕ, 2 ≤ b ∧ d=b^t := by
  obtain ⟨b,hb,hprod,_⟩ := Nat.exists_digit_product_pow_of_period 2 s t a.val
    (by decide) hs ht (weight_pos_of_faithful e d π hf a f)
    (by simpa only [←hnt,←hK] using a.isLt)
    (by simpa only [←hnt,←hK] using hper)
  refine ⟨b,hb,?_⟩
  have hh := f.toLinearEquiv.finrank_eq
  rw [highestWeightSpan_finrank_eq_prod_digits e 2 Nat.prime_two a n hK
    (by simpa only [←hK] using a.isLt)] at hh
  have hh' : d = ∏ i : Fin n, (a.val / 2^(i:ℕ)%2+1) := by
    simpa only [Module.finrank_pi,Fintype.card_fin,Module.finrank_self,mul_one] using hh
  rw [hnt] at hh'
  exact hh'.trans hprod

open FrobeniusTensor
variable {K V : Type*} [Field K] [Finite K] [CharP K 2]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

omit [CharP K 2] in
private theorem square_periods
    (ρ : Representation (ZMod 2) (SL(2,K) × SL(2,K)) V) [ρ.IsIrreducible]
    (e : K →+* Closure ρ) (a b : Fin (Nat.card K)) (n : ℕ) (hK : Nat.card K=2^n)
    (hchar : ∀ g : SL(2,K) × SL(2,K), (absoluteRep ρ).character g =
      (highestWeightSpan e a.val).toRepresentation.character g.1 *
      (highestWeightSpan e b.val).toRepresentation.character g.2) :
    let s := Module.finrank (ZMod 2) (FrobeniusTensor.SchurField ρ)
    s ∣ n ∧ (Nat.card K-1) ∣ a.val*(2^s-1) ∧
      (Nat.card K-1) ∣ b.val*(2^s-1) := by
  let s := Module.finrank (ZMod 2) (FrobeniusTensor.SchurField ρ)
  have hsdvd : s ∣ n := by
    apply (character_pow_iff ρ n).mp
    intro g
    rw [hchar,mul_pow,weight_character_fixed_of_card e n hK,
      weight_character_fixed_of_card e n hK]
  have hfix (x y : SL(2,K)) :
      ((highestWeightSpan e a.val).toRepresentation.character x *
        (highestWeightSpan e b.val).toRepresentation.character y) ^ (2^s) =
      (highestWeightSpan e a.val).toRepresentation.character x *
        (highestWeightSpan e b.val).toRepresentation.character y := by
    simpa only [hchar] using (character_pow_iff ρ s).mpr (dvd_refl s) (x,y)
  have hpa := weight_period_of_character_fixed e a a.isLt s
    (factor_character_fixed e a b a.isLt b.isLt s hfix)
  have hpb := weight_period_of_character_fixed e b b.isLt s
    (factor_character_fixed e b a b.isLt a.isLt s (by
      intro x y
      rw [mul_comm]
      exact hfix y x))
  exact ⟨hsdvd,hpa,hpb⟩

/-- Every faithful irreducible binary square of degree at most 4(n+1), n≥3,
has Schur degree n and two absolute factors of degree two. -/
private theorem small_square_degree_of_embedding
    (ρ : Representation (ZMod 2) (SL(2,K) × SL(2,K)) V)
    [ρ.IsIrreducible] (hf : Function.Injective ρ)
    (e : K →+* Closure ρ)
    (n : ℕ) (hn : 3 ≤ n) (hK : Nat.card K=2^n)
    (hbudget : Module.finrank (ZMod 2) V ≤ 4*(n+1)) :
    Module.finrank (ZMod 2) (FrobeniusTensor.SchurField ρ)=n ∧
    ∃ τ μ : Representation (Closure ρ) SL(2,K) (Fin 2 → Closure ρ),
      τ.IsIrreducible ∧ μ.IsIrreducible ∧
      Nonempty ((absoluteRep ρ).Equiv (externalTensor τ μ)) := by
  let s := Module.finrank (ZMod 2) (FrobeniusTensor.SchurField ρ)
  obtain ⟨d₁,d₂,τ,μ,hτ,hμ,⟨f⟩⟩ :=
    ProductFactors.exists_irreducible_externalTensor_factors (absoluteRep ρ)
  let := hτ
  let := hμ
  have hfaith := factors_faithful (absoluteRep ρ) (absoluteRep_injective ρ hf) τ μ f
  obtain ⟨a,⟨fτ⟩⟩ := exists_highestWeightSpan_equiv e 2 τ
  obtain ⟨b,⟨fμ⟩⟩ := exists_highestWeightSpan_equiv e 2 μ
  have hchar (g : SL(2,K) × SL(2,K)) : (absoluteRep ρ).character g =
      (highestWeightSpan e a.val).toRepresentation.character g.1 *
      (highestWeightSpan e b.val).toRepresentation.character g.2 := by
    rw [Representation.char_iso f,externalTensor_character,
      Representation.char_iso fτ,Representation.char_iso fμ]
  have hspos : 0<s := schurField_finrank_pos ρ
  obtain ⟨hsdvd,hpa,hpb⟩ := square_periods ρ e a b n hK hchar
  obtain ⟨t,hnt⟩ := hsdvd
  have ht : 0<t := by nlinarith
  obtain ⟨b₁,hb₁,dim₁⟩ := degree_pow_of_period e n hK s t hspos ht hnt
    d₁ τ hfaith.1 a fτ hpa
  obtain ⟨b₂,hb₂,dim₂⟩ := degree_pow_of_period e n hK s t hspos ht hnt
    d₂ μ hfaith.2 b fμ hpb
  have hd : Module.finrank (ZMod 2) V = s*(d₁*d₂) := by
    rw [binary_finrank_eq ρ,f.toLinearEquiv.finrank_eq,Module.finrank_tensorProduct]
    simp only [Module.finrank_pi,Fintype.card_fin]
    rfl
  rw [hd,dim₁,dim₂] at hbudget
  obtain ⟨hs,h₁,h₂⟩ := small_product_degrees n s t b₁ b₂ hn hspos ht hb₁ hb₂ hnt hbudget
  have he₁ : d₁=2 := dim₁.trans h₁
  have he₂ : d₂=2 := dim₂.trans h₂
  cases he₁
  cases he₂
  exact ⟨hs,τ,μ,hτ,hμ,⟨f⟩⟩

/-- Every faithful irreducible binary square of degree at most 4(n+1), n≥3,
has Schur degree n and two absolute factors of degree two. -/
theorem small_square_degree
    (ρ : Representation (ZMod 2) (SL(2,K) × SL(2,K)) V)
    [ρ.IsIrreducible] (hf : Function.Injective ρ)
    (n : ℕ) (hn : 3 ≤ n) (hK : Nat.card K=2^n)
    (hbudget : Module.finrank (ZMod 2) V ≤ 4*(n+1)) :
    Module.finrank (ZMod 2) (FrobeniusTensor.SchurField ρ)=n ∧
    ∃ τ μ : Representation (Closure ρ) SL(2,K) (Fin 2 → Closure ρ),
      τ.IsIrreducible ∧ μ.IsIrreducible ∧
      Nonempty ((absoluteRep ρ).Equiv (externalTensor τ μ)) := by
  let : Algebra (ZMod 2) K := ZMod.algebra _ 2
  let : Algebra (ZMod 2) (Closure ρ) := ZMod.algebra _ 2
  exact small_square_degree_of_embedding ρ hf
    (IsAlgClosed.lift (R := ZMod 2) (S := K) (M := Closure ρ)).toRingHom n hn hK hbudget
end Representation.SL2.SmallSquare

namespace Representation.SL2.SmallSquare
open FrobeniusTensor BinaryOffender Subgroup
variable {K E F : Type*} [Field K] [Field E] [Field F]
local instance (f : E ≃+* F) : RingHomInvPair f.toRingHom f.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv f
local instance (f : E ≃+* F) : RingHomInvPair f.symm.toRingHom f.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm f
private def coordinateFieldEquiv (f : E ≃+* F) :
    (Fin 2 → E) ≃ₛₗ[f.toRingHom] (Fin 2 → F) where
  toFun v i := f (v i)
  invFun v i := f.symm (v i)
  left_inv v := by ext i; exact f.symm_apply_apply _
  right_inv v := by ext i; exact f.apply_symm_apply _
  map_add' v w := by ext i; exact map_add f _ _
  map_smul' a v := by ext i; exact map_mul f _ _

private theorem coordinateFieldEquiv_intertwines (f : E ≃+* F)
    (e : K →+* E) (g : SL(2,K)) (v : Fin 2 → E) :
    coordinateFieldEquiv f (BinarySmall.embeddedNatural e g v)=
      BinarySmall.embeddedNatural (f.toRingHom.comp e) g (coordinateFieldEquiv f v) := by
  ext i
  change f (Matrix.mulVec (g.val.map e) v i)=
    Matrix.mulVec (g.val.map (f.toRingHom.comp e)) (fun j => f (v j)) i
  simp only [Matrix.mulVec,dotProduct,map_sum,map_mul,Matrix.map_apply,
    RingHom.comp_apply,RingEquiv.toRingHom_eq_coe,RingEquiv.coe_toRingHom]

private def naturalTensorFieldEquiv [Algebra (ZMod 2) E] [Algebra (ZMod 2) F]
    (f : E ≃+* F) (e₁ e₂ : K →+* E) :
    (restrictScalars (k := ZMod 2) (externalTensor
      (BinarySmall.embeddedNatural e₁) (BinarySmall.embeddedNatural e₂))).Equiv
      (restrictScalars (k := ZMod 2) (externalTensor
        (BinarySmall.embeddedNatural (f.toRingHom.comp e₁))
        (BinarySmall.embeddedNatural (f.toRingHom.comp e₂)))) := by
  let c := TensorProduct.congr (coordinateFieldEquiv f) (coordinateFieldEquiv f)
  let b := LinearEquiv.ofBijective (c.toAddEquiv.toAddMonoidHom.toZModLinearMap 2) c.bijective
  refine Representation.Equiv.mk b (fun g => ?_)
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw
  | tmul v w =>
    change c ((BinarySmall.embeddedNatural e₁ g.1 v) ⊗ₜ[E]
      (BinarySmall.embeddedNatural e₂ g.2 w)) =
      TensorProduct.map (BinarySmall.embeddedNatural (f.toRingHom.comp e₁) g.1)
        (BinarySmall.embeddedNatural (f.toRingHom.comp e₂) g.2) (c (v ⊗ₜ[E] w))
    simp only [c,TensorProduct.congr_tmul,TensorProduct.map_tmul,
      coordinateFieldEquiv_intertwines]


variable [Finite K] [CharP K 2]
local instance : Algebra (ZMod 2) K := ZMod.algebra _ 2
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The whole small binary square is a natural tensor, with its field twist
and original acting-group marking retained. -/
theorem small_square_natural_tensor
    (ρ : Representation (ZMod 2) (SL(2,K) × SL(2,K)) V)
    [ρ.IsIrreducible] (hf : Function.Injective ρ)
    (n : ℕ) (hn : 3 ≤ n) (hK : Nat.card K=2^n)
    (hbudget : Module.finrank (ZMod 2) V ≤ 4*(n+1)) :
    ∃ α : MulAut SL(2,K), Nonempty (ρ.Equiv (restrictScalars (k := ZMod 2)
      (externalTensor ((BinarySmall.embeddedNatural (RingHom.id K)).comp α.symm.toMonoidHom)
        (BinarySmall.embeddedNatural (RingHom.id K))))) := by
  obtain ⟨hs,τ,μ,hτ,hμ,⟨f⟩⟩ := small_square_degree ρ hf n hn hK hbudget
  let E := FrobeniusTensor.SchurField ρ
  let F := Closure ρ
  let : Algebra (ZMod 2) F := ZMod.algebra _ 2
  let e : K →+* F := (IsAlgClosed.lift (R := ZMod 2) (S := K) (M := F)).toRingHom
  let := hτ
  let := hμ
  obtain ⟨i,_,⟨φ⟩⟩ := EvenSquare.absolute_degree_two_natural τ n hK e
  obtain ⟨j,_,⟨ψ⟩⟩ := EvenSquare.absolute_degree_two_natural μ n hK e
  let e₁ := (iterateFrobenius F 2 i).comp e
  let e₂ := (iterateFrobenius F 2 j).comp e
  have hc : Nat.card K=Nat.card E := by
    let : Module.Finite (ZMod 2) E := Module.Finite.of_finite
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := E),Nat.card_zmod,hs,hK]
  obtain ⟨c₁,hc₁⟩ := BinarySmall.exists_fieldEquiv_comp_eq_of_card_eq e₁ (algebraMap E F) hc
  obtain ⟨c₂,hc₂⟩ := BinarySmall.exists_fieldEquiv_comp_eq_of_card_eq e₂ (algebraMap E F) hc
  let τ₁ := BinarySmall.embeddedNatural c₁.toRingHom
  let τ₂ := BinarySmall.embeddedNatural c₂.toRingHom
  let π := externalTensor τ₁ τ₂
  have q₁ := BinarySmall.embeddedNaturalBaseChange (F := F) c₁.toRingHom
  have q₂ := BinarySmall.embeddedNaturalBaseChange (F := F) c₂.toRingHom
  rw [hc₁] at q₁
  rw [hc₂] at q₂
  let q := (externalTensorBaseChange τ₁ τ₂).trans (externalTensorEquiv q₁ q₂)
  obtain ⟨d⟩ := repEquiv_of_extendScalars ρ.endFieldRep π
    ⟨RepEquiv.ofRepresentationEquiv ((f.trans (externalTensorEquiv φ ψ)).trans q.symm)⟩
  let : SMul (ZMod 2) E := (inferInstance : Algebra (ZMod 2) E).toSMul
  let : Module (ZMod 2) E := Algebra.toModule
  let badd := ρ.asModuleEquiv.symm.toAddEquiv.trans d.toLinearEquiv.toAddEquiv
  let b : V ≃ₗ[ZMod 2] ((Fin 2 → E) ⊗[E] (Fin 2 → E)) :=
    LinearEquiv.ofBijective (badd.toAddMonoidHom.toZModLinearMap 2) badd.bijective
  have hb : ρ.Equiv (restrictScalars (k := ZMod 2) π) := by
    refine Representation.Equiv.mk b (fun g => ?_)
    apply LinearMap.ext
    intro v
    exact d.isIntertwining g (ρ.asModuleEquiv.symm v)
  have hc' : c₂.symm.toRingHom.comp c₂.toRingHom=RingHom.id K := by
    ext x
    exact c₂.symm_apply_apply x
  have hfield := naturalTensorFieldEquiv c₂.symm c₁.toRingHom c₂.toRingHom
  rw [hc'] at hfield
  let δ := c₁.trans c₂.symm
  let α := Theory.PSL2.sl2FieldAut δ.symm
  refine ⟨α,⟨?_⟩⟩
  have he : BinarySmall.embeddedNatural (c₂.symm.toRingHom.comp c₁.toRingHom) =
      (BinarySmall.embeddedNatural (RingHom.id K)).comp α.symm.toMonoidHom := by
    ext g v k
    rfl
  exact (hb.trans hfield).trans (by rw [he]; exact Representation.Equiv.refl _)
end Representation.SL2.SmallSquare
