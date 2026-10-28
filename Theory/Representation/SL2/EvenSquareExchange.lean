module
public import Theory.Representation.ExchangedProductDegree
public import Theory.Representation.Quotient
public import Theory.Representation.BinaryOffender.SchurNormalizerAction
public import Theory.Representation.SL2.PrimeFieldParameters.Unsigned
public import Theory.GroupAction.InnerInvolutionGeometry
public import Theory.Representation.SL2.BinaryNaturalTripleRecognition.NaturalComparison
public import Theory.Representation.QuadraticFourGroup.TensorClassification.Descent
public import Theory.Representation.SL2.BinaryNaturalTripleRecognition.FieldIdentification

/-!
# Small exchanges on a binary SL₂ square

For an involution exchanging the two factors and fixing the actual Schur
field, the absolute representation is a symmetric tensor. Its diagonal
character is the square of its factor character. Frobenius injectivity then
identifies the factor's period with the original Schur period. Highest-weight
digit periodicity and the exact tensor-exchange displacement force absolute
factor degree two when the binary displacement is at most 2(n+1), n≥3.

The pure-power polynomial intertwiner recognizes the natural factor.
Compatible finite-field identification and Noether--Deuring descent give a
whole-space binary natural tensor. Relabelling one component absorbs an
arbitrary exchange twist while retaining the actual normalizer element.
The Chapter D and original Chapter 10 seed consumers use these intertwiners;
Schur linearity is tested there, not assumed of every source actor.

Source: Aschbacher--Smith D.3.7, printed pp.197--198.
-/


public noncomputable section
open scoped MatrixGroups TensorProduct MonoidAlgebra
open Module Representation
open Representation.QuadraticFourGroup.TensorClassification
namespace Representation.SL2.EvenSquare

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

private theorem choose_pow_ge_three_mul (b t : ℕ) (hb : 2 ≤ b) (ht : 2 ≤ t) :
    3*t ≤ (b^t).choose 2 := by
  have hc : ∀ d : ℕ, 2*d.choose 2+d=d*d := by
    intro d
    induction d with
    | zero => simp
    | succ d ih => rw [Nat.choose_succ_succ,Nat.choose_one_right]; nlinarith
  have hpow : 2*t ≤ 2^t := by
    induction t,ht using Nat.le_induction with
    | base => decide
    | succ t ht ih => rw [pow_succ]; nlinarith
  have hd := hpow.trans (Nat.pow_le_pow_left hb t)
  have hchoose := hc (b^t)
  nlinarith

private theorem degree_two_of_exchange_budget (n s t b : ℕ)
    (hn : 3 ≤ n) (_hs : 0 < s) (ht : 0 < t) (hb : 2 ≤ b)
    (hns : n=s*t) (hbudget : s*(b^t).choose 2 ≤ 2*(n+1)) :
    b^t=2 ∧ s=n := by
  have ht1 : t=1 := by
    by_contra h
    have hh := choose_pow_ge_three_mul b t hb (by omega)
    have h := Nat.mul_le_mul_left s hh
    nlinarith
  subst t
  simp only [pow_one,mul_one] at hbudget hns ⊢
  subst n
  have hb2 : b=2 := by
    by_contra h
    have hh : 3 ≤ b.choose 2 := by
      simpa using Nat.choose_le_choose 2 (show 3 ≤ b by omega)
    nlinarith
  exact ⟨hb2,rfl⟩

open FrobeniusTensor BinaryOffender Subgroup
variable {K V : Type*} [Field K] [Finite K] [CharP K 2]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- The actual symmetric tensor in a small Schur-linear exchange has absolute
factor degree two and Schur degree equal to the defining-field degree. -/
theorem schur_linear_exchange_degree
    (ρ : Representation (ZMod 2) (SL(2,K) × SL(2,K)) V)
    [ρ.IsIrreducible] (hf : Function.Injective ρ)
    (n : ℕ) (hn : 3 ≤ n) (hK : Nat.card K=2^n)
    (a : linearNormalizer ρ) (ha : a^2=1)
    (hlin : SchurNormalizer.IsSchurLinear ρ a)
    (hex : ∀ g v, normalizerRepresentation ρ a (ρ g v) =
      ρ (g.2,g.1) (normalizerRepresentation ρ a v))
    (hbudget : Module.finrank (ZMod 2) (a.val.val-1).range ≤ 2*(n+1)) :
    Module.finrank (ZMod 2) (SchurField ρ)=n ∧ Module.finrank (ZMod 2) V=4*n ∧
    ∃ τ : Representation (Closure ρ) SL(2,K) (Fin 2 → Closure ρ),
      τ.IsIrreducible ∧ Nonempty ((absoluteRep ρ).Equiv (externalTensor τ τ)) := by
  let E := SchurField ρ
  let F := Closure ρ
  let s := Module.finrank (ZMod 2) E
  let R := SchurNormalizer.absoluteActor ρ F a hlin
  have hR2 : R*R=1 := by
    simpa only [pow_two] using SchurNormalizer.absoluteActor_square ρ F a hlin ha
  have hR (g : SL(2,K) × SL(2,K)) (v) :
      R (absoluteRep ρ g v)=absoluteRep ρ (g.2,g.1) (R v) := by
    have hh : SchurNormalizer.schurActor ρ a hlin * ρ.endFieldRep g =
        ρ.endFieldRep (g.2,g.1) * SchurNormalizer.schurActor ρ a hlin := by
      ext w
      apply ρ.asModuleEquiv.injective
      exact hex g (ρ.asModuleEquiv w)
    have h := congrArg (fun f : Module.End E ρ.asModule => f.baseChange F) hh
    rw [LinearMap.baseChange_mul,LinearMap.baseChange_mul] at h
    exact LinearMap.congr_fun h v
  obtain ⟨d,τ,hτ,⟨f⟩,hr⟩ := ExchangedProduct.exists_symmetric_tensor (absoluteRep ρ) R hR2 hR
  let := hτ
  let : Algebra (ZMod 2) K := ZMod.algebra _ 2
  let : Algebra (ZMod 2) F := ZMod.algebra _ 2
  let e : K →+* F := (IsAlgClosed.lift (R := ZMod 2) (S := K) (M := F)).toRingHom
  obtain ⟨m,⟨fτ⟩⟩ := exists_highestWeightSpan_equiv e 2 τ
  have hdim : d = ∏ i : Fin n, (m.val/2^(i:ℕ)%2+1) := by
    have hh := fτ.toLinearEquiv.finrank_eq
    rw [highestWeightSpan_finrank_eq_prod_digits e 2 Nat.prime_two m n hK (by
      simpa only [←hK] using m.isLt)] at hh
    change Module.finrank F (Fin d → F) = _ at hh
    simpa only [Module.finrank_pi,Fintype.card_fin,Module.finrank_self,mul_one] using hh
  have hchar (g : SL(2,K) × SL(2,K)) : (absoluteRep ρ).character g =
      (highestWeightSpan e m.val).toRepresentation.character g.1 *
      (highestWeightSpan e m.val).toRepresentation.character g.2 := by
    rw [Representation.char_iso f,externalTensor_character,
      Representation.char_iso fτ]
  have hspos : 0<s := schurField_finrank_pos ρ
  have hsdvd : s ∣ n := by
    apply (character_pow_iff ρ n).mp
    intro g
    rw [hchar,mul_pow]
    have hfix (x : SL(2,K)) :
        (highestWeightSpan e m.val).toRepresentation.character x ^ (2^n) =
          (highestWeightSpan e m.val).toRepresentation.character x := by
      let σ := iterateFrobeniusEquiv F 2 n
      have he : (σ : F →+* F).comp e=e := by
        ext x
        change (e x)^(2^n)=e x
        rw [←map_pow,←hK]
        congr 1
        let : Fintype K := Fintype.ofFinite K
        simpa only [Nat.card_eq_fintype_card] using FiniteField.pow_card x
      have hh := highestWeightSpan_character_comp_embedding σ e m.val x
      rw [he] at hh
      exact hh.symm
    rw [hfix,hfix]
  have hfix (x : SL(2,K)) :
      (highestWeightSpan e m.val).toRepresentation.character x ^ (2^s) =
        (highestWeightSpan e m.val).toRepresentation.character x := by
    have hh := (character_pow_iff ρ s).mpr (dvd_refl s) (x,x)
    rw [hchar,mul_pow] at hh
    exact (frobenius F 2).injective (by simpa only [frobenius_def,pow_two] using hh)
  have hper := weight_period_of_character_fixed e m m.isLt s hfix
  have hmpos : 0<m.val := by
    by_contra! hz
    have hz : m.val=0 := Nat.eq_zero_of_le_zero hz
    have hτone (g : SL(2,K)) : τ g=1 := by
      apply LinearMap.ext
      intro v
      apply fτ.injective
      have hh := LinearMap.congr_fun (fτ.isIntertwining' g) v
      change fτ (τ g v) = (highestWeightSpan e m.val).toRepresentation g (fτ v) at hh
      have hzero : ∀ w : (highestWeightSpan e m.val).toSubmodule,
          (highestWeightSpan e m.val).toRepresentation g w=w := by
        have hp (k : ℕ) (hk : k=0) : ∀ w : (highestWeightSpan e k).toSubmodule,
            (highestWeightSpan e k).toRepresentation g w=w := by
          subst k
          exact highestWeightSpan_zero_apply e g
        exact hp _ hz
      exact hh.trans (hzero (fτ v))
    have hh : absoluteRep ρ (cubicMatrix K,1)=absoluteRep ρ 1 := by
      apply LinearMap.ext
      intro v
      apply f.injective
      have he (g : SL(2,K) × SL(2,K)) : f (absoluteRep ρ g v)=externalTensor τ τ g (f v) :=
        LinearMap.congr_fun (f.isIntertwining' g) v
      change f (absoluteRep ρ (cubicMatrix K,1) v)=f (absoluteRep ρ 1 v)
      rw [he,he,externalTensor_apply,externalTensor_apply]
      simp only [hτone]
    have hh := congrArg Prod.fst (absoluteRep_injective ρ hf hh)
    have hh := congrArg (fun g : SL(2,K) => g 0 0) hh
    simp [cubicMatrix] at hh
  obtain ⟨t,hnt⟩ := hsdvd
  have ht : 0<t := by nlinarith
  obtain ⟨b,hb,hprod,_⟩ := Nat.exists_digit_product_pow_of_period 2 s t m.val
    (by decide) hspos ht hmpos (by simpa only [←hnt,←hK] using m.isLt)
    (by simpa only [←hnt,←hK] using hper)
  have hd : d=b^t := by rw [hnt] at hdim; exact hdim.trans hprod
  have hbd : s*d.choose 2 ≤ 2*(n+1) := by
    have hh := SchurNormalizer.binary_range_finrank ρ F a hlin
    rw [hr] at hh
    exact hh ▸ hbudget
  obtain ⟨hd2,hs⟩ := degree_two_of_exchange_budget n s t b hn hspos ht hb hnt (hd ▸ hbd)
  have hd2 : d=2 := hd.trans hd2
  cases hd2
  refine ⟨hs,?_,τ,hτ,⟨f⟩⟩
  rw [binary_finrank_eq ρ,f.toLinearEquiv.finrank_eq,Module.finrank_tensorProduct]
  simp only [Module.finrank_pi,Fintype.card_fin]
  change s*(2*2)=4*n
  omega
end Representation.SL2.EvenSquare

namespace Representation.SL2.EvenSquare
private def digitProd (m n : ℕ) : ℕ := ∏ i : Fin m, (n/2^(i:ℕ)%2+1)
private theorem digitProd_succ (m n : ℕ) :
    digitProd (m+1) n=(n%2+1)*digitProd m (n/2) := by
  rw [digitProd,Fin.prod_univ_succ]
  simp only [Fin.val_zero,pow_zero,Nat.div_one]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simp only [Fin.val_succ,pow_succ,Nat.div_div_eq_div_mul,mul_comm]
private theorem eq_zero_of_prod_one (m n : ℕ) (hn : n<2^m)
    (h : digitProd m n=1) : n=0 := by
  induction m generalizing n with
  | zero => simpa using hn
  | succ m ih =>
    rw [digitProd_succ] at h
    have hp : 0<digitProd m (n/2) := Finset.prod_pos (fun _ _ => Nat.zero_lt_succ _)
    have hle := Nat.le_mul_of_pos_left (digitProd m (n/2)) (Nat.zero_lt_succ (n%2))
    rw [h] at hle
    have hq : digitProd m (n/2)=1 := by omega
    have hr : n%2=0 := by rw [hq] at h; omega
    have hn' : n/2<2^m := Nat.div_lt_of_lt_mul (by simpa [pow_succ,mul_comm] using hn)
    have hz := ih (n/2) hn' hq
    omega
private theorem pow_of_prod_two (m n : ℕ) (hn : n<2^m)
    (h : digitProd m n=2) : ∃ j<m, n=2^j := by
  induction m generalizing n with
  | zero => simp [digitProd] at h
  | succ m ih =>
    rw [digitProd_succ] at h
    have hn' : n/2<2^m := Nat.div_lt_of_lt_mul (by simpa [pow_succ,mul_comm] using hn)
    by_cases hr : n%2=0
    · have hq : digitProd m (n/2)=2 := by simpa [hr] using h
      obtain ⟨j,hj,he⟩ := ih (n/2) hn' hq
      refine ⟨j+1,by omega,?_⟩
      rw [pow_succ]
      omega
    · have hr1 : n%2=1 := by omega
      have hq : digitProd m (n/2)=1 := by rw [hr1] at h; omega
      have hz := eq_zero_of_prod_one m (n/2) hn' hq
      exact ⟨0,by omega,by simp; omega⟩

variable {K F : Type*} [Field K] [Finite K] [CharP K 2]
  [Field F] [CharP F 2] [IsAlgClosed F]

/-- An actual two-dimensional absolute SL₂ representation is a Frobenius
natural module, with its intertwiner in the given coefficient field. -/
theorem absolute_degree_two_natural
    (τ : Representation F SL(2,K) (Fin 2 → F)) [τ.IsIrreducible]
    (n : ℕ) (hK : Nat.card K=2^n) (e : K →+* F) :
    ∃ i<n, Nonempty (τ.Equiv (BinarySmall.embeddedNatural
      ((iterateFrobenius F 2 i).comp e))) := by
  obtain ⟨m,⟨f⟩⟩ := exists_highestWeightSpan_equiv e 2 τ
  have hd := f.toLinearEquiv.finrank_eq
  rw [highestWeightSpan_finrank_eq_prod_digits e 2 Nat.prime_two m n hK
    (by simpa only [←hK] using m.isLt)] at hd
  have hprod : digitProd n m.val=2 := by
    simpa only [digitProd,Module.finrank_pi,Fintype.card_fin,Module.finrank_self,mul_one] using hd.symm
  obtain ⟨i,hi,hm⟩ := pow_of_prod_two n m.val (by simpa only [←hK] using m.isLt) hprod
  rw [hm] at f
  exact ⟨i,hi,⟨f.trans (BinarySmall.highestWeightPurePowerEquiv e i)⟩⟩
end Representation.SL2.EvenSquare

namespace Representation.SL2.EvenSquare
open FrobeniusTensor BinaryOffender
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
    (f : E ≃+* F) (e : K →+* E) :
    (restrictScalars (k := ZMod 2) (externalTensor
      (BinarySmall.embeddedNatural e) (BinarySmall.embeddedNatural e))).Equiv
      (restrictScalars (k := ZMod 2) (externalTensor
        (BinarySmall.embeddedNatural (f.toRingHom.comp e))
        (BinarySmall.embeddedNatural (f.toRingHom.comp e)))) := by
  let c := TensorProduct.congr (coordinateFieldEquiv f) (coordinateFieldEquiv f)
  let b := LinearEquiv.ofBijective (c.toAddEquiv.toAddMonoidHom.toZModLinearMap 2) c.bijective
  refine Representation.Equiv.mk b (fun g => ?_)
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw
  | tmul v w =>
    change c ((BinarySmall.embeddedNatural e g.1 v) ⊗ₜ[E]
      (BinarySmall.embeddedNatural e g.2 w)) =
      TensorProduct.map (BinarySmall.embeddedNatural (f.toRingHom.comp e) g.1)
        (BinarySmall.embeddedNatural (f.toRingHom.comp e) g.2) (c (v ⊗ₜ[E] w))
    simp only [c,TensorProduct.congr_tmul,TensorProduct.map_tmul,
      coordinateFieldEquiv_intertwines]

variable [Finite K] [CharP K 2]
local instance : Algebra (ZMod 2) K := ZMod.algebra _ 2
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- A small Schur-linear exchanging involution constructs the actual binary
natural tensor, by descent through its original endomorphism field. -/
theorem schur_linear_exchange_natural
    (ρ : Representation (ZMod 2) (SL(2,K) × SL(2,K)) V)
    [ρ.IsIrreducible] (hf : Function.Injective ρ)
    (n : ℕ) (hn : 3 ≤ n) (hK : Nat.card K=2^n)
    (a : linearNormalizer ρ) (ha : a^2=1)
    (hlin : SchurNormalizer.IsSchurLinear ρ a)
    (hex : ∀ g v, normalizerRepresentation ρ a (ρ g v) =
      ρ (g.2,g.1) (normalizerRepresentation ρ a v))
    (hbudget : Module.finrank (ZMod 2) (a.val.val-1).range ≤ 2*(n+1)) :
    Nonempty (ρ.Equiv (restrictScalars (k := ZMod 2) (externalTensor
      (BinarySmall.embeddedNatural (RingHom.id K))
      (BinarySmall.embeddedNatural (RingHom.id K))))) := by
  obtain ⟨hs,_,τ,hτ,⟨f⟩⟩ := schur_linear_exchange_degree ρ hf n hn hK a ha hlin hex hbudget
  let E := FrobeniusTensor.SchurField ρ
  let F := Closure ρ
  let : Algebra (ZMod 2) F := ZMod.algebra _ 2
  let e : K →+* F := (IsAlgClosed.lift (R := ZMod 2) (S := K) (M := F)).toRingHom
  let := hτ
  obtain ⟨i,_,⟨φ⟩⟩ := absolute_degree_two_natural τ n hK e
  let e' := (iterateFrobenius F 2 i).comp e
  have hc : Nat.card K=Nat.card E := by
    let : Module.Finite (ZMod 2) E := Module.Finite.of_finite
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := E),Nat.card_zmod,hs,hK]
  obtain ⟨c,hc⟩ := BinarySmall.exists_fieldEquiv_comp_eq_of_card_eq e' (algebraMap E F) hc
  let μ := BinarySmall.embeddedNatural c.toRingHom
  let π := externalTensor μ μ
  have q := BinarySmall.embeddedNaturalBaseChange (F := F) c.toRingHom
  rw [hc] at q
  let q₂ := (externalTensorBaseChange μ μ).trans (externalTensorEquiv q q)
  obtain ⟨d⟩ := repEquiv_of_extendScalars ρ.endFieldRep π
    ⟨RepEquiv.ofRepresentationEquiv ((f.trans (externalTensorEquiv φ φ)).trans q₂.symm)⟩
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
  have hc' : c.symm.toRingHom.comp c.toRingHom=RingHom.id K := by
    ext x
    exact c.symm_apply_apply x
  have hfield := naturalTensorFieldEquiv c.symm c.toRingHom
  rw [hc'] at hfield
  exact ⟨hb.trans hfield⟩
end Representation.SL2.EvenSquare

namespace Representation.SL2.EvenSquare
open FrobeniusTensor BinaryOffender Subgroup
variable {K V : Type*} [Field K] [Finite K] [CharP K 2]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
local instance : Algebra (ZMod 2) K := ZMod.algebra _ 2

/-- Absorbing a genuine exchange twist preserves Schur linearity and gives
natural tensor coordinates on the original representation. -/
theorem twisted_schur_linear_exchange_natural
    (ρ : Representation (ZMod 2) (SL(2,K) × SL(2,K)) V)
    [ρ.IsIrreducible] (hf : Function.Injective ρ)
    (n : ℕ) (hn : 3 ≤ n) (hK : Nat.card K=2^n)
    (a : linearNormalizer ρ) (ha : a^2=1)
    (hlin : SchurNormalizer.IsSchurLinear ρ a) (α : MulAut SL(2,K))
    (hex : ∀ g v, normalizerRepresentation ρ a (ρ g v) =
      ρ (α g.2,α.symm g.1) (normalizerRepresentation ρ a v))
    (hbudget : Module.finrank (ZMod 2) (a.val.val-1).range ≤ 2*(n+1)) :
    Nonempty (ρ.Equiv (restrictScalars (k := ZMod 2) (externalTensor
      ((BinarySmall.embeddedNatural (RingHom.id K)).comp α.symm.toMonoidHom)
      (BinarySmall.embeddedNatural (RingHom.id K))))) := by
  let δ := α.prodCongr (MulEquiv.refl SL(2,K))
  let σ : Representation (ZMod 2) (SL(2,K) × SL(2,K)) V := ρ.comp δ.toMonoidHom
  let : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff δ.toMonoidHom δ.surjective ρ).mpr inferInstance
  have himage : actionImage σ=actionImage ρ := by
    ext x
    constructor
    · rintro ⟨g,rfl⟩
      exact ⟨δ g,Units.ext rfl⟩
    · rintro ⟨g,rfl⟩
      obtain ⟨g,rfl⟩ := δ.surjective g
      exact ⟨g,Units.ext rfl⟩
  have hn : linearNormalizer ρ ≤ linearNormalizer σ := by
    unfold linearNormalizer
    rw [himage]
  let a' := inclusion hn a
  have ha' : a'^2=1 := by
    change (inclusion hn a)^2=1
    rw [←map_pow,ha,map_one]
  have hlin' : SchurNormalizer.IsSchurLinear σ a' := by
    intro f v
    let f' : IntertwiningMap ρ ρ := {
      toLinearMap := f.toLinearMap
      isIntertwining' g := by
        have hh := f.isIntertwining' (δ.symm g)
        change f.toLinearMap * ρ (δ (δ.symm g))=ρ (δ (δ.symm g))*f.toLinearMap at hh
        change f.toLinearMap * ρ g=ρ g*f.toLinearMap
        simpa only [δ.apply_symm_apply] using hh }
    exact hlin f' v
  have hex' : ∀ g v, normalizerRepresentation σ a' (σ g v)=
      σ (g.2,g.1) (normalizerRepresentation σ a' v) := by
    rintro ⟨x,y⟩ v
    have hh := hex (α x,y) v
    change normalizerRepresentation ρ a (ρ (α x,y) v)=
      ρ (α y,x) (normalizerRepresentation ρ a v)
    simpa only [α.symm_apply_apply] using hh
  obtain ⟨f⟩ := schur_linear_exchange_natural σ (hf.comp δ.injective)
    n (by assumption) hK a' ha' hlin' hex' hbudget
  refine ⟨Representation.Equiv.mk f.toLinearEquiv ?_⟩
  intro g
  apply LinearMap.ext
  intro v
  have hh := LinearMap.congr_fun (f.isIntertwining' (δ.symm g)) v
  change f (ρ (δ (δ.symm g)) v)=_ at hh
  rw [δ.apply_symm_apply] at hh
  change f (ρ g v)= (TensorProduct.map
    (BinarySmall.embeddedNatural (RingHom.id K) (α.symm g.1))
    (BinarySmall.embeddedNatural (RingHom.id K) g.2)) (f v)
  change f (ρ g v)= (TensorProduct.map
    (BinarySmall.embeddedNatural (RingHom.id K) (δ.symm g).1)
    (BinarySmall.embeddedNatural (RingHom.id K) (δ.symm g).2)) (f v) at hh
  have hδ : δ.symm g=(α.symm g.1,g.2) := by
    apply δ.injective
    rw [δ.apply_symm_apply]
    exact Prod.ext (α.apply_symm_apply g.1).symm rfl
  rw [hδ] at hh
  exact hh
end Representation.SL2.EvenSquare
