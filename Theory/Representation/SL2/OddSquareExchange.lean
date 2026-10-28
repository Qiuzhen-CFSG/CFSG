module
public import Theory.GroupAction.InnerInvolutionGeometry
public import Theory.Representation.ExchangedProductDegree
public import Theory.Representation.AbelianFrobeniusDegree
public import Theory.SpecificGroups.SL2.ProjectiveBorelFrobenius
public import Theory.SpecificGroups.PSL2.PrimeFieldTwoRank
public import Theory.Representation.BinaryOffender.SquareNormalizerActors

/-!
# Excluding exchanges on odd prime-field PSL₂ squares

The actual projective Borel gives degree at least `(p-1)/2` in characteristic
two. For p at least eleven, an irreducible faithful square therefore has
binary degree at least twenty-five and every exchanging involution moves at
least ten dimensions. The elementary actor containing it has rank at most
three, by the actual automorphism group of PSL₂(p). Its ratio is thus above two.

Changing the component marking absorbs any twist of the exchange. Consequently
every small elementary actor preserves each original factor image. Outer
diagonal automorphisms of the individual factors remain allowed.

The original Chapter10 seed application uses the literal quotient marking.
Source: Aschbacher--Smith D.3.7, printed pp.197--198.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace Representation.SL2
open Matrix.ProjectiveSpecialLinearGroup
variable {p : ℕ} [Fact p.Prime]

/-- The projective Borel degree bound over any characteristic-two field. -/
theorem odd_prime_faithful_degree
    {F V : Type*} [Field F] [CharP F 2]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (hp : 3 < p) (ρ : Representation F PSL(2,ZMod p) V)
    (hf : Function.Injective ρ) : (p-1)/2 ≤ Module.finrank F V := by
  have ho : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have horder : (Nat.card (OddBorel.kernel (ZMod p)) : F) ≠ 0 := by
    rw [OddBorel.card_kernel,Nat.card_eq_fintype_card,ZMod.card]
    intro hz
    exact ho.not_two_dvd_nat ((CharP.cast_eq_zero_iff F 2 p).mp hz)
  have hb := card_le_finrank_of_fixedPointFree_normalizer_of_field ρ
    (OddBorel.kernel (ZMod p)) (OddBorel.complement (ZMod p)) hf horder
    (OddBorel.complement_normalizes _) (OddBorel.fixedPointFree _)
  rw [OddBorel.card_complement,Nat.card_eq_fintype_card,ZMod.card] at hb
  have hd : 2 ∣ p-1 := by obtain ⟨n,hn⟩ := ho; exact ⟨n,by omega⟩
  rwa [Nat.gcd_eq_right_iff_dvd.mpr hd] at hb

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The original binary square has degree at least twenty-five for p ≥ 11. -/
theorem odd_prime_square_degree
    (hp : 11 ≤ p)
    (ρ : Representation (ZMod 2) (PSL(2,ZMod p) × PSL(2,ZMod p)) V)
    (hi : ρ.IsIrreducible) (hf : Function.Injective ρ) :
    25 ≤ Module.finrank (ZMod 2) V := by
  let := hi
  apply ExchangedProduct.binary_square_finrank_ge_of_factor_degree ρ hf 5
  intro d τ hτ
  have hd := odd_prime_faithful_degree (by omega : 3 < p) τ hτ
  simp only [Module.finrank_pi,Fintype.card_fin] at hd
  omega

/-- A genuine exchange moves at least ten binary dimensions, without any
assumption on its action on the Schur field. -/
theorem odd_prime_square_exchange_displacement
    (hp : 11 ≤ p)
    (ρ : Representation (ZMod 2) (PSL(2,ZMod p) × PSL(2,ZMod p)) V)
    (hi : ρ.IsIrreducible) (hf : Function.Injective ρ)
    (T : Module.End (ZMod 2) V) (h2 : T*T=1)
    (hT : ∀ g v, T (ρ g v) = ρ (g.2,g.1) (T v)) :
    10 ≤ Module.finrank (ZMod 2) (T-1).range := by
  let := hi
  apply ExchangedProduct.binary_exchange_displacement_ge_of_factor_degree ρ hf 5
  · intro d τ hτ
    have hd := odd_prime_faithful_degree (by omega : 3 < p) τ hτ
    simp only [Module.finrank_pi,Fintype.card_fin] at hd
    omega
  · exact h2
  · exact hT

variable [IsQuasisimple PSL(2,ZMod p)]

/-- A small elementary actor cannot contain a genuine factor exchange. -/
theorem odd_prime_square_exchanged_actor_strict_bound
    (hp : 11 ≤ p)
    (ρ : Representation (ZMod 2) (PSL(2,ZMod p) × PSL(2,ZMod p)) V)
    (hi : ρ.IsIrreducible) (hf : Function.Injective ρ)
    (A : Subgroup (linearNormalizer ρ)) [IsElementaryAbelian 2 A]
    (a : linearNormalizer ρ) (ha : a ∈ A)
    (hswap : ∀ g v, normalizerRepresentation ρ a (ρ g v) =
      ρ (g.2,g.1) (normalizerRepresentation ρ a v)) :
    2 * rank A < fixedCodim (normalizerRepresentation ρ) A := by
  let : IsSimpleGroup PSL(2,ZMod p) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by simpa using (show 4 ≤ p by omega))
  have hr := square_exchange_rank_le center_eq_bot_of_simple_perfect ρ hi hf A a ha hswap
  have hrp := Theory.PSL2.primeField_automorphism_two_rank (by omega : 3 < p)
  have h2 : normalizerRepresentation ρ a * normalizerRepresentation ρ a = 1 := by
    have he := congrArg (normalizerRepresentation ρ)
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha)
    simpa only [pow_two,map_mul,map_one] using he
  have hd := odd_prime_square_exchange_displacement hp ρ hi hf
    (normalizerRepresentation ρ a) h2 hswap
  change 10 ≤ Module.finrank (ZMod 2) (normalizerRepresentation ρ a - LinearMap.id).range at hd
  rw [←fixedCodim_zpowers_eq_displacement_rank] at hd
  have hm := Submodule.finrank_mono (show fixedSpace (normalizerRepresentation ρ) A ≤
      fixedSpace (normalizerRepresentation ρ) (zpowers a) from
        fun v hv b => hv ⟨b,(zpowers_le.mpr ha) b.property⟩)
  have h1 := fixedCodim_add_finrank (normalizerRepresentation ρ) (zpowers a)
  have h2 := fixedCodim_add_finrank (normalizerRepresentation ρ) A
  omega

/-- Changing the factor marking absorbs every automorphism twist of an exchange. -/
theorem odd_prime_square_twisted_exchange_strict_bound
    (hp : 11 ≤ p)
    (ρ : Representation (ZMod 2) (PSL(2,ZMod p) × PSL(2,ZMod p)) V)
    (hi : ρ.IsIrreducible) (hf : Function.Injective ρ)
    (A : Subgroup (linearNormalizer ρ)) [IsElementaryAbelian 2 A]
    (a : linearNormalizer ρ) (ha : a ∈ A) (α : MulAut PSL(2,ZMod p))
    (hswap : ∀ g v, normalizerRepresentation ρ a (ρ g v) =
      ρ (α g.2,α.symm g.1) (normalizerRepresentation ρ a v)) :
    2 * rank A < fixedCodim (normalizerRepresentation ρ) A := by
  let δ := α.prodCongr (MulEquiv.refl PSL(2,ZMod p))
  let σ : Representation (ZMod 2) (PSL(2,ZMod p) × PSL(2,ZMod p)) V :=
    ρ.comp δ.toMonoidHom
  have himage : actionImage σ = actionImage ρ := by
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
  let j := inclusion hn
  have hj : Function.Injective j := inclusion_injective hn
  let C := A.map j
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.map j
  have hiσ : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff δ.toMonoidHom δ.surjective ρ).mpr hi
  have hfσ : Function.Injective σ := hf.comp δ.injective
  have hs : ∀ g v, normalizerRepresentation σ (j a) (σ g v) =
      σ (g.2,g.1) (normalizerRepresentation σ (j a) v) := by
    rintro ⟨x,y⟩ v
    have hh := hswap (α x,y) v
    change normalizerRepresentation ρ a (ρ (α x,y) v) =
      ρ (α y,x) (normalizerRepresentation ρ a v)
    simpa only [MulEquiv.symm_apply_apply] using hh
  have hb := odd_prime_square_exchanged_actor_strict_bound hp σ hiσ hfσ C (j a)
    (mem_map_of_mem j ha) hs
  have hcod : fixedCodim (normalizerRepresentation σ) C =
      fixedCodim (normalizerRepresentation ρ) A :=
    (fixedCodim_map_equivariant (normalizerRepresentation ρ) (normalizerRepresentation σ)
      j (LinearEquiv.refl _ _) (fun _ _ => rfl) A).symm
  rw [hcod,show rank C = rank A from rank_map_injective j hj A] at hb
  exact hb

/-- Every small elementary actor preserves the two literal factor images.
The conclusion permits outer diagonal automorphisms of each factor. -/
theorem odd_prime_square_small_actor_preserves
    (hp : 11 ≤ p)
    (ρ : Representation (ZMod 2) (PSL(2,ZMod p) × PSL(2,ZMod p)) V)
    (hi : ρ.IsIrreducible) (hf : Function.Injective ρ)
    (A : Subgroup (linearNormalizer ρ)) [IsElementaryAbelian 2 A]
    (hsmall : fixedCodim (normalizerRepresentation ρ) A ≤ 2 * rank A) :
    ∀ a ∈ A, a.val ∈ normalizer
      (((⊤ : Subgroup PSL(2,ZMod p)).prod ⊥).map ρ.asGroupHom : Set _) := by
  let : IsSimpleGroup PSL(2,ZMod p) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by simpa using (show 4 ≤ p by omega))
  have hZ : center PSL(2,ZMod p) = ⊥ := center_eq_bot_of_simple_perfect
  let e := PerfectNormalizer.imageEquiv ρ hf
  let f : linearNormalizer ρ →* MulAut (PSL(2,ZMod p) × PSL(2,ZMod p)) :=
    (MulAut.congr e.symm).toMonoidHom.comp (actionImage ρ).normalizerMonoidHom
  intro a ha
  have h2 : a ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian a ha
  have hconj (g : PSL(2,ZMod p) × PSL(2,ZMod p)) :
      (e (f a g)).val = a.val * (e g).val * a.val⁻¹ :=
    congrArg Subtype.val (e.apply_symm_apply _)
  rcases AutomorphismSquare.normal_form hZ (f a) with ⟨α,β,hdiag⟩ | ⟨α,β,hswap⟩
  · let J := ((⊤ : Subgroup PSL(2,ZMod p)).prod ⊥).map ρ.asGroupHom
    have hJ : J ≤ actionImage ρ := by rintro _ ⟨g,_,rfl⟩; exact ⟨g,rfl⟩
    have hmem (g : PSL(2,ZMod p) × PSL(2,ZMod p)) : (e g).val ∈ J ↔ g.2 = 1 := by
      constructor
      · rintro ⟨k,hk,hkg⟩
        have he : k = g := e.injective (Subtype.ext hkg)
        exact he ▸ mem_bot.mp hk.2
      · intro hg
        exact ⟨g,⟨mem_top _,hg⟩,rfl⟩
    apply mem_normalizer_iff.mpr
    intro z
    constructor
    · intro hz
      obtain ⟨g,rfl⟩ := hJ hz
      change (e g).val ∈ J at hz
      change a.val * (e g).val * a.val⁻¹ ∈ J
      rw [←hconj,hdiag]
      apply (hmem _).mpr
      change β g.2 = 1
      rw [(hmem g).mp hz,β.map_one]
    · intro hz
      have hz' : z ∈ actionImage ρ := (mem_normalizer_iff.mp a.property z).mpr (hJ hz)
      obtain ⟨g,rfl⟩ := hz'
      change a.val * (e g).val * a.val⁻¹ ∈ J at hz
      rw [←hconj,hdiag] at hz
      apply (hmem g).mpr
      exact β.injective (((hmem _).mp hz).trans β.map_one.symm)
  · have hfa2 : (f a) ^ 2 = 1 := by rw [←map_pow,h2,map_one]
    have hba (x : PSL(2,ZMod p)) : β (α x) = x :=
      congrArg Prod.snd (DFunLike.congr_fun (hswap ▸ hfa2) (1,x))
    have hβ : β = α.symm := by
      apply MulEquiv.ext
      intro x
      obtain ⟨x,rfl⟩ := α.surjective x
      exact (hba x).trans (α.symm_apply_apply x).symm
    have hex : ∀ g v, normalizerRepresentation ρ a (ρ g v) =
        ρ (α g.2,α.symm g.1) (normalizerRepresentation ρ a v) := by
      intro g v
      have hh := congrArg (fun x : (Module.End (ZMod 2) V)ˣ => x.val
        (normalizerRepresentation ρ a v)) (hconj g).symm
      rw [hswap,hβ] at hh
      change a.val.val (ρ g ((a.val⁻¹).val (a.val.val v))) =
        ρ (α g.2,α.symm g.1) (a.val.val v) at hh
      have hv : (a.val⁻¹).val (a.val.val v) = v := by
        change ((a.val⁻¹).val * a.val.val) v = v
        rw [←Units.val_mul,inv_mul_cancel,Units.val_one]
        rfl
      rwa [hv] at hh
    exact ((not_lt_of_ge hsmall)
      (odd_prime_square_twisted_exchange_strict_bound hp ρ hi hf A a ha α hex)).elim

end Representation.SL2
