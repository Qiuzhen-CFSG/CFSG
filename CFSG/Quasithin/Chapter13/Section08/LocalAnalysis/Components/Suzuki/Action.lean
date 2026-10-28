module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.Natural
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.Reduction

/-!
# Equivariant transport and lifting of the Suzuki calculation

The multiplicative field group is prime to both two and three. Hence an
endomorphism commuting with either the natural Suzuki module or the pair
of natural modules, whose order divides 2^r 3^s, is the identity. Conjugating
endomorphisms by an actual equivariant linear equivalence transports this
calculation to any representation surjecting onto the concrete actor.

For W=[W,K], use the literal action of L on W/C_W(K). When L centralizes K
and has order 2^r 3^s, the natural-module calculation makes this quotient
action trivial. The commutator lifting lemma then fixes all of W without
splitting off C_W(K). Both the one-factor and two-factor versions are proved.

These conditional lemmas support Aschbacher–Smith 13.8.16, printed pp.952–953
(combined manuscript of 1 March 2004). The source owner must construct the
equivariant identifications, commuting actors and commutator generation.
-/

public section

open BenderSuzuki BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII Representation
namespace CFSG.Quasithin.Chapter13.Section08.Components.Suzuki

/-- The commuting endomorphisms are precisely multiplication by a unique field scalar. -/
theorem commuting_endomorphism_iff_scalar (m : ℕ)
    (f : Module.End (ZMod 2) (Fin 4 → BinaryGaloisField (2 * m + 1))) :
    (∀ g : SuzukiMatrixGroup m, ∀ v, f (natural m g v) = natural m g (f v)) ↔
      ∃! a : BinaryGaloisField (2 * m + 1), ∀ v, f v = a • v := by
  constructor
  · intro hf
    obtain ⟨a, ha⟩ := commuting_endomorphism_scalar m f hf
    refine ⟨a, ha, ?_⟩
    intro b hb
    have he := congrFun ((hb (fun _ => 1)).symm.trans (ha (fun _ => 1))) 0
    simpa using he
  · rintro ⟨a, ha, _⟩ g v
    rw [ha, ha, natural_smul]

/-- The multiplicative group of the binary field has odd order. -/
theorem field_units_card_coprime_two (m : ℕ) :
    Nat.Coprime 2 (Nat.card (BinaryGaloisField (2 * m + 1))ˣ) := by
  rw [Nat.card_units, GaloisField.card 2 (2 * m + 1) (by omega)]
  apply Nat.prime_two.coprime_iff_not_dvd.mpr
  intro h
  have he : 2 ^ (2 * m + 1) % 2 = 0 := by
    simp [Nat.pow_mod]
  have hp : 1 ≤ 2 ^ (2 * m + 1) := by
    have : 0 < 2 ^ (2 * m + 1) := by positivity
    omega
  have hz := (Nat.modEq_iff_dvd' hp).mpr h
  change 1 % 2 = 2 ^ (2 * m + 1) % 2 at hz
  omega

/-- A scalar of order dividing a product of powers of two and three is one. -/
theorem field_scalar_eq_one_of_pow_two_three (m r s : ℕ)
    (a : BinaryGaloisField (2 * m + 1)) (ha : a ^ (2 ^ r * 3 ^ s) = 1) : a = 1 := by
  have hn : 2 ^ r * 3 ^ s ≠ 0 := by positivity
  have hne : a ≠ 0 := by intro hz; simp [hz, hn] at ha
  let u := Units.mk0 a hne
  have hu : u ^ (2 ^ r * 3 ^ s) = 1 := Units.ext ha
  have hc : Nat.Coprime (2 ^ r * 3 ^ s) (Nat.card (BinaryGaloisField (2 * m + 1))ˣ) :=
    ((field_units_card_coprime_two m).pow_left r).mul_left
      ((field_units_card_coprime_three m).pow_left s)
  have he : u = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hc (orderOf_dvd_of_pow_eq_one hu) (orderOf_dvd_natCard u))
  exact congrArg Units.val he

private theorem scalar_pow_apply (m : ℕ)
    (f : Module.End (ZMod 2) (Fin 4 → BinaryGaloisField (2 * m + 1)))
    (a : BinaryGaloisField (2 * m + 1)) (hf : ∀ v, f v = a • v)
    (n : ℕ) (v) : (f ^ n) v = a ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, hf, smul_smul, pow_succ']

/-- The natural module has no nontrivial commuting operator of order dividing 2^r 3^s. -/
theorem commuting_endomorphism_eq_one_of_pow_two_three (m r s : ℕ)
    (f : Module.End (ZMod 2) (Fin 4 → BinaryGaloisField (2 * m + 1)))
    (hf : ∀ g : SuzukiMatrixGroup m, ∀ v, f (natural m g v) = natural m g (f v))
    (hpow : f ^ (2 ^ r * 3 ^ s) = 1) : f = 1 := by
  obtain ⟨a, ha⟩ := commuting_endomorphism_scalar m f hf
  have he := congrArg (fun t : Module.End (ZMod 2)
    (Fin 4 → BinaryGaloisField (2 * m + 1)) => t (fun _ => 1) 0) hpow
  have hscalar : a ^ (2 ^ r * 3 ^ s) = 1 := by
    simpa only [scalar_pow_apply m f a ha, Pi.smul_apply, smul_eq_mul, mul_one,
      Module.End.one_apply] using he
  have ha1 := field_scalar_eq_one_of_pow_two_three m r s a hscalar
  apply LinearMap.ext
  intro v
  simp [ha, ha1]


/-- The same order obstruction holds for the two independent natural summands. -/
theorem commuting_pair_endomorphism_eq_one_of_pow_two_three (m r s : ℕ)
    (f : Module.End (ZMod 2) ((Fin 4 → BinaryGaloisField (2 * m + 1)) ×
      (Fin 4 → BinaryGaloisField (2 * m + 1))))
    (hf : ∀ g, ∀ v, f (naturalPair m g v) = naturalPair m g (f v))
    (hpow : f ^ (2 ^ r * 3 ^ s) = 1) : f = 1 := by
  obtain ⟨a, b, hab⟩ := commuting_pair_endomorphism_scalar m f hf
  have hpowapply (n : ℕ) (v) : (f ^ n) v = (a ^ n • v.1, b ^ n • v.2) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih, hab]
      simp only [smul_smul, pow_succ']
  have ha := congrArg (fun t : Module.End (ZMod 2)
    ((Fin 4 → BinaryGaloisField (2 * m + 1)) × (Fin 4 → BinaryGaloisField (2 * m + 1))) =>
      (t ((fun _ => 1), 0)).1 0) hpow
  have hb := congrArg (fun t : Module.End (ZMod 2)
    ((Fin 4 → BinaryGaloisField (2 * m + 1)) × (Fin 4 → BinaryGaloisField (2 * m + 1))) =>
      (t (0, (fun _ => 1))).2 0) hpow
  have ha3 : a ^ (2 ^ r * 3 ^ s) = 1 := by
    simpa only [hpowapply, Pi.smul_apply, smul_eq_mul, mul_one, Module.End.one_apply] using ha
  have hb3 : b ^ (2 ^ r * 3 ^ s) = 1 := by
    simpa only [hpowapply, Pi.smul_apply, smul_eq_mul, mul_one, Module.End.one_apply] using hb
  have ha1 := field_scalar_eq_one_of_pow_two_three m r s a ha3
  have hb1 := field_scalar_eq_one_of_pow_two_three m r s b hb3
  apply LinearMap.ext
  intro v
  change f v = v
  simp [hab, ha1, hb1]

section Transport
variable {K D V W : Type*} [Group K] [Group D]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]

/-- An equivariant equivalence and a surjective actor map transport the full commutation condition. -/
theorem conjugated_endomorphism_commutes
    (ρ : Representation (ZMod 2) K V) (σ : Representation (ZMod 2) D W)
    (φ : K →* D) (hφ : Function.Surjective φ) (e : V ≃ₗ[ZMod 2] W)
    (he : ∀ k v, e (ρ k v) = σ (φ k) (e v))
    (f : Module.End (ZMod 2) V) (hf : ∀ k v, f (ρ k v) = ρ k (f v)) :
    ∀ d w, e.conjRingEquiv f (σ d w) = σ d (e.conjRingEquiv f w) := by
  intro d w
  obtain ⟨k, rfl⟩ := hφ d
  change e (f (e.symm (σ (φ k) w))) = σ (φ k) (e (f (e.symm w)))
  have hinv : e.symm (σ (φ k) w) = ρ k (e.symm w) := by
    apply e.injective
    rw [e.apply_symm_apply, he, e.apply_symm_apply]
  rw [hinv, hf, he]

/-- Transport the single natural-module calculation through an actual equivariant identification. -/
theorem natural_transport_eq_one (m r s : ℕ)
    (ρ : Representation (ZMod 2) K V) (φ : K →* SuzukiMatrixGroup m)
    (hφ : Function.Surjective φ)
    (e : V ≃ₗ[ZMod 2] (Fin 4 → BinaryGaloisField (2 * m + 1)))
    (he : ∀ k v, e (ρ k v) = natural m (φ k) (e v))
    (f : Module.End (ZMod 2) V) (hf : ∀ k v, f (ρ k v) = ρ k (f v))
    (hpow : f ^ (2 ^ r * 3 ^ s) = 1) : f = 1 := by
  apply e.conjRingEquiv.injective
  rw [map_one]
  apply commuting_endomorphism_eq_one_of_pow_two_three m r s
  · exact conjugated_endomorphism_commutes ρ (natural m) φ hφ e he f hf
  · rw [← map_pow, hpow, map_one]

/-- Transport the two-factor calculation through an actual equivariant identification. -/
theorem naturalPair_transport_eq_one (m r s : ℕ)
    (ρ : Representation (ZMod 2) K V)
    (φ : K →* (SuzukiMatrixGroup m × SuzukiMatrixGroup m))
    (hφ : Function.Surjective φ)
    (e : V ≃ₗ[ZMod 2] ((Fin 4 → BinaryGaloisField (2 * m + 1)) ×
      (Fin 4 → BinaryGaloisField (2 * m + 1))))
    (he : ∀ k v, e (ρ k v) = naturalPair m (φ k) (e v))
    (f : Module.End (ZMod 2) V) (hf : ∀ k v, f (ρ k v) = ρ k (f v))
    (hpow : f ^ (2 ^ r * 3 ^ s) = 1) : f = 1 := by
  apply e.conjRingEquiv.injective
  rw [map_one]
  apply commuting_pair_endomorphism_eq_one_of_pow_two_three m r s
  · exact conjugated_endomorphism_commutes ρ (naturalPair m) φ hφ e he f hf
  · rw [← map_pow, hpow, map_one]

end Transport


section CentralExtension
open Subgroup Representation.BinaryOffender
variable {G V D X : Type*} [Group G]
  [AddCommGroup V] [Module (ZMod 2) V]
  [Group D] [AddCommGroup X] [Module (ZMod 2) X]

private theorem central_extension_fixed_of_model
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) D X)
    (K L : Subgroup G) (W : Submodule (ZMod 2) V)
    (hWK : K ≤ subspaceStabilizer ρ W) (hWL : L ≤ subspaceStabilizer ρ W)
    (hc : L ≤ centralizer (K : Set G))
    (hgen : subspaceCommutator ρ W K = W)
    (r s : ℕ) (hcard : Nat.card L = 2 ^ r * 3 ^ s)
    (φ : K →* D) (hφ : Function.Surjective φ)
    (e : centralQuotient ρ K W ≃ₗ[ZMod 2] X)
    (he : ∀ k v, e (centralQuotientRepresentation ρ K W hWK k v) = σ (φ k) (e v))
    (hmodel : ∀ f : Module.End (ZMod 2) X,
      (∀ g v, f (σ g v) = σ g (f v)) → f ^ (2 ^ r * 3 ^ s) = 1 → f = 1) :
    W ≤ fixedSpace ρ L := by
  let τ := centralSectionRepresentation ρ K L W hWL
    (hc.trans (centralizer_le_normalizer _))
  have hcomm (l : L) (k : K) (v) :
      τ l (centralQuotientRepresentation ρ K W hWK k v) =
        centralQuotientRepresentation ρ K W hWK k (τ l v) := by
    induction v using Submodule.Quotient.induction_on with | _ v =>
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    congr 1
    apply Subtype.ext
    change ρ l (ρ k v) = ρ k (ρ l v)
    change (ρ l * ρ k) v = (ρ k * ρ l) v
    rw [← map_mul, ← map_mul]
    have hkcomm := mem_centralizer_iff.mp (hc l.property) k k.property
    rw [hkcomm]
  have htrivial (l : L) : τ l = 1 := by
    apply e.conjRingEquiv.injective
    rw [map_one]
    apply hmodel
    · exact conjugated_endomorphism_commutes
        (centralQuotientRepresentation ρ K W hWK) σ φ hφ e he (τ l) (hcomm l)
    · rw [← map_pow, ← hcard, ← map_pow, pow_card_eq_one', map_one, map_one]
  apply central_extension_fixed_of_section_kernel ρ K L W hWL hc hgen
  apply top_unique
  intro l _
  exact htrivial l

/-- Fix the entire commutator-generated extension when its literal central quotient is natural. -/
theorem central_extension_fixed_of_natural
    (ρ : Representation (ZMod 2) G V) (K L : Subgroup G)
    (W : Submodule (ZMod 2) V)
    (hWK : K ≤ subspaceStabilizer ρ W) (hWL : L ≤ subspaceStabilizer ρ W)
    (hc : L ≤ centralizer (K : Set G))
    (hgen : subspaceCommutator ρ W K = W)
    (m r s : ℕ) (hcard : Nat.card L = 2 ^ r * 3 ^ s)
    (φ : K →* SuzukiMatrixGroup m) (hφ : Function.Surjective φ)
    (e : centralQuotient ρ K W ≃ₗ[ZMod 2] (Fin 4 → BinaryGaloisField (2 * m + 1)))
    (he : ∀ k v, e (centralQuotientRepresentation ρ K W hWK k v) =
      natural m (φ k) (e v)) : W ≤ fixedSpace ρ L :=
  central_extension_fixed_of_model ρ (natural m) K L W hWK hWL hc hgen r s hcard φ hφ e he
    (commuting_endomorphism_eq_one_of_pow_two_three m r s)

/-- Fix the entire commutator-generated extension when its literal central quotient is the two-factor natural module. -/
theorem central_extension_fixed_of_naturalPair
    (ρ : Representation (ZMod 2) G V) (K L : Subgroup G)
    (W : Submodule (ZMod 2) V)
    (hWK : K ≤ subspaceStabilizer ρ W) (hWL : L ≤ subspaceStabilizer ρ W)
    (hc : L ≤ centralizer (K : Set G))
    (hgen : subspaceCommutator ρ W K = W)
    (m r s : ℕ) (hcard : Nat.card L = 2 ^ r * 3 ^ s)
    (φ : K →* (SuzukiMatrixGroup m × SuzukiMatrixGroup m)) (hφ : Function.Surjective φ)
    (e : centralQuotient ρ K W ≃ₗ[ZMod 2] ((Fin 4 → BinaryGaloisField (2 * m + 1)) ×
      (Fin 4 → BinaryGaloisField (2 * m + 1))))
    (he : ∀ k v, e (centralQuotientRepresentation ρ K W hWK k v) =
      naturalPair m (φ k) (e v)) : W ≤ fixedSpace ρ L :=
  central_extension_fixed_of_model ρ (naturalPair m) K L W hWK hWL hc hgen r s hcard φ hφ e he
    (commuting_pair_endomorphism_eq_one_of_pow_two_three m r s)

end CentralExtension

end CFSG.Quasithin.Chapter13.Section08.Components.Suzuki
