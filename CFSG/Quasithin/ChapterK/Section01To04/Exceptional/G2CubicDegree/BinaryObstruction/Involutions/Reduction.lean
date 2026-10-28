module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Inputs
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Degrees
public import Theory.Representation.BinaryOffender.InnerInvolutions
public import Theory.Representation.BinaryOffender.InnerNormalizerActors
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Odd-element reduction for binary G₂ involution displacement

The commutator of an inverter with an odd-order element generates the same
cyclic subgroup as that element. The commutator rank inequality therefore
bounds the odd element's displacement by twice the inverter's displacement.
We transport this inequality through the literal action embedding into the
full linear normalizer. Binary Schur's lemma ensures that an outer normalizer
involution induces an outer automorphism of the original faithful actor.

The remaining group witnesses and the odd-element calculations on irreducible
modules are separate explicit premises. This is a conditional reduction of
Guralnick--Malle, Classification of 2F-modules I, Proposition 4.3, pp.10--11,
not a proof of those two concrete inputs. Both degrees 14 and 32 are retained.
-/

@[expose] public noncomputable section

namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction
open Subgroup Representation Representation.BinaryOffender

namespace Involutions

/-- The regular unipotent three-class of the actual derived binary G₂ group.
Its centralizer in the derived group, rather than the full G₂ group, has order nine. -/
def RegularThree (x : Derived) : Prop :=
  orderOf x = 3 ∧ Nat.card (centralizer ({x} : Set Derived)) = 9

/-- Group-theoretic inversion witnesses, independent of any representation. -/
structure InversionWitnesses : Prop where
  inner : ∀ t : Derived, t ≠ 1 → t ^ 2 = 1 →
    ∃ x : Derived, RegularThree x ∧ t * x * t⁻¹ = x⁻¹
  outer : ∀ a : MulAut Derived, a ^ 2 = 1 →
    (¬ ∃ g : Derived, a = MulAut.conj g) →
    ∃ x : Derived, orderOf x = 7 ∧ a x = x⁻¹

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The two odd-element calculations, retaining the actual representation. -/
structure OddDisplacementBounds (σ : Representation (ZMod 2) Derived V) : Prop where
  regular_three : ∀ x : Derived, RegularThree x → 10 ≤ fixedCodim σ (zpowers x)
  seven : ∀ x : Derived, orderOf x = 7 → 12 ≤ fixedCodim σ (zpowers x)

/-- The exact degree catalogue reduces the odd-element calculation to both
large-degree branches. No absolute irreducibility is imposed. -/
theorem oddDisplacementBounds_of_degree_cases [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) Derived V) [IsIrreducible σ]
    (hd : 8 < Module.finrank (ZMod 2) V)
    (h14 : Module.finrank (ZMod 2) V = 14 → OddDisplacementBounds σ)
    (h32 : Module.finrank (ZMod 2) V = 32 → OddDisplacementBounds σ) :
    OddDisplacementBounds σ := by
  rcases binary_derived_irreducible_degrees σ with h | h | h | h
  · omega
  · omega
  · exact h14 h
  · exact h32 h

section Normalizer
variable {G : Type*} [Group G]
  (σ : Representation (ZMod 2) G V) (hf : Function.Injective σ)

/-- The faithful representation identifies the original group with its literal image. -/
def faithfulImageEquiv : G ≃* actionImage σ :=
  MonoidHom.ofInjective (fun _ _ h => hf (congrArg Units.val h))

/-- Conjugation on the literal image, transported back to the original actor. -/
def normalizerAutomorphism : linearNormalizer σ →* MulAut G :=
  (MulAut.congr (faithfulImageEquiv σ hf).symm).toMonoidHom.comp
    (actionImage σ).normalizerMonoidHom

/-- The transported automorphism preserves the literal conjugation equation. -/
theorem normalizerAutomorphism_action (t : linearNormalizer σ) (x : G) :
    σ.asGroupHom (normalizerAutomorphism σ hf t x) =
      t.val * σ.asGroupHom x * t.val⁻¹ := by
  let e := faithfulImageEquiv σ hf
  exact congrArg Subtype.val (e.apply_symm_apply
    ((actionImage σ).normalizerMonoidHom t (e x)))

/-- An involution inducing an inner automorphism is an actual square-one
operator from the original group. This also removes the possible Schur kernel. -/
theorem normalizerAutomorphism_lift_inner [Finite G] [IsIrreducible σ]
    (t : linearNormalizer σ) (ht : t ^ 2 = 1)
    (hi : ∃ x : G, normalizerAutomorphism σ hf t = MulAut.conj x) :
    ∃ x : G, x ^ 2 = 1 ∧ t.val = σ.asGroupHom x := by
  let e := faithfulImageEquiv σ hf
  have hinner : ∃ a : actionImage σ,
      (actionImage σ).normalizerMonoidHom t = MulAut.conj a := by
    obtain ⟨x, hx⟩ := hi
    refine ⟨e x, ?_⟩
    apply (MulAut.congr e.symm).injective
    rw [MulAut.congr_conj, e.symm_apply_apply]
    exact hx
  let : IsIrreducible ((Units.coeHom (Module.End (ZMod 2) V)).comp
      (actionImage σ).subtype) := imageRepresentation_isIrreducible σ inferInstance
  have hmem := involution_mem_of_inner (Units.coeHom (Module.End (ZMod 2) V))
    (actionImage σ) (fun _ _ h => Units.ext h) t (congrArg Subtype.val ht) hinner
  obtain ⟨x, hx⟩ := hmem
  refine ⟨x, ?_, hx.symm⟩
  apply hf
  have hσ : σ.asGroupHom (x ^ 2) = σ.asGroupHom 1 := by
    rw [map_pow, hx, map_one]
    exact congrArg Subtype.val ht
  exact congrArg Units.val hσ

/-- Inversion on the original group is inversion of its actual embedded operators. -/
theorem normalizerEmbedding_inverted (t : linearNormalizer σ) (x : G)
    (hx : normalizerAutomorphism σ hf t x = x⁻¹) :
    t * normalizerEmbedding σ x * t⁻¹ = (normalizerEmbedding σ x)⁻¹ := by
  apply Subtype.ext
  have he := normalizerAutomorphism_action σ hf t x
  rw [hx, map_inv] at he
  exact he.symm

end Normalizer

/-- Noninner involutions of the full normalizer remain noninner on the actor. -/
theorem normalizerAutomorphism_not_inner
    (σ : Representation (ZMod 2) Derived V) (hf : Function.Injective σ)
    [IsIrreducible σ] (t : linearNormalizer σ) (ht : t ^ 2 = 1)
    (hi : ¬ innerInvolution σ t) :
    ¬ ∃ x : Derived, normalizerAutomorphism σ hf t = MulAut.conj x :=
  fun h => hi (normalizerAutomorphism_lift_inner σ hf t ht h)

/-- Embedding the actor in its full normalizer does not change displacement. -/
theorem fixedCodim_normalizerEmbedding (σ : Representation (ZMod 2) Derived V)
    (x : Derived) :
    fixedCodim (normalizerRepresentation σ) (zpowers (normalizerEmbedding σ x)) =
      fixedCodim σ (zpowers x) := by
  rw [← (normalizerEmbedding σ).map_zpowers]
  exact (fixedCodim_map_equivariant σ (normalizerRepresentation σ)
    (normalizerEmbedding σ) (LinearEquiv.refl _ _) (fun _ _ => rfl) (zpowers x)).symm

private theorem odd_fixedCodim_le_twice {G : Type*} [Group G]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
    (x t : G) (ho : Odd (orderOf x)) (hi : t * x * t⁻¹ = x⁻¹) :
    fixedCodim ρ (zpowers x) ≤ 2 * fixedCodim ρ (zpowers t) := by
  have hp : zpowers (x ^ 2) = zpowers x := by
    apply le_antisymm
    · exact zpowers_le.mpr ((zpowers x).pow_mem (mem_zpowers x) 2)
    · apply zpowers_le.mpr
      exact mem_zpowers_pow_iff.mpr ho.coprime_two_left.gcd_eq_one
  have he : t * x * t⁻¹ * x⁻¹ = (x ^ 2)⁻¹ := by
    rw [hi, pow_two, mul_inv_rev]
  simpa only [he, zpowers_inv, hp] using fixedCodim_commutator_le_twice ρ t x

/-- The odd-element inequality on the literal full normalizer, with the
odd displacement still measured on the original component representation. -/
theorem fixedCodim_le_twice_normalizer [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) Derived V) (hf : Function.Injective σ)
    (t : linearNormalizer σ) (x : Derived) (ho : Odd (orderOf x))
    (hi : t * normalizerEmbedding σ x * t⁻¹ = (normalizerEmbedding σ x)⁻¹) :
    fixedCodim σ (zpowers x) ≤ 2 * fixedCodim (normalizerRepresentation σ) (zpowers t) := by
  have ho' : Odd (orderOf (normalizerEmbedding σ x)) := by
    rw [orderOf_injective (normalizerEmbedding σ) (normalizerEmbedding_injective σ hf)]
    exact ho
  have h := odd_fixedCodim_le_twice (normalizerRepresentation σ)
    (normalizerEmbedding σ x) t ho' hi
  rwa [fixedCodim_normalizerEmbedding] at h

/-- The concrete odd-element and group calculations imply both required
involution bounds, including outer actors and the degree-32 branch. -/
theorem involutionBounds_of_odd_displacement [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) Derived V) [IsIrreducible σ]
    (hf : Function.Injective σ) (witnesses : InversionWitnesses)
    (bounds : OddDisplacementBounds σ) : InvolutionBounds σ := by
  constructor
  · intro t ht _ hinner
    obtain ⟨g, hg2, hg⟩ := hinner
    have hgt : normalizerEmbedding σ g = t := Subtype.ext hg.symm
    have hg1 : g ≠ 1 := by
      intro he
      apply ht
      rw [← hgt, he, map_one]
    obtain ⟨x, hx, hinv⟩ := witnesses.inner g hg1 hg2
    have hinv' : t * normalizerEmbedding σ x * t⁻¹ =
        (normalizerEmbedding σ x)⁻¹ := by
      rw [← hgt, ← map_inv, ← map_mul, ← map_mul, hinv, map_inv]
    have h := fixedCodim_le_twice_normalizer σ hf t x (by rw [hx.1]; decide) hinv'
    have hten := bounds.regular_three x hx
    omega
  · intro t _ ht houter
    obtain ⟨x, hx, hinv⟩ := witnesses.outer (normalizerAutomorphism σ hf t)
      (by rw [← map_pow, ht, map_one])
      (normalizerAutomorphism_not_inner σ hf t ht houter)
    have h := fixedCodim_le_twice_normalizer σ hf t x (by rw [hx]; decide)
      (normalizerEmbedding_inverted σ hf t x hinv)
    have htwelve := bounds.seven x hx
    omega

end Involutions
end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction
