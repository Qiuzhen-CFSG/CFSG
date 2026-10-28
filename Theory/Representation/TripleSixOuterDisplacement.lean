module

public import Theory.Alternating.TripleSixActorInversion
public import Theory.Representation.HexacodeAction.CoverRecognition
public import Theory.Representation.SchurDisplacement

/-!
# Outer involutions on faithful triple-A₆ constituents

Recognize the ORIGINAL quasisimple group, with cubic center and actual A₆
central quotient, as the even hexacode cover over the specified quotient map.
The proved outer-involution theorem for that cover then inverts its cubic
center. In a faithful representation the corresponding central operator is
an element of the component Schur algebra which the involution moves.
Schur displacement therefore gives rank at least three in binary dimension six.

Faithfulness is required only on the component. Scalar inversion, a splitting
of the cover, and a faithful action of the central quotient are not premises.

Source: GLS3 5.2.3 and 5.2.7, via TripleSixActorInversion; Aschbacher–Smith,
combined manuscript of 1 March 2004, 13.5.21, printed p.924 (PDF p.941).
The concrete cover and its projection use the existing licensed hexacode port.
-/

@[expose] public section

open Subgroup Theory.GroupTheory Representation Atlas.Codes
namespace Representation.TripleSixOuterDisplacement

/-- The induced equivalence retains the actual central quotient. -/
noncomputable def centralQuotientEquiv {E F : Type*} [Group E] [Group F]
    (e : E ≃* F) : (E ⧸ center E) ≃* (F ⧸ center F) :=
  QuotientGroup.congr _ _ e (by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (centerCongr e ⟨x, hx⟩).property
    · intro hy
      exact ⟨e.symm y, (centerCongr e.symm ⟨y, hy⟩).property, e.apply_symm_apply y⟩)

/-- Recognize the original perfect cover, retaining its central quotient map. -/
theorem cover_equiv {E : Type*} [Group E] [Finite E] [IsQuasisimple E]
    (hc : Nat.card (center E) = 3)
    (q : (E ⧸ center E) ≃* alternatingGroup (Fin 6)) :
    ∃ e : E ≃* HexEvenAutomorphisms,
      hexEvenCoordinate.comp e.toMonoidHom =
        q.toMonoidHom.comp (QuotientGroup.mk' (center E)) := by
  let f := q.toMonoidHom.comp (QuotientGroup.mk' (center E))
  have hk : f.ker = center E := by
    rw [MonoidHom.ker_comp_of_injective _ _ q.injective, QuotientGroup.ker_mk']
  exact Hexacode.triple_cover_equiv f
    (q.surjective.comp (QuotientGroup.mk'_surjective _)) hk.le (hk ▸ hc)

/-- Every outer involution inverts the cubic center of the original cover. -/
theorem center_inverted {E : Type*} [Group E] [Finite E] [IsQuasisimple E]
    (hc : Nat.card (center E) = 3)
    (q : (E ⧸ center E) ≃* alternatingGroup (Fin 6))
    (a : MulAut E) (ha : a ^ 2 = 1)
    (hout : ∀ k : E, a ≠ MulAut.conj k) :
    ∀ z : E, z ∈ center E → a z = z⁻¹ := by
  obtain ⟨e, _⟩ := cover_equiv hc q
  let b := MulAut.congr e a
  have hb : b ^ 2 = 1 := by
    change MulAut.congr e a ^ 2 = 1
    rw [← map_pow, ha, map_one]
  have hbo : ∀ k : HexEvenAutomorphisms, b ≠ MulAut.conj k := by
    intro k hk
    apply hout (e.symm k)
    ext z
    apply e.injective
    have he := DFunLike.congr_fun hk (e z)
    change e (a (e.symm (e z))) = k * e z * k⁻¹ at he
    simpa only [e.symm_apply_apply, MulAut.conj_apply, map_mul, map_inv,
      e.apply_symm_apply] using he
  intro z hz
  have hez : e z ∈ center HexEvenAutomorphisms := (centerCongr e ⟨z, hz⟩).property
  have he := GLS3.Chapter5.TripleSixActorInversion.hexEven_center_inverted b hb hbo (e z) hez
  apply e.injective
  change e (a (e.symm (e z))) = (e z)⁻¹ at he
  simpa only [e.symm_apply_apply, map_inv] using he

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- Cubic scalar movement is a consequence of outer involutory conjugation,
not an additional assumption on the representation. Only the original
component action needs to be faithful. -/
theorem not_isSchurLinear (ρ : Representation (ZMod 2) G V)
    (L : Subgroup G) [Finite L] [IsQuasisimple L]
    (hc : Nat.card (center L) = 3)
    (q : (L ⧸ center L) ≃* alternatingGroup (Fin 6))
    (hf : Function.Injective (ρ.comp L.subtype))
    (t : G) (ht : t ∈ normalizer (L : Set G)) (ht2 : t ^ 2 = 1)
    (hout : ∀ k : L, L.normalizerMonoidHom ⟨t, ht⟩ ≠ MulAut.conj k) :
    ¬ IsSchurLinear ρ L t := by
  obtain ⟨e, _⟩ := cover_equiv hc q
  let z : L := e.symm hexEvenZ
  have hz : z ∈ center L := by
    apply mem_center_iff.mpr
    intro g
    apply e.injective
    simp only [map_mul, z, e.apply_symm_apply]
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mp (hex_conjugation_even (e g).val (e g).property)
  have hz3 : z ^ 3 = 1 := by
    apply e.injective
    simp only [map_pow, z, e.apply_symm_apply, map_one]
    exact Subtype.ext hexZ_cube
  have hz1 : z ≠ 1 := by
    intro h
    apply hexZ_ne_one
    have he := congrArg (fun x => (e x).val) h
    simpa only [z, e.apply_symm_apply, map_one, Subgroup.coe_one, hexEvenZ] using he
  have ha2 : (L.normalizerMonoidHom ⟨t, ht⟩) ^ 2 = 1 := by
    rw [← map_pow]
    have he : (⟨t, ht⟩ : normalizer (L : Set G)) ^ 2 = 1 := Subtype.ext ht2
    rw [he, map_one]
  have hinv : t * (z : G) * t⁻¹ = (z : G)⁻¹ :=
    congrArg Subtype.val (center_inverted hc q _ ha2 hout z hz)
  let f : IntertwiningMap (ρ.comp L.subtype) (ρ.comp L.subtype) :=
    { toLinearMap := ρ (z : G)
      isIntertwining' := by
        intro g
        change ρ (z : G) * ρ (g : G) = ρ (g : G) * ρ (z : G)
        rw [← map_mul, ← map_mul]
        exact congrArg (fun k : L => ρ (k : G)) (mem_center_iff.mp hz g).symm }
  intro hs
  have hcomm := (hs f).eq
  change ρ t * ρ (z : G) = ρ (z : G) * ρ t at hcomm
  have he : (ρ.comp L.subtype) z⁻¹ = (ρ.comp L.subtype) z := by
    change ρ (z : G)⁻¹ = ρ (z : G)
    rw [← hinv, map_mul, map_mul, hcomm, mul_assoc, ← map_mul,
      mul_inv_cancel, map_one, mul_one]
  have hzi : z⁻¹ = z := hf he
  have hz2 : z ^ 2 = 1 := by
    calc
      z ^ 2 = z⁻¹ * z := by rw [pow_two, hzi]
      _ = 1 := inv_mul_cancel z
  apply hz1
  simpa only [pow_succ, hz2, one_mul] using hz3

/-- The six-dimensional constituent forces displacement at least three. -/
theorem displacement_ge_three [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G)
    [Finite L] [IsQuasisimple L] [IsIrreducible (ρ.comp L.subtype)]
    (hc : Nat.card (center L) = 3)
    (q : (L ⧸ center L) ≃* alternatingGroup (Fin 6))
    (hf : Function.Injective (ρ.comp L.subtype))
    (hd : Module.finrank (ZMod 2) V = 6)
    (t : G) (ht : t ∈ normalizer (L : Set G)) (ht2 : t ^ 2 = 1)
    (hout : ∀ k : L, L.normalizerMonoidHom ⟨t, ht⟩ ≠ MulAut.conj k) :
    3 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) := by
  have h := finrank_le_twice_displacement_of_not_isSchurLinear ρ L t ht
    (not_isSchurLinear ρ L hc q hf t ht ht2 hout)
  omega

end Representation.TripleSixOuterDisplacement
