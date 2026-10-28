module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.Section

/-!
# The algebraic part of reversing the critical pair

Conjugation carries the literal commutator-preimage denominators to the
denominators with the endpoints exchanged. Thus the reversed actor rank
is the original quotient dimension, and conversely. Equality gives the
reversed numerical choice. These identities do not assert that the reversed
conjugator has the required geodesic, marked action, or nonsplitting data.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), F.9.12–17,
printed pp.322–324, and its use in 13.8.25, printed p.962.
-/

public section

open Subgroup
open Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences
variable {G : Type*} [Group G]

private theorem map_commutatorPreimage_le (f : G →* G) (Q B Z : Subgroup G)
    (hQZ : Q ≤ normalizer (Z : Set G)) :
    (commutatorPreimage Q B Z).map f ≤
      commutatorPreimage (Q.map f) (B.map f) (Z.map f) := by
  apply le_commutatorPreimage (map_mono (commutatorPreimage_le Q B Z))
  rw [← map_commutator]
  exact map_mono (commutator_commutatorPreimage_le Q B Z hQZ)

/-- The critical denominator is equivariant under an actual equivalence,
using local normalization of the line, with no ambient normality. -/
theorem map_commutatorPreimage_equiv (e : G ≃* G) (Q B Z : Subgroup G)
    (hQZ : Q ≤ normalizer (Z : Set G)) :
    (commutatorPreimage Q B Z).map e.toMonoidHom =
      commutatorPreimage (Q.map e.toMonoidHom) (B.map e.toMonoidHom)
        (Z.map e.toMonoidHom) := by
  apply le_antisymm (map_commutatorPreimage_le _ _ _ _ hQZ)
  have hm : Q.map e.toMonoidHom ≤ normalizer ((Z.map e.toMonoidHom : Subgroup G) : Set G) := by
    rw [← map_equiv_normalizer_eq]
    exact map_mono hQZ
  have h := map_commutatorPreimage_le e.symm.toMonoidHom
    (Q.map e.toMonoidHom) (B.map e.toMonoidHom) (Z.map e.toMonoidHom) hm
  have hh := map_mono (f := e.toMonoidHom) h
  have he : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id G := by
    ext x; exact e.apply_symm_apply x
  have he' : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
    ext x; exact e.symm_apply_apply x
  simpa only [map_map, he, he', map_id] using hh

@[simp] theorem conjugate_inverse_cancel (g : G) (Q : Subgroup G) :
    (Q.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = Q := by
  rw [map_map]
  have he : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id G := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [he, map_id]

/-- The source line condition also exchanges endpoints under the same
conjugator. This identity does not assert either noncontainment. -/
theorem reversed_line_containment (UH Z : Subgroup G) (g : G) :
    Z.map (MulAut.conj g).toMonoidHom ≤ UH ↔
      Z ≤ UH.map (MulAut.conj g⁻¹).toMonoidHom := by
  constructor
  · intro h
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) h
    rwa [conjugate_inverse_cancel] at hh
  · intro h
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) h
    have hc := conjugate_inverse_cancel g⁻¹ UH
    simp only [inv_inv] at hc
    rwa [hc] at hh

/-- Pulling the right-hand denominator back to H gives the left-hand
denominator for the reversed algebraic pair. -/
theorem reversed_DH (UH Z : Subgroup G) (g : G)
    (hUgZ : UH.map (MulAut.conj g).toMonoidHom ≤ normalizer (Z : Set G)) :
    Source.DH UH (UH.map (MulAut.conj g⁻¹).toMonoidHom)
        (Z.map (MulAut.conj g⁻¹).toMonoidHom) =
      (Source.Dgamma (UH.map (MulAut.conj g).toMonoidHom) UH Z).map
        (MulAut.conj g⁻¹).toMonoidHom := by
  rw [Source.Dgamma, map_commutatorPreimage_equiv _ _ _ _ hUgZ, conjugate_inverse_cancel]
  rfl

/-- The other denominator also swaps; its central line is again Z. -/
theorem reversed_Dgamma (UH Z : Subgroup G) (g : G)
    (hUA : UH ≤ normalizer ((Z.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) :
    Source.Dgamma (UH.map (MulAut.conj g⁻¹).toMonoidHom) UH Z =
      (Source.DH UH (UH.map (MulAut.conj g).toMonoidHom)
        (Z.map (MulAut.conj g).toMonoidHom)).map
        (MulAut.conj g⁻¹).toMonoidHom := by
  rw [Source.DH, map_commutatorPreimage_equiv _ _ _ _ hUA, conjugate_inverse_cancel,
    conjugate_inverse_cancel]
  rfl

theorem reversed_DH_index (UH Z : Subgroup G) (g : G)
    (hUgZ : UH.map (MulAut.conj g).toMonoidHom ≤ normalizer (Z : Set G)) :
    (Source.DH UH (UH.map (MulAut.conj g⁻¹).toMonoidHom)
      (Z.map (MulAut.conj g⁻¹).toMonoidHom)).relIndex UH =
      (Source.Dgamma (UH.map (MulAut.conj g).toMonoidHom) UH Z).relIndex
        (UH.map (MulAut.conj g).toMonoidHom) := by
  rw [reversed_DH UH Z g hUgZ]
  conv_lhs => arg 2; rw [← conjugate_inverse_cancel g UH]
  exact relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective

theorem reversed_Dgamma_index (UH Z : Subgroup G) (g : G)
    (hUA : UH ≤ normalizer ((Z.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) :
    (Source.Dgamma (UH.map (MulAut.conj g⁻¹).toMonoidHom) UH Z).relIndex
        (UH.map (MulAut.conj g⁻¹).toMonoidHom) =
      (Source.DH UH (UH.map (MulAut.conj g).toMonoidHom)
        (Z.map (MulAut.conj g).toMonoidHom)).relIndex UH := by
  rw [reversed_Dgamma UH Z g hUA]
  exact relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective

theorem reversed_actor_le (H UH : Subgroup G) (g : G)
    (h : UH ≤ H.map (MulAut.conj g).toMonoidHom) :
    UH.map (MulAut.conj g⁻¹).toMonoidHom ≤ H := by
  have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) h
  rwa [conjugate_inverse_cancel] at hh

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]
  {H UH Z : Subgroup G} {ρ : Representation (ZMod 2) (Source.Hstar H) U}

/-- The rank of the reversed actor and its actual section codimension are the
original codimension and rank. In particular, equality makes the reversed
numerical choice admissible, with no symmetry premise. -/
theorem reversed_rank_and_codimension (s : ConjugationSection H UH Z ρ) (g : G)
    (hforward : UH.map (MulAut.conj g).toMonoidHom ≤ H)
    (hreverse : UH ≤ H.map (MulAut.conj g).toMonoidHom)
    (hfaith : Function.Injective ρ) :
    rank (Source.starImage H (UH.map (MulAut.conj g⁻¹).toMonoidHom)) =
      Module.finrank (ZMod 2) (U ⧸ s.image (Source.DH UH
        (UH.map (MulAut.conj g).toMonoidHom) (Z.map (MulAut.conj g).toMonoidHom))) ∧
    Module.finrank (ZMod 2) (U ⧸ s.image (Source.DH UH
        (UH.map (MulAut.conj g⁻¹).toMonoidHom) (Z.map (MulAut.conj g⁻¹).toMonoidHom))) =
      rank (Source.starImage H (UH.map (MulAut.conj g).toMonoidHom)) := by
  have hr := reversed_actor_le H UH g hreverse
  have hUgZ := hforward.trans (s.centralizes.trans (centralizer_le_normalizer _))
  have hUA := hreverse.trans
    ((s.centralizes_conjugate_line g).trans (centralizer_le_normalizer _))
  constructor
  · rw [s.quotient_finrank _ (s.line_le_DH _ _ hforward), rank,
      ← s.Dgamma_relIndex _ hr hfaith, reversed_Dgamma_index UH Z g hUA]
  · rw [s.quotient_finrank _ (s.line_le_DH _ _ hr), reversed_DH_index UH Z g hUgZ,
      s.Dgamma_relIndex _ hforward hfaith, rank]

theorem equality_reversed_numerical_choice (s : ConjugationSection H UH Z ρ) (g : G)
    (hforward : UH.map (MulAut.conj g).toMonoidHom ≤ H)
    (hreverse : UH ≤ H.map (MulAut.conj g).toMonoidHom)
    (hfaith : Function.Injective ρ)
    (hrank : 1 < rank (Source.starImage H (UH.map (MulAut.conj g).toMonoidHom)))
    (hequal : Module.finrank (ZMod 2) (U ⧸ s.image (Source.DH UH
      (UH.map (MulAut.conj g).toMonoidHom) (Z.map (MulAut.conj g).toMonoidHom))) =
      rank (Source.starImage H (UH.map (MulAut.conj g).toMonoidHom))) :
    1 < rank (Source.starImage H (UH.map (MulAut.conj g⁻¹).toMonoidHom)) ∧
    Module.finrank (ZMod 2) (U ⧸ s.image (Source.DH UH
      (UH.map (MulAut.conj g⁻¹).toMonoidHom) (Z.map (MulAut.conj g⁻¹).toMonoidHom))) =
      rank (Source.starImage H (UH.map (MulAut.conj g⁻¹).toMonoidHom)) := by
  obtain ⟨hr, hc⟩ := reversed_rank_and_codimension s g hforward hreverse hfaith
  rw [hr, hequal]
  exact ⟨hrank, hc⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences
