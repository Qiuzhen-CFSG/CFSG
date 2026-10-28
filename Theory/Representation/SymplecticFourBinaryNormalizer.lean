module

public import Theory.Representation.SymplecticConjugatePair.Ambient.Normalizer

/-!
# The binary symplectic natural normalizer

The proved semilinear normalizer theorem applies to the genuine derived
Sp4 image, including over F2. Both the coefficient unit and field
automorphism are trivial over F2, so every such normalizer is a full
symplectic operator. In particular an automorphism of Sp4(2) realized on
its natural module is inner.

Source: Aschbacher–Smith, H.7, pp.388–389; applied in G.6.4, pp.345–346.
-/

public section
open Subgroup Representation Theory.SpecificGroups.SymplecticFour
open SymplecticConjugatePair.Ambient
namespace Representation.SymplecticFourBinaryNormalizer
open SymplecticConjugatePair.Ambient.Normalizer

theorem normalizer
    (f : Vector (ZMod 2) ≃ₗ[ZMod 2] Vector (ZMod 2)) (φ : MulAut (Sp (ZMod 2)))
    (hf : ∀ g v, f (symplecticNatural 2 g v) = symplecticNatural 2 (φ g) (f v)) :
    ∃ s : Sp (ZMod 2), ∀ v, f v = symplecticNatural 2 s v := by
  have hconj (g : commutator (Sp (ZMod 2))) :
      f * linearAction naturalDerivedAction g * f⁻¹ ∈ naturalDerivedImage := by
    refine ⟨MulAut.characteristic (commutator (Sp (ZMod 2))) φ g, ?_⟩
    apply LinearEquiv.ext
    intro v
    change symplecticNatural 2 (φ g.val) v = f (symplecticNatural 2 g.val (f.symm v))
    rw [hf, f.apply_symm_apply]
  let : Finite (naturalDerivedImage (F := ZMod 2)) :=
    Finite.of_surjective (linearAction (naturalDerivedAction (F := ZMod 2))).rangeRestrict
      (linearAction (naturalDerivedAction (F := ZMod 2))).rangeRestrict_surjective
  have hn : f ∈ naturalNormalizer := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
      exact hconj g
    · exact (Subgroup.card_map_of_injective (MulAut.conj f).injective).ge
  obtain ⟨a, s, σ, he⟩ := naturalNormalizer_semilinear f hn
  have ha : a = 1 := Subsingleton.elim _ _
  have hσ : σ = RingEquiv.refl (ZMod 2) := by
    apply RingEquiv.ext
    intro x
    fin_cases x
    · exact map_zero σ
    · exact map_one σ
  refine ⟨s, fun v => ?_⟩
  rw [he, ha, hσ]
  simp only [Units.val_one, one_smul]
  rfl

theorem automorphism_inner
    (f : Vector (ZMod 2) ≃ₗ[ZMod 2] Vector (ZMod 2)) (φ : MulAut (Sp (ZMod 2)))
    (hf : ∀ g v, f (symplecticNatural 2 g v) = symplecticNatural 2 (φ g) (f v)) :
    ∃ s : Sp (ZMod 2), MulAut.conj s = φ := by
  obtain ⟨s, hs⟩ := normalizer f φ hf
  refine ⟨s, ?_⟩
  apply MulEquiv.ext
  intro g
  apply Subtype.ext
  ext i j
  have hc : symplecticNatural 2 (s * g * s⁻¹) = symplecticNatural 2 (φ g) := by
    apply LinearMap.ext
    intro v
    obtain ⟨w, rfl⟩ := ((symplecticNatural (k := ZMod 2) 2).apply_bijective s).2 v
    have h := hf g w
    rw [hs, hs] at h
    simpa only [← Module.End.mul_apply, ← map_mul, mul_assoc,
      inv_mul_cancel, mul_one] using h
  have hij := congrArg (fun x : Vector (ZMod 2) => x i)
    (LinearMap.congr_fun hc (Pi.single j 1))
  simpa only [MulAut.conj_apply, symplecticNatural_apply, Matrix.mulVec_single_one,
    Matrix.col_apply] using hij

end Representation.SymplecticFourBinaryNormalizer
