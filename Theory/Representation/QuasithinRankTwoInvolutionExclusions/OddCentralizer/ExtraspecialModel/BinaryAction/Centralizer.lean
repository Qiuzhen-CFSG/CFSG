module

public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.OddCentralizer.ExtraspecialModel.BinaryAction
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.OddCentralizer.ExtraspecialModel.MinimalDegree
import Mathlib.Tactic

/-!
# Centralizer of the binary Heisenberg action

The fixed space of the diagonal Heisenberg generator is one coordinate line
over the concrete field of four elements. A commuting binary automorphism
therefore takes a chosen nonzero vector to one of its three scalar multiples.
Irreducibility and Schur's lemma show that this determines the automorphism.
Consequently the full linear centralizer is exactly the represented center
of the Heisenberg group, of order three.

This is the centralizer calculation needed for the GL₆(2) normalizer argument
in Aschbacher--Smith, G.9.4(5), printed p.355 (PDF p.366). The only finite
certificate checks vectors in the 64-element module, not linear operators.
-/

@[expose] public section

open Representation Subgroup
namespace Representation.RankTwo.ExtraspecialModel.BinaryAction

/-- The actual restriction of the constructed action to the Heisenberg kernel. -/
abbrev heisenbergRepresentation : Representation (ZMod 2) P V :=
  representation.comp SemidirectProduct.inl

/-- The constructed binary Heisenberg action is irreducible. -/
theorem heisenbergRepresentation_irreducible : IsIrreducible heisenbergRepresentation := by
  let : IsExtraspecial 3 P := HeisenbergPrime.isExtraspecial (by decide)
  apply irreducible_of_faithful_six heisenbergRepresentation
    (representation_injective.comp SemidirectProduct.inl_injective)
  · exact HeisenbergPrime.card
  · exact finrank_vector

private def seed : V := Pi.single 0 1

private theorem seed_ne_zero : seed ≠ 0 := by
  intro h
  have he := congrFun h 0
  simp [seed] at he

private theorem Y_seed : Y seed = seed := by decide +kernel

private theorem Y_fixed_certificate (v : V) (hv : Y v = v) (hne : v ≠ 0) :
    ∃ c : ZMod 3, v = heisenberg ⟨0, 0, c⟩ seed := by
  revert v
  decide +kernel

private theorem central_image_mem (c : ZMod 3) :
    heisenberg ⟨0, 0, c⟩ ∈ centralizer (heisenbergImage : Set (V ≃ₗ[ZMod 2] V)) := by
  rw [heisenbergImage_eq_range]
  apply mem_centralizer_iff.mpr
  rintro _ ⟨p, rfl⟩
  rw [← map_mul, ← map_mul]
  apply congrArg heisenberg
  exact mem_center_iff.mp ((HeisenbergPrime.mem_center_iff _).mpr ⟨rfl, rfl⟩) p

private def centralizerMap
    (g : centralizer (heisenbergImage : Set (V ≃ₗ[ZMod 2] V))) :
    IntertwiningMap heisenbergRepresentation heisenbergRepresentation where
  toLinearMap := g.val.toLinearMap
  isIntertwining' p := by
    have hp : heisenberg p ∈ heisenbergImage := by rw [heisenbergImage_eq_range]; exact ⟨p, rfl⟩
    have he := (mem_centralizer_iff.mp g.property) _ hp
    apply LinearMap.ext
    intro v
    change g.val (linearAction (SemidirectProduct.inl p) v) =
      linearAction (SemidirectProduct.inl p) (g.val v)
    rw [linearAction_inl]
    exact LinearEquiv.congr_fun he.symm v

/-- The full binary linear centralizer is precisely the scalar cubic subgroup. -/
theorem centralizer_heisenbergImage :
    centralizer (heisenbergImage : Set (V ≃ₗ[ZMod 2] V)) =
      (center P).map heisenberg := by
  apply le_antisymm
  · intro g hg
    have hy : Y ∈ heisenbergImage := subset_closure (by simp)
    have hYg : Y (g seed) = g seed := by
      have he := LinearEquiv.congr_fun ((mem_centralizer_iff.mp hg) Y hy) seed
      simpa only [LinearEquiv.mul_apply, Y_seed] using he
    have hne : g seed ≠ 0 := fun he =>
      seed_ne_zero (g.injective (he.trans g.map_zero.symm))
    obtain ⟨c, hc⟩ := Y_fixed_certificate (g seed) hYg hne
    let d := heisenberg (⟨0, 0, c⟩ : P)
    have hd : d ∈ centralizer (heisenbergImage : Set (V ≃ₗ[ZMod 2] V)) := central_image_mem c
    let : IsIrreducible heisenbergRepresentation := heisenbergRepresentation_irreducible
    let f := centralizerMap ⟨g, hg⟩ - centralizerMap ⟨d, hd⟩
    have hf : f seed = 0 := sub_eq_zero.mpr hc
    have hzero : f = 0 := by
      rcases IsIrreducible.injective_or_eq_zero f with hinj | hz
      · exact False.elim (seed_ne_zero (hinj (hf.trans (map_zero f).symm)))
      · exact hz
    have heq : g = d := by
      apply LinearEquiv.toLinearMap_injective
      exact congrArg IntertwiningMap.toLinearMap (sub_eq_zero.mp hzero)
    exact ⟨⟨0, 0, c⟩, (HeisenbergPrime.mem_center_iff _).mpr ⟨rfl, rfl⟩, heq.symm⟩
  · rintro g ⟨p, hp, rfl⟩
    obtain ⟨ha, hb⟩ := (HeisenbergPrime.mem_center_iff p).mp hp
    have he : p = ⟨0, 0, p.c⟩ := by ext <;> simp [ha, hb]
    rw [he]
    exact central_image_mem p.c

/-- In particular the represented Heisenberg group contains its full centralizer. -/
theorem centralizer_heisenbergImage_le :
    centralizer (heisenbergImage : Set (V ≃ₗ[ZMod 2] V)) ≤ heisenbergImage := by
  rw [centralizer_heisenbergImage, heisenbergImage_eq_range]
  rintro _ ⟨p, _, rfl⟩
  exact ⟨p, rfl⟩

/-- The kernel size for the conjugation action of the full linear normalizer. -/
theorem card_centralizer_heisenbergImage :
    Nat.card (centralizer (heisenbergImage : Set (V ≃ₗ[ZMod 2] V))) = 3 := by
  rw [centralizer_heisenbergImage]
  exact (Nat.card_congr ((center P).equivMapOfInjective heisenberg
    heisenberg_injective).toEquiv).symm.trans HeisenbergPrime.card_center

end Representation.RankTwo.ExtraspecialModel.BinaryAction
