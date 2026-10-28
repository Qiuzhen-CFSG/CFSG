module

public import Theory.Representation.SymplecticFourOrthogonalCover.SylowFlag.Conjugation

/-!
# The selected derived-Sylow flag in the orthogonal five-space

Every actual Sylow two-subgroup of Sp₄(K)′ is conjugate to the literal
intersection of the standard unipotent subgroup with Sp₄(K)′. The same
conjugation identifies its unique invariant natural line and plane. The first
preimage is its fixed two-space, with a unique singular projective point
complementing the radical. Both selected natural subspaces are isotropic.

Source: Aschbacher–Smith, I.2.3(1a),(2), printed p.413 / PDF p.424.
Binary stabilizer irreducibility and the original ambient-action assembly are
separate obligations; this module asserts the proved flag and cover geometry.
-/

@[expose] public section
noncomputable section

open Representation.OneCohomology ClassicalOrthogonal
namespace Representation.SymplecticFourOrthogonalCover.SylowFlag
variable {K : Type*} [Field K] [Finite K] [CharP K 2]

/-- Existence and uniqueness of the source's invariant natural flag, including F₂. -/
theorem exists_unique_flag (S : Sylow 2 (L (K := K))) :
    ∃ g : L (K := K), (S : Subgroup (L (K := K))) = movedSylow g ∧
      Module.finrank K (movedLine g) = 1 ∧ Module.finrank K (movedPlane g) = 2 ∧
      (∀ t : (S : Subgroup (L (K := K))), movedLine g ≤
        (movedLine g).comap (symplecticDerivedNatural 2 t.val)) ∧
      (∀ t : (S : Subgroup (L (K := K))), movedPlane g ≤
        (movedPlane g).comap (symplecticDerivedNatural 2 t.val)) ∧
      (∀ W : Submodule K (Natural (K := K)),
        (∀ t : (S : Subgroup (L (K := K))), W ≤ W.comap (symplecticDerivedNatural 2 t.val)) →
        Module.finrank K W = 1 → W = movedLine g) ∧
      (∀ W : Submodule K (Natural (K := K)),
        (∀ t : (S : Subgroup (L (K := K))), W ≤ W.comap (symplecticDerivedNatural 2 t.val)) →
        Module.finrank K W = 2 → W = movedPlane g) := by
  obtain ⟨g,hg⟩ := exists_marking S
  refine ⟨g,hg,movedLine_finrank g,movedPlane_finrank g,?_,?_,?_,?_⟩
  all_goals rw [hg]
  · exact movedLine_invariant g
  · exact movedPlane_invariant g
  · exact movedLine_unique g
  · exact movedPlane_unique g

/-- The geometry of any source-selected flag, with no conjugation or geometry premise. -/
theorem selected_flag_geometry (S : Sylow 2 (L (K := K)))
    (V1 V2 : Submodule K (Natural (K := K)))
    (h1 : ∀ t : (S : Subgroup (L (K := K))), V1 ≤ V1.comap (symplecticDerivedNatural 2 t.val))
    (d1 : Module.finrank K V1 = 1)
    (h2 : ∀ t : (S : Subgroup (L (K := K))), V2 ≤ V2.comap (symplecticDerivedNatural 2 t.val))
    (d2 : Module.finrank K V2 = 2) :
    ∃ g : L (K := K),
      (S : Subgroup (L (K := K))) = movedSylow g ∧
      V1 = movedLine g ∧ V2 = movedPlane g ∧ V1 ≤ V2 ∧
      (∀ x ∈ V1, ∀ y ∈ V1, (formD 2 K).polarBilin x y = 0) ∧
      (∀ x ∈ V2, ∀ y ∈ V2, (formD 2 K).polarBilin x y = 0) ∧
      V1.comap projection.toLinearMap = fixed ((action (K := K)).comp (S : Subgroup (L (K := K))).subtype) ∧
      Module.finrank K (V1.comap projection.toLinearMap) = 2 ∧
      V1.comap projection.toLinearMap = movedPoint g ⊔ radical ∧
      Disjoint (movedPoint g) radical ∧ Module.finrank K (movedPoint g) = 1 ∧
      (∀ x ∈ movedPoint g, formB 2 K x = 0) ∧
      (∀ P : Submodule K (Space (K := K)), P ≤ V1.comap projection.toLinearMap →
        Module.finrank K P = 1 → (∀ x ∈ P, formB 2 K x = 0) → P = movedPoint g) ∧
      movedRoot g ≤ (Subgroup.center (S : Subgroup (L (K := K)))).map (S : Subgroup (L (K := K))).subtype := by
  obtain ⟨g,hg⟩ := exists_marking S
  have e1 : V1 = movedLine g := movedLine_unique g V1 (hg ▸ h1) d1
  have e2 : V2 = movedPlane g := movedPlane_unique g V2 (hg ▸ h2) d2
  refine ⟨g,hg,e1,e2,?_,?_,?_,?_,?_,?_,movedPoint_disjoint g,
    movedPoint_finrank g,movedPoint_singular g,?_,?_⟩
  · rw [e1,e2]
    exact movedLine_le_plane g
  · rw [e1]
    exact fun x hx y hy => movedLine_isotropic g x y hx hy
  · rw [e2]
    exact fun x hx y hy => movedPlane_isotropic g x y hx hy
  · rw [hg,e1]
    exact (moved_cover_fixed g).symm
  · rw [e1]
    exact moved_preimage_finrank g
  · rw [e1]
    exact movedLine_preimage g
  · rw [e1]
    exact moved_singular_unique g
  · rw [hg]
    exact movedRoot_central g

end Representation.SymplecticFourOrthogonalCover.SylowFlag
