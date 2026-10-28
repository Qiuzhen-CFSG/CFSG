module

public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.CharacterGeometry.Decomposition

/-!
# The norm character of an elementary eight

Every character space is a line, and every nonzero scalar in `𝔽₃` has square
one. Thus the norm of a nonzero vector depends only on its character line.
Composition of norms makes these eight values a multiplicative character of
the character group. This is the invariant used to distinguish the two Cayley
frames; no conjugacy or multiplication-table theorem is assumed here.

Application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Theorem 0.1.2(4), printed pp.3–4 and 481–482. Coordinates and norm follow the
licensed ATLAS port; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section
namespace Atlas.G2.TernaryLocals.CharacterGeometry.EightConjugacy
open Atlas.SplitOctonion

/-- Nonzero vectors of one character line have the same norm over `𝔽₃`. -/
theorem norm_eq_of_same_character (E : Subgroup G) [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) {χ : Character E} {x y : V}
    (hx : x ∈ characterSpace E χ) (hx0 : x ≠ 0)
    (hy : y ∈ characterSpace E χ) (hy0 : y ≠ 0) : norm x = norm y := by
  obtain ⟨r, hr⟩ := exists_smul_eq_of_finrank_eq_one
    (finrank_of_card_eight E hE χ)
    (show (⟨x, hx⟩ : characterSpace E χ) ≠ 0 from fun h => hx0 (congrArg Subtype.val h))
    (⟨y, hy⟩ : characterSpace E χ)
  have he : r • x = y := congrArg Subtype.val hr
  have hr0 : r ≠ 0 := by
    intro hz
    apply hy0
    simpa [hz] using he.symm
  have hs : r^2 = 1 := (by decide : ∀ r : ZMod 3, r ≠ 0 → r^2 = 1) r hr0
  rw [← he, norm_smul, hs, one_mul]

/-- Every nonzero vector of a character line is nonisotropic. -/
theorem norm_ne_zero_of_mem (E : Subgroup G) [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) {χ : Character E} {x : V}
    (hx : x ∈ characterSpace E χ) (hx0 : x ≠ 0) : norm x ≠ 0 := by
  obtain ⟨v, hv, hn⟩ := exists_nonisotropic E χ
  have hv0 : v ≠ 0 := by intro h; apply hn; simp [h, norm]
  rw [norm_eq_of_same_character E hE hx hx0 hv hv0]
  exact hn

private noncomputable def normVector (E : Subgroup G) [IsElementaryAbelian 2 E]
    (χ : Character E) : V := (exists_nonisotropic E χ).choose

private theorem normVector_mem (E : Subgroup G) [IsElementaryAbelian 2 E]
    (χ : Character E) : normVector E χ ∈ characterSpace E χ :=
  (exists_nonisotropic E χ).choose_spec.1

private theorem normVector_norm_ne (E : Subgroup G) [IsElementaryAbelian 2 E]
    (χ : Character E) : norm (normVector E χ) ≠ 0 :=
  (exists_nonisotropic E χ).choose_spec.2

private theorem normVector_ne (E : Subgroup G) [IsElementaryAbelian 2 E]
    (χ : Character E) : normVector E χ ≠ 0 := by
  intro h
  apply normVector_norm_ne E χ
  simp [h, norm]

/-- The norm on homogeneous lines, as a character of the actual character group. -/
noncomputable def lineNorm (E : Subgroup G) [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) : Character E →* (ZMod 3)ˣ where
  toFun χ := Units.mk0 (norm (normVector E χ)) (normVector_norm_ne E χ)
  map_one' := by
    apply Units.ext
    change norm (normVector E 1) = 1
    exact (norm_eq_of_same_character E hE (normVector_mem E 1) (normVector_ne E 1)
      (unit_mem E) unit_ne_zero).trans (by rfl)
  map_mul' χ ψ := by
    apply Units.ext
    change norm (normVector E (χ * ψ)) = norm (normVector E χ) * norm (normVector E ψ)
    rw [← norm_mul]
    apply norm_eq_of_same_character E hE (normVector_mem E _) (normVector_ne E _)
      (mul_mem (normVector_mem E χ) (normVector_mem E ψ))
    intro hz
    have hn : norm (mul (normVector E χ) (normVector E ψ)) ≠ 0 := by
      rw [norm_mul]
      exact mul_ne_zero (normVector_norm_ne E χ) (normVector_norm_ne E ψ)
    apply hn
    simp [hz, norm]

/-- Any nonzero homogeneous vector computes the norm character. -/
theorem lineNorm_apply (E : Subgroup G) [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) {χ : Character E} {x : V}
    (hx : x ∈ characterSpace E χ) (hx0 : x ≠ 0) :
    (lineNorm E hE χ : ZMod 3) = norm x :=
  norm_eq_of_same_character E hE (normVector_mem E χ) (normVector_ne E χ) hx hx0

end Atlas.G2.TernaryLocals.CharacterGeometry.EightConjugacy
