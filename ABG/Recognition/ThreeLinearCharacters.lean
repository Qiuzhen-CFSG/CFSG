module
public import ABG.Recognition.ThreeCharacterTheory

/-!
# The degree-twelve character in Wong's linear branch

When the group has order 5616, the seven distinguished irreducible characters
have degrees 26, 27, 26, 26, 39, 12, 13. Every other nontrivial irreducible has
degree divisible by 16, so χ₆ is the unique irreducible character of degree 12.
Its irreducibility witness supplies an actual representation on `Fin 12 → ℂ`.
The final data package retains this representation and the original catalog,
including the restriction of χ₆ to roots of the distinguished involution.

Source: W. J. Wong, “On finite groups whose 2-Sylow subgroups have cyclic
subgroups of index 2” (1964), §4(b), p.103, and Appendix (b), pp.108–109,
DOI 10.1017/S1446788700022771.
-/

namespace ABG
open BenderGlauberman
noncomputable section

namespace ThreeGlobalDegreeData

variable {G : Type*} [Group G] [Finite G] (c : ThreeGlobalDegreeData G)

/-- The order selects the linear branch of the shared character catalog. -/
public theorem linear_degrees (hG : Nat.card G = 5616) :
    c.decomposition.degree = ![26,27,26,26,39,12,13] := by
  rcases c.degree_alternatives with ⟨_, h⟩ | ⟨h, _⟩
  · omega
  · exact h

/-- Wong's χ₆ (index 5) has degree twelve in the linear branch. -/
public theorem sixth_degree_twelve (hG : Nat.card G = 5616) :
    c.decomposition.χ 5 1 = 12 := by
  rw [c.decomposition.degree_eq, c.linear_degrees hG]
  change ((12 : ℕ) : ℂ) = 12
  norm_num

/-- No other irreducible character has degree twelve. Characters outside the
catalog are excluded by divisibility by sixteen. -/
public theorem degree_twelve_unique (hG : Nat.card G = 5616)
    {θ : ClassFunction G} (hθ : IsIrreducibleCharacter θ) (hdegree : θ 1 = 12) :
    θ = c.decomposition.χ 5 := by
  classical
  have h1 : θ ≠ 1 := by
    intro h
    simp [h] at hdegree
  by_cases hmem : ∃ i, θ = c.decomposition.χ i
  · obtain ⟨i, rfl⟩ := hmem
    rw [c.decomposition.degree_eq, c.linear_degrees hG] at hdegree
    fin_cases i <;> simp_all [Matrix.cons_val]
  · obtain ⟨n, hn, hdvd⟩ := c.remaining_degree θ hθ h1
      (fun i hi => hmem ⟨i, hi⟩)
    have hn12 : n = 12 := by exact_mod_cast hn.symm.trans hdegree
    omega

/-- Every nonprincipal irreducible other than χ₆ has degree at least thirteen.
This is the degree obstruction used for the thirteen-coset permutation character. -/
public theorem linear_degree_ge_thirteen_of_ne_sixth (hG : Nat.card G = 5616)
    {θ : ClassFunction G} (hθ : IsIrreducibleCharacter θ) (h1 : θ ≠ 1)
    (h6 : θ ≠ c.decomposition.χ 5) : 13 ≤ (θ 1).re := by
  classical
  by_cases hmem : ∃ i, θ = c.decomposition.χ i
  · obtain ⟨i, rfl⟩ := hmem
    have hi : i ≠ 5 := fun h => h6 (congrArg c.decomposition.χ h)
    rw [c.decomposition.degree_eq, c.linear_degrees hG]
    fin_cases i <;> simp_all [Matrix.cons_val] <;> norm_num
  · obtain ⟨n, hn, hdvd⟩ := c.remaining_degree θ hθ h1
      (fun i hi => hmem ⟨i, hi⟩)
    have hpos := irreducible_degree_ge_one hθ
    rw [hn] at hpos ⊢
    have hnpos : 0 < n := by
      have : 1 ≤ n := by exact_mod_cast hpos
      omega
    have hlarge : 16 ≤ n := Nat.le_of_dvd hnpos hdvd
    have hn13 : 13 ≤ n := by omega
    exact_mod_cast hn13

include c in
/-- Every nonprincipal irreducible has degree at least twelve. -/
public theorem linear_degree_ge_twelve (hG : Nat.card G = 5616)
    {θ : ClassFunction G} (hθ : IsIrreducibleCharacter θ) (h1 : θ ≠ 1) :
    12 ≤ (θ 1).re := by
  by_cases h6 : θ = c.decomposition.χ 5
  · rw [h6, c.sixth_degree_twelve hG]
    norm_num
  · have h := c.linear_degree_ge_thirteen_of_ne_sixth hG hθ h1 h6
    linarith

include c in
/-- Existence and uniqueness are statements about genuine irreducible
characters, rather than only the seven entries of the catalog. -/
public theorem existsUnique_degree_twelve (hG : Nat.card G = 5616) :
    ∃! θ : ClassFunction G, IsIrreducibleCharacter θ ∧ θ 1 = 12 := by
  exact ⟨c.decomposition.χ 5,
    ⟨c.decomposition.irreducible 5, c.sixth_degree_twelve hG⟩,
    fun _ hθ => c.degree_twelve_unique hG hθ.1 hθ.2⟩

/-- An actual twelve-dimensional irreducible representation affording the
same χ₆ that occurs in the induction identities and Appendix restrictions. -/
public theorem exists_sixth_representation (hG : Nat.card G = 5616) :
    ∃ ρ : Representation ℂ G (Fin 12 → ℂ),
      Representation.IsIrreducible ρ ∧ c.decomposition.χ 5 = ρ.character := by
  obtain ⟨n, ρ, hρ, hχ⟩ := c.decomposition.irreducible 5
  have hn : n = 12 := by
    have h := c.sixth_degree_twelve hG
    rw [hχ, Representation.char_one] at h
    simp only [Module.finrank_pi, Fintype.card_fin] at h
    exact_mod_cast h
  subst n
  exact ⟨ρ, hρ, hχ⟩

end ThreeGlobalDegreeData

/-- The linear branch retains the seven-character catalog and an actual
irreducible representation affording its sixth character. -/
public structure ThreeLinearCharacterData (G : Type*) [Group G] [Finite G]
    extends ThreeGlobalDegreeData G where
  group_order : Nat.card G = 5616
  sixthRepresentation : Representation ℂ G (Fin 12 → ℂ)
  sixthRepresentation_irreducible : Representation.IsIrreducible sixthRepresentation
  sixthRepresentation_character : decomposition.χ 5 = sixthRepresentation.character

/-- Degree-twelve uniqueness for the packaged linear-branch witnesses. -/
public theorem ThreeLinearCharacterData.degree_twelve_unique
    {G : Type*} [Group G] [Finite G] (c : ThreeLinearCharacterData G)
    {θ : ClassFunction G} (hθ : IsIrreducibleCharacter θ) (hdegree : θ 1 = 12) :
    θ = c.sixthRepresentation.character :=
  (c.toThreeGlobalDegreeData.degree_twelve_unique c.group_order hθ hdegree).trans
    c.sixthRepresentation_character

/-- Assemble the actual representation and the catalog from the original
local group hypotheses in the order-5616 branch. -/
public theorem exists_threeLinearCharacterData
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S) (hcard : Nat.card S = 16)
    (hC : ∀ t : G, orderOf t = 2 →
      Subgroup.centralizer ({t} : Set G) ≃* GL2 3 1)
    (hG : Nat.card G = 5616) : Nonempty (ThreeLinearCharacterData G) := by
  obtain ⟨c⟩ := exists_threeCharacterTheory S hS hcard hC
  obtain ⟨ρ, hρ, hχ⟩ := c.exists_sixth_representation hG
  exact ⟨{
    toThreeGlobalDegreeData := c
    group_order := hG
    sixthRepresentation := ρ
    sixthRepresentation_irreducible := hρ
    sixthRepresentation_character := hχ }⟩

end
end ABG
