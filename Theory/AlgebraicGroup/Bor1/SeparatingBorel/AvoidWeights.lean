module

public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.Cocharacters
/-!
# Cocharacters avoiding a finite set of weights

The integral finite-avoidance result also works without prescribed signs.
Embed the lattice as a direct summand after adding two free coordinates and
apply the proved separating-functional theorem to those auxiliary coordinates.
Restricting the functional back avoids every original nonzero character.
Torus duality realizes it by an actual cocharacter.

This supplies a generic parameter before the two rank-one endpoint characters
have been oriented, as required in Borel, *Linear Algebraic Groups*, IV,
13.2--13.3 and 13.11(3).
-/

public section
namespace Theory.AlgebraicGroup.Bor1.SeparatingBorel
variable {M : Type*} [AddCommGroup M] [Module.Free ℤ M]

theorem exists_integral_dual_avoiding (s : Finset M) (hs : ∀ x ∈ s, x ≠ 0) :
    ∃ φ : Module.Dual ℤ M, ∀ x ∈ s, φ x ≠ 0 := by
  classical
  let α : M × (ℤ × ℤ) := (0, (1, 0))
  let β : M × (ℤ × ℤ) := (0, (0, 1))
  have hi : LinearIndependent ℤ ![α, β] := by
    apply LinearIndependent.pair_iff.mpr
    intro a b hab
    constructor
    · have h := congrArg (fun z : M × (ℤ × ℤ) => z.2.1) hab
      simpa [α, β] using h
    · have h := congrArg (fun z : M × (ℤ × ℤ) => z.2.2) hab
      simpa [α, β] using h
  let i : M →ₗ[ℤ] M × (ℤ × ℤ) := LinearMap.inl ℤ M (ℤ × ℤ)
  obtain ⟨φ, _, _, hf⟩ := exists_integral_separating_regular_dual hi (s.image i) (by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    intro he
    apply hs x hx
    exact congrArg Prod.fst he)
  refine ⟨φ.comp i, ?_⟩
  intro x hx
  exact hf (i x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)

variable {k : Type*} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

theorem exists_cocharacter_avoiding_weights (T : ClosedSubgroup G) (hT : IsSubtorus T)
    (s : Finset (TorusWeight T)) (hs : ∀ χ ∈ s, χ ≠ 1) :
    ∃ c : ClosedSubgroupTorusCocharacter T,
      ∀ χ ∈ s, characterCocharacterPairing T c (Additive.ofMul χ) ≠ 0 := by
  classical
  obtain ⟨n, ⟨e⟩⟩ := hT
  let : Module.Free ℤ (Additive (TorusWeight T)) := torus_character_free_of_iso n e
  obtain ⟨φ, hφ⟩ := exists_integral_dual_avoiding (s.image Additive.ofMul) (by
    intro x hx
    obtain ⟨χ, hχ, rfl⟩ := Finset.mem_image.mp hx
    exact hs χ hχ)
  obtain ⟨c, hc⟩ := exists_cocharacter_realizing_characterFunctional T ⟨n, ⟨e⟩⟩ φ.toAddMonoidHom
  refine ⟨c, ?_⟩
  intro χ hχ
  have he : characterCocharacterPairing T c (Additive.ofMul χ) = φ (Additive.ofMul χ) :=
    (weightCocharacterEquation_existsUnique T χ c).unique
      (characterCocharacterPairing_spec T χ c) (hc χ)
  rw [he]
  exact hφ _ (Finset.mem_image.mpr ⟨χ, hχ, rfl⟩)
theorem exists_cocharacter_separating_finite_weights (T : ClosedSubgroup G) (hT : IsSubtorus T)
    (s : Finset (TorusWeight T)) :
    ∃ c : ClosedSubgroupTorusCocharacter T,
      ∀ χ ∈ s, ∀ ψ ∈ s, χ ≠ ψ →
        characterCocharacterPairing T c (Additive.ofMul χ) ≠
          characterCocharacterPairing T c (Additive.ofMul ψ) := by
  classical
  let P := (s.product s).filter (fun p => p.1 ≠ p.2)
  let D := P.image (fun p => p.1 * p.2⁻¹)
  have hD : ∀ δ ∈ D, δ ≠ 1 := by
    intro δ hδ
    obtain ⟨⟨χ, ψ⟩, hp, rfl⟩ := Finset.mem_image.mp hδ
    exact fun he => (Finset.mem_filter.mp hp).2 (mul_inv_eq_one.mp he)
  obtain ⟨c, hc⟩ := exists_cocharacter_avoiding_weights T hT D hD
  refine ⟨c, ?_⟩
  intro χ hχ ψ hψ hne
  have hd : χ * ψ⁻¹ ∈ D := Finset.mem_image.mpr
    ⟨(χ, ψ), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hχ, hψ⟩, hne⟩, rfl⟩
  have h := hc _ hd
  change characterCocharacterPairing T c (Additive.ofMul χ - Additive.ofMul ψ) ≠ 0 at h
  rwa [map_sub, sub_ne_zero] at h

end Theory.AlgebraicGroup.Bor1.SeparatingBorel
