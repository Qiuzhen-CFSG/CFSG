module
public import ABG.Recognition.ThreeQuotientCyclicSections

/-!
# The induced principal-block section bridge

For an arbitrary ambient principal congruence two-block and an involution
centralizer with odd-core quotient GL₂(3), Wong's one shared induced catalog
supplies eight distinct actual block rows, the compatible degree-three local
row, rationality of the first five rows, and both signed section formulas.
The odd core and the prescribed modular place are retained throughout.

This bundles the proved membership, rationality, involution, and cyclic-section
results for the semidihedral principal-section constructor. It neither resolves
the three odd-degree signs nor asserts exhaustion of the ambient block; these
are separate obligations of the downstream construction.

Source: Alperin--Brauer--Gorenstein III.5--6 and III.2 Propositions 1--4;
Wong (1964), Table 1 and equation (3).
-/

namespace ABG
open BenderGlauberman ModularBlock.PrincipalBlockConstruction
open ModularBlock.CompatibleBrauerBlock
noncomputable section
attribute [local instance] Fintype.ofFinite Classical.propDecidable

variable {G : Type*} [Group G] [Finite G] (x : G)
local notation "C" => Subgroup.centralizer (Set.singleton x)

/-- One actual ambient block embedding, local row, and pair of section witnesses
for the same supplied induced-character catalog and prescribed modular place. -/
public theorem threeQuotient_principalBlock_sections
    (hx : orderOf x = 2)
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1)
    (d : ThreeCharacterDecomposition (threeQuotientInducedGenerator x e))
    (b : PrincipalCongruenceBlockData G) :
    ∃ row : Fin 8 ↪ {i : b.I // i ∈ b.block},
      (row 0).val = b.principal ∧
      (∀ i : Fin 8, b.chi (row i).val = d.principalConjCandidate i) ∧
      (∀ (i : Fin 5) (g : G), ∃ q : ℚ,
        b.chi (row ⟨i.val, by omega⟩).val (ConjClasses.mk g) = (q : ℂ)) ∧
      ∃ localRow : (localData b C).I,
        localRow ∈ (localData b C).block ∧
        (localData b C).chi localRow = threeOddCoreCharacter e 3 ∧
        (localData b C).chi localRow (ConjClasses.mk 1) = 3 ∧
        (∀ (r : C), Odd (orderOf r) → ∀ i : Fin 8,
          b.chi (row i).val (ConjClasses.mk (x * (r : G))) =
            threeSignedPrincipalInvolutionSection ![-d.sign 0,-d.sign 3,-d.sign 1]
              ((localData b C).chi localRow (ConjClasses.mk r)) i) ∧
        ∃ u : G, orderOf u = 8 ∧ u^4 = x ∧
          ∃ ζ : ℂ, IsPrimitiveRoot ζ 8 ∧
            ∀ (h : ℤ), ¬ 4 ∣ h →
              ∀ (r : Subgroup.centralizer ({u^h} : Set G)), Odd (orderOf r) →
                ∀ i : Fin 8, b.chi (row i).val (ConjClasses.mk (u^h * (r : G))) =
                  threeSignedPrincipalCyclicSection ![-d.sign 0,-d.sign 3,-d.sign 1] ζ h i := by
  choose f hf he using threeQuotient_principalConjCandidate_mem x e d b hx
  let row : Fin 8 ↪ {i : b.I // i ∈ b.block} := {
    toFun := fun i => ⟨f i, hf i⟩
    inj' := by
      intro i j hij
      apply d.principalConjCandidate_injective
      rw [← he i, ← he j]
      exact congrArg b.chi (congrArg Subtype.val hij) }
  have hrow (i : Fin 8) : b.chi (row i).val = d.principalConjCandidate i := he i
  refine ⟨row, ?_, hrow, ?_, ?_⟩
  · apply b.complete.2.2
    rw [hrow, b.principal_eq]
    funext c
    obtain ⟨g, rfl⟩ := ConjClasses.exists_rep c
    rfl
  · intro i g
    rw [hrow]
    exact threeQuotient_principalConjCandidate_rational x e d i g
  · obtain ⟨k, hk, hke, hkd⟩ :=
      threeOddCore_principalBlock_exists_degree_three e (localData b C)
    refine ⟨k, hk, hke, hkd, ?_, ?_⟩
    · intro r hr i
      rw [hrow, hke]
      exact threeQuotient_principalCandidate_involution_section x e d b hx r hr i
    · obtain ⟨u, hu, hfour, ζ, hζ, hsec⟩ :=
        threeQuotient_principalCandidate_exists_cyclic_sections x e d b hx
      refine ⟨u, hu, hfour, ζ, hζ, ?_⟩
      intro h hh r hr i
      rw [hrow]
      exact hsec h hh r hr i

end
end ABG
