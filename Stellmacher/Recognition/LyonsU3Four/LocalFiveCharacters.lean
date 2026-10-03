module

public import Stellmacher.Recognition.LyonsU3Four.LocalFiveDecompositionRows
public import Stellmacher.Recognition.LyonsU3Four.LocalFiveModularSimples
public import Stellmacher.Recognition.LyonsU3Four.LocalFivePrincipalBlock
public import Theory.Character.ModularBlock.Cartan

/-!
# Ordinary and principal-block characters of the supplied Lyons local group

This is the assembly interface for the order-320 semidirect product in Lyons,
*A Characterization of the Group U₃(4)* (1972), Lemmas 2 and 4, pp. 373 and 381.
The complete genuine ordinary table, including the restrictions and cyclic
section identities, is constructed in `LocalFiveOrdinaryTable`. The five
linear, fifteen quartic and three quintic rows exhaust all irreducibles.

All ordinary rows lie in the principal characteristic-two block. The five
modular simples are the reductions of the complement characters, with their
actual eigenvalue-defined Brauer values. Reindexing the ordinary restriction
coefficients therefore constructs genuine principal decomposition data. Its
Cartan matrix is `4 * (3 + δ_jk)`: diagonal 16 and off-diagonal 12. The signed
central-section identities also hold in this genuine Brauer basis.

The ordinary table and both modular transfer results are proved independently;
this module assembles them without an ambient centralizer hypothesis.
-/

public section
noncomputable section

namespace Stellmacher.Recognition.LyonsU3Four

/-- Exactly five genuine linear characters, with principal restriction to S. -/
public theorem exists_five_linear_characters
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (h : SylowStructure S) (β : MulAut S) (hβ : orderOf β = 15)
    (α : FiveComplement →* MulAut S)
    (hα : α (Multiplicative.ofAdd 1) = β ^ (3 : ℕ)) :
    ∃ χ : Fin 5 → ClassFunction (LocalFiveGroup S α),
      (∀ i, IsLinearCharacter (χ i)) ∧ Function.Injective χ ∧
      (∀ φ, IsLinearCharacter φ → ∃ i, χ i = φ) ∧
      (∀ i (s : S), χ i (SemidirectProduct.inl s) = 1) := by
  let e : FiveLinearIndex ≃ Fin 5 := by
    simpa only [fiveLinearIndex_card] using Finite.equivFin FiveLinearIndex
  refine ⟨fun i => localFiveLinearHom S α (e.symm i),
    fun i => localFiveLinear_isLinear S α (e.symm i),
    (localFiveLinear_injective S α).comp e.symm.injective, ?_, ?_⟩
  · intro φ hφ
    obtain ⟨ψ, hψ, _⟩ := localFiveLinear_complete S h β hβ α hα φ hφ
    exact ⟨e ψ, by simpa only [e.symm_apply_apply] using hψ⟩
  · exact fun i s => localFiveLinear_inl S α (e.symm i) s

open scoped BigOperators
open ModularBlock PrincipalBlockConstruction BrauerCoefficientExtension Cartan
attribute [local instance] Fintype.ofFinite Classical.propDecidable

variable {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    {α : FiveComplement →* MulAut S}

/-- The five constructed simple modules form the genuine principal Brauer family. -/
@[expose] def LocalFiveCharacterTable.principalBrauerFamily
    (T : LocalFiveCharacterTable S α) (h : SylowStructure S)
    (d : PrincipalCongruenceBlockData (LocalFiveGroup S α)) : PrincipalBrauerFamily d 5 where
  degree _ := 1
  rep j := localFiveModularRep S α d (fiveLinearEnumeration j)
  irreducible j := localFiveModularRep_irreducible S α d _
  inBlock j := inPrincipalBlock_of_block_eq_univ d (T.block_eq_univ h d) _
  complete m ρ hρ _ := by
    let := hρ
    obtain ⟨χ, hχ⟩ := localFiveModularRep_complete S α d ρ
    exact ⟨fiveLinearEnumeration.symm χ, by simpa using hχ⟩
  independent := (localFiveModularRep_linearIndependent S α d).comp
    fiveLinearEnumeration fiveLinearEnumeration.injective

/-- The Brauer values use the prescribed coefficient datum's eigenvalue lifts. -/
theorem LocalFiveCharacterTable.principalBrauerFamily_value
    (T : LocalFiveCharacterTable S α) (h : SylowStructure S)
    (d : PrincipalCongruenceBlockData (LocalFiveGroup S α))
    (j : Fin 5) (u : LocalFiveGroup S α) :
    BrauerCharacter.value d ((T.principalBrauerFamily h d).rep j) u =
      fiveLinearEnumeration j u.right :=
  localFiveModularRep_value S α d _ u

/-- The ordinary restriction coefficients are the genuine decomposition numbers. -/
@[expose] def LocalFiveCharacterTable.decompositionData
    (T : LocalFiveCharacterTable S α) (h : SylowStructure S)
    (d : PrincipalCongruenceBlockData (LocalFiveGroup S α)) : PrincipalDecompositionData d 5 where
  family := T.principalBrauerFamily h d
  decomposition i j := localFiveDecompositionRow S ((T.blockIndex d).symm i)
    (fiveLinearEnumeration j)
  restriction i _ u hu := by
    obtain ⟨r, rfl⟩ := (T.blockIndex d).surjective i
    simp only [Equiv.symm_apply_apply, T.blockIndex_apply,
      T.principalBrauerFamily_value]
    rw [T.odd_expansion r u hu]
    exact (fiveLinearEnumeration.sum_comp (fun χ =>
      (localFiveDecompositionRow S r χ : ℂ) * χ u.right)).symm

/-- The actual decomposition numbers retain the three ordinary row patterns. -/
@[simp] theorem LocalFiveCharacterTable.decompositionData_row
    (T : LocalFiveCharacterTable S α) (h : SylowStructure S)
    (d : PrincipalCongruenceBlockData (LocalFiveGroup S α))
    (i : LocalFiveRowIndex S) (j : Fin 5) :
    (T.decompositionData h d).decomposition (T.blockIndex d i) j =
      localFiveDecompositionRow S i (fiveLinearEnumeration j) := by
  simp only [decompositionData, Equiv.symm_apply_apply]

/-- All five simple principal-block modules have dimension one. -/
@[simp] theorem LocalFiveCharacterTable.decompositionData_degree
    (T : LocalFiveCharacterTable S α) (h : SylowStructure S)
    (d : PrincipalCongruenceBlockData (LocalFiveGroup S α)) (j : Fin 5) :
    (T.decompositionData h d).family.degree j = 1 := rfl

/-- The principal characteristic-two Cartan matrix has diagonal 16 and off-diagonal 12. -/
theorem LocalFiveCharacterTable.decompositionData_cartan
    (T : LocalFiveCharacterTable S α) (h : SylowStructure S)
    (d : PrincipalCongruenceBlockData (LocalFiveGroup S α)) (j k : Fin 5) :
    (T.decompositionData h d).cartan j k = 4 * (3 + if j = k then 1 else 0) := by
  simp only [PrincipalDecompositionData.cartan, decompositionData, T.block_eq_univ h d]
  rw [(T.blockIndex d).symm.sum_comp (fun i =>
    localFiveDecompositionRow S i (fiveLinearEnumeration j) *
      localFiveDecompositionRow S i (fiveLinearEnumeration k)), localFiveDecompositionRow_gram S h]
  simp only [Equiv.apply_eq_iff_eq]

/-- Lyons' signed cyclic section coefficients expand in the genuine Brauer characters. -/
theorem LocalFiveCharacterTable.brauer_section_expansion
    (T : LocalFiveCharacterTable S α) (h : SylowStructure S)
    (d : PrincipalCongruenceBlockData (LocalFiveGroup S α))
    (w : QuarticCentralIndex S) (i : LocalFiveRowIndex S)
    (u : LocalFiveGroup S α) (hu : Odd (orderOf u)) :
    T.row i (ConjClasses.mk (SemidirectProduct.inl w.1.1 * u)) =
      ∑ j : Fin 5, (localFiveSectionRow S w i (fiveLinearEnumeration j) : ℂ) *
        BrauerCharacter.value d ((T.decompositionData h d).family.rep j) u := by
  simp only [decompositionData, T.principalBrauerFamily_value]
  rw [T.section_expansion h w i u hu]
  exact (fiveLinearEnumeration.sum_comp (fun χ =>
    (localFiveSectionRow S w i χ : ℂ) * χ u.right)).symm

/-- Assemble the ordinary table and its genuine modular Cartan data from the supplied action. -/
theorem exists_localFivePrincipalDecompositionData
    (S : Sylow 2 G) (h : SylowStructure S) (β : MulAut S) (hβ : orderOf β = 15)
    (α : FiveComplement →* MulAut S)
    (hα : α (Multiplicative.ofAdd 1) = β ^ (3 : ℕ))
    (d : PrincipalCongruenceBlockData (LocalFiveGroup S α)) :
    ∃ a : PrincipalDecompositionData d 5,
      (∀ j, a.family.degree j = 1) ∧
      (∀ j u, BrauerCharacter.value d (a.family.rep j) u = fiveLinearEnumeration j u.right) ∧
      (∀ j k, a.cartan j k = 4 * (3 + if j = k then 1 else 0)) := by
  obtain ⟨T⟩ := exists_localFiveCharacterTable S α h β hβ hα
  exact ⟨T.decompositionData h d, T.decompositionData_degree h d,
    T.principalBrauerFamily_value h d, T.decompositionData_cartan h d⟩

end Stellmacher.Recognition.LyonsU3Four
