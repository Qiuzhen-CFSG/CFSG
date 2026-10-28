module

public import CFSG.Quasithin.ChapterH.Section01To04.L3Four.CubicSpectrum
public import CFSG.Quasithin.ChapterH.Section01To04.L3Four.CubicSpectrum.WordRanks
public import CFSG.Quasithin.ChapterH.Section01To04.L3Four.CubicSpectrum.ProjectiveEigenbasis
public import CFSG.Quasithin.ChapterH.Section01To04.L3Four.CubicSpectrum.ProjectiveEigenbasis.NaturalSpectrum
public import CFSG.Quasithin.ChapterH.Section01To04.L3Four.InvertedCubic
public import Theory.SpecificGroups.PSL3Four.InvolutionNormalForms.Graph
public import Theory.SpecificGroups.PSL3Four.GraphFieldMarking
public import Theory.Representation.BinaryPrimeDisplacement

/-!
# Cubic and involution displacement for the actual PSL₃(4) component

A projective cubic has three distinct natural eigenvalues. The two adjoint
factors therefore have displacement ranks six and their tensor product has
rank forty-two. Descent through the actual Schur field makes the non-nine
binary ranks twelve or forty-two.

Every ambient involution inverts a cubic in the genuine generalized Fitting
subgroup. The graph and graph–field normal forms supply the remaining cases
of that assertion. The commutator displacement inequality then gives rank
at least six for the original involution. No spectral calculation or
conjugacy normal form remains an input to the exported bounds.

Source: Aschbacher–Smith H.4.7, refs/quasithin.pdf, printed pp.382–383.
This supplies its displacement lower bound for the exceptional L₃(4) branch
of 5.1.14; the nine-dimensional exclusion and equality analysis are separate.
-/

public section

open scoped MatrixGroups
open Representation Representation.SL3.BinaryDefiningFactors Theory.GroupTheory
namespace CFSG.Quasithin.ChapterH.Section01To04.L3Four.CubicSpectrum

variable {F K : Type*} [Field F] [Field K] [Finite F] [CharP F 2]
  [IsAlgClosed K] [CharP K 2]

/-- Absolute displacement ranks on the three surviving adjoint words. -/
theorem projective_cubic_word_ranks (hcard : Nat.card F = 4)
    (ι : F →+* K) (g : SL(3,F))
    (hg : orderOf (QuotientGroup.mk' (Subgroup.center SL(3,F)) g) = 3) :
    Module.finrank K (LinearMap.range (wordRep ι [.adjoint,.trivial] g - 1)) = 6 ∧
    Module.finrank K (LinearMap.range (wordRep ι [.trivial,.adjoint] g - 1)) = 6 ∧
    Module.finrank K (LinearMap.range (wordRep ι [.adjoint,.adjoint] g - 1)) = 42 := by
  obtain ⟨ω, hω, ⟨b⟩, ⟨c⟩⟩ := paired_adjointCubicEigenbasis_of_natural ι g
    (fun η ω hω => projective_cubic_natural_eigenbasis hcard η g hg ω hω)
  exact word_ranks_of_adjointCubicEigenbases ι g ω hω b c

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The exact non-nine binary displacement alternatives for a projective cubic. -/
theorem binary_projective_cubic_displacement
    (ρ : Representation (ZMod 2) SL(3,F) V) [IsIrreducible ρ]
    (hcard : Nat.card F = 4)
    (hcenter : Subgroup.center SL(3,F) ≤ ρ.ker) (hact : ∃ g, ρ g ≠ 1)
    (hdim : Module.finrank (ZMod 2) V ≠ 9) (g : SL(3,F))
    (hg : orderOf (QuotientGroup.mk' (Subgroup.center SL(3,F)) g) = 3) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ g - 1)) = 12 ∨
      Module.finrank (ZMod 2) (LinearMap.range (ρ g - 1)) = 42 := by
  exact binary_displacement_of_word_ranks ρ hcard hcenter hact hdim g
    (fun ι => projective_cubic_word_ranks hcard ι g hg)

variable {M : Type*} [Group M]

/-- A cubic in the actual generalized Fitting subgroup moves at least twelve
binary dimensions in the original faithful non-nine action. -/
theorem source_psl3Four_cubic_displacement
    (e : Matrix.PSL3Four.PSL ≃* generalizedFitting M)
    (ρ : Representation (ZMod 2) M V)
    [IsIrreducible (ρ.comp (generalizedFitting M).subtype)] (hρ : Function.Injective ρ)
    (hdim : Module.finrank (ZMod 2) V ≠ 9)
    (x : M) (hx : x ∈ generalizedFitting M) (horder : orderOf x = 3) :
    12 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ x - 1)) := by
  exact source_psl3Four_cubic_displacement_of_word_ranks e ρ hρ hdim
    (fun g hg ι => projective_cubic_word_ranks Matrix.PSL3Four.card_F ι g hg)
    x hx horder

end CFSG.Quasithin.ChapterH.Section01To04.L3Four.CubicSpectrum

namespace CFSG.Quasithin.ChapterH.Section01To04.L3Four.InvertedCubic
open Matrix Matrix.PSL3Four Matrix.PSL3.OuterSolvable

private theorem graphField_involution_conjugate (m : GL (Fin 3) F)
    (hm : (linearConj F m * pslFrobenius * graph F) ^ 2 = 1) :
    ∃ d : MulAut PSL, MulAut.congr d (linearConj F m * pslFrobenius * graph F) =
      pslFrobenius * graph F := by
  have hne : fieldFrobenius ≠ 1 := by
    intro he
    obtain ⟨x, hx⟩ := exists_fieldFrobenius_ne
    exact hx (by rw [he]; rfl)
  rw [← fieldAction_frobenius] at hm ⊢
  obtain ⟨d, hd⟩ := GraphFieldMarking.linear_conjugate card_F m fieldFrobenius hne hm
  exact ⟨linearConj F d, hd⟩

variable {M : Type*} [Group M] [Finite M]

/-- Every ambient involution inverts a cubic in the literal PSL₃(4) component. -/
theorem exists_inverted_cubic (e : PSL ≃* generalizedFitting M)
    (t : M) (ht : orderOf t = 2) :
    ∃ y : generalizedFitting M, orderOf y = 3 ∧
      t * (y : M) * t⁻¹ = (y : M)⁻¹ :=
  exists_inverted_cubic_of_graph_conjugacy
    InvolutionNormalForms.graph_involution_conjugate
    graphField_involution_conjugate e t ht

end CFSG.Quasithin.ChapterH.Section01To04.L3Four.InvertedCubic

namespace CFSG.Quasithin.ChapterH.Section01To04.L3Four
open Representation.BinaryOffender

variable {M V : Type*} [Group M] [Finite M] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The non-nine H.4.7 involution displacement lower bound, with every
spectral and group-theoretic auxiliary premise discharged. -/
theorem source_psl3Four_involution_displacement
    (e : Matrix.PSL3Four.PSL ≃* generalizedFitting M)
    (ρ : Representation (ZMod 2) M V)
    [IsIrreducible (ρ.comp (generalizedFitting M).subtype)] (hρ : Function.Injective ρ)
    (hdim : Module.finrank (ZMod 2) V ≠ 9)
    (t : M) (ht : orderOf t = 2) :
    6 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) := by
  obtain ⟨y, hy, hty⟩ := InvertedCubic.exists_inverted_cubic e t ht
  have horder : orderOf (y : M) = 3 := (Subgroup.orderOf_coe y).trans hy
  have hlow := CubicSpectrum.source_psl3Four_cubic_displacement e ρ hρ hdim
    y y.property horder
  have hupper := fixedCodim_three_le_twice_of_inverted ρ (y : M) t horder hty
  simp only [fixedCodim_zpowers_eq_displacement_rank, Module.End.one_eq_id] at hlow hupper ⊢
  omega

end CFSG.Quasithin.ChapterH.Section01To04.L3Four
