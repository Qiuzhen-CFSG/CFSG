module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.ExtensionControl.Head
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.ExtensionControl.DualExclusion
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.ExtensionControl.SelfExtensions

/-!
# Extension control for binary SL₃(2) FF-modules

Full commutator generation and an offender give dimension at most six. The
irreducible catalogue then supplies a natural head with either the full fixed
space as kernel or a second natural factor as kernel. The displacement-counting
argument excludes opposite orientations, even in nonsplit extensions.
Thus one-copy quotient coordinates are constructed, or both factors carry
one common explicit marking of the natural matrix representation.

In the latter case, `SelfExtensions` constructs an equivariant complement by
correcting a linear section with an inner matrix derivation. The final theorem
`exists_moduleQuotient` therefore supplies a surjective equivariant map onto
one or two copies of the natural module, with kernel exactly the fixed space
and one common marking. It has no additional splitting premise.

Source: the binary specialization of Aschbacher–Smith B.4.9(2)(i),(ii),
printed pp.92,94, and B.5.1, pp.99–101, used by C.1.34, pp.136–137
(combined manuscript, 1 March 2004). The dimension reduction avoids any
need for the full B.4.8 classification of four-dimensional indecomposables.
-/

public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.QuotientRecognition.ExtensionControl

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) SL V)

/-- Every faithful full-commutator binary SL₃(2) FF-module either already has
one-copy quotient coordinates, or is an extension of two natural modules
with the same explicit marking. No splitting assertion is hidden here. -/
theorem one_copy_or_homogeneous_extension
    (hρ : Function.Injective ρ) (hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤)
    (hFF : IsFFModule ρ) :
    Nonempty (ModuleQuotient ρ 1) ∨
      ∃ (N : Subrepresentation ρ) (a : SL ≃* SL),
        Nonempty (N.toRepresentation.Equiv (BinaryLinearThree.W.comp a.toMonoidHom)) ∧
        Nonempty (N.quotientRepresentation.Equiv (BinaryLinearThree.W.comp a.toMonoidHom)) := by
  rcases subsingleton_or_nontrivial V with hs | hn
  · let : Subsingleton V := hs
    let : Subsingleton SL := ⟨fun g k => hρ (Subsingleton.elim _ _)⟩
    have hc : Nat.card SL = 1 := Nat.card_unique
    rw [Matrix.PSL3Two.card_SL] at hc
    omega
  · let : Nontrivial V := hn
    obtain ⟨N,hQ,hN⟩ := exists_natural_head ρ (finrank_le_six ρ hfull hFF) hfull
    rcases hN with hker | hN
    · exact Or.inl (moduleQuotient_one_of_natural_head ρ N hQ hker)
    · right
      rcases hN with hN | hN <;> rcases hQ with hQ | hQ
      · exact ⟨N, MulEquiv.refl SL, hN, hQ⟩
      · exact False.elim (not_ff_of_opposite_natural_layers ρ N (Or.inl ⟨hN,hQ⟩) hFF)
      · exact False.elim (not_ff_of_opposite_natural_layers ρ N (Or.inr ⟨hN,hQ⟩) hFF)
      · obtain ⟨eN⟩ := hN
        obtain ⟨eQ⟩ := hQ
        exact ⟨N, BinaryLinearThree.AutomorphismAction.graph,
          ⟨eN.trans BinaryLinearThree.AutomorphismAction.graphNaturalDual.symm⟩,
          ⟨eQ.trans BinaryLinearThree.AutomorphismAction.graphNaturalDual.symm⟩⟩

/-- Coordinate assembly with an explicit homogeneous splitting premise.
The theorem `exists_moduleQuotient` below discharges this premise. -/
theorem exists_moduleQuotient_of_homogeneous_splitting
    (hρ : Function.Injective ρ) (hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤)
    (hFF : IsFFModule ρ)
    (hsplit : ∀ (N : Subrepresentation ρ) (a : SL ≃* SL),
      Nonempty (N.toRepresentation.Equiv (BinaryLinearThree.W.comp a.toMonoidHom)) →
      Nonempty (N.quotientRepresentation.Equiv (BinaryLinearThree.W.comp a.toMonoidHom)) →
      Nonempty (ρ.Equiv (Representation.prod (BinaryLinearThree.W.comp a.toMonoidHom)
        (BinaryLinearThree.W.comp a.toMonoidHom)))) :
    ∃ m : ℕ, (m = 1 ∨ m = 2) ∧ Nonempty (ModuleQuotient ρ m) := by
  rcases one_copy_or_homogeneous_extension ρ hρ hfull hFF with h | ⟨N,a,hN,hQ⟩
  · exact ⟨1, Or.inl rfl, h⟩
  · obtain ⟨e⟩ := hsplit N a hN hQ
    exact ⟨2, Or.inr rfl, moduleQuotient_two_of_equiv ρ a e⟩

/-- A faithful, commutator-generated binary SL₃(2) FF-module modulo its full
fixed space is one or two copies of a natural module with one common marking.
The witness supplies the surjective equivariant linear map and its exact kernel;
homogeneous self-extension splitting is proved, not assumed. -/
theorem exists_moduleQuotient
    (hρ : Function.Injective ρ) (hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤)
    (hFF : IsFFModule ρ) :
    ∃ m : ℕ, (m = 1 ∨ m = 2) ∧ Nonempty (ModuleQuotient ρ m) :=
  exists_moduleQuotient_of_homogeneous_splitting ρ hρ hfull hFF
    (homogeneous_splitting ρ)

end CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.QuotientRecognition.ExtensionControl
