module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.CentralAttachments.Involution

/-!
# Central attachments to faithful binary SL₃(2) FF-modules

The literal commutator submodule D is faithful, fully moving, and an
FF-module. Its natural quotient classification, the checked one-dimensional
H¹ calculation, and the involution displacement argument yield four exhaustive
possibilities: a split natural module, a split doubled natural module, a
natural quotient with a fixed line below, or a natural module with one
central quotient dimension above. All coordinate maps use the actual matrix
group and a common automorphism marking. Both nonsplit four-dimensional
modules are retained.

This is the abstract representation-theoretic input to MS93 (3.2). The local
identifications of D with U and the reconstruction of X and Z remain with
that theorem's source-application owner.
Source: Aschbacher–Smith B.4.8–9 and B.5.1, printed pp.91–103;
Meierfrankenfeld–Stellmacher (1993), (3.2), printed p.863.
-/

@[expose] public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.CentralAttachments
open AbelianCore.QuotientRecognition

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) SL V)

/-- The four exhaustive central-attachment alternatives for a faithful binary
FF-representation of the actual matrix SL₃(2). The moving module is literally
D = [V,SL₃(2)], and C is the full fixed space. Natural copies use one common
marking; the nonsplit lower case carries a surjective equivariant natural map
whose kernel is exactly C ∩ D. Both nonsplit four-dimensional cases are retained.

This is the binary central-attachment classification needed for MS93 (3.2).
It does not identify the downstream local groups X, Z or U; those comparisons
belong to the source application. -/
theorem classification (hρ : Function.Injective ρ) (hFF : IsFFModule ρ) :
    (Nonempty (Copies (moving ρ).toRepresentation 1) ∧
      IsCompl (fixedSpace ρ ⊤) (moving ρ).toSubmodule) ∨
    (Nonempty (Copies (moving ρ).toRepresentation 2) ∧
      IsCompl (fixedSpace ρ ⊤) (moving ρ).toSubmodule) ∨
    (Nonempty (ModuleQuotient (moving ρ).toRepresentation 1) ∧ centralSum ρ = ⊤ ∧
      Module.finrank (ZMod 2)
        (fixedSpace ρ ⊤ ⊓ (moving ρ).toSubmodule : Submodule (ZMod 2) V) = 1) ∨
    (Nonempty (Copies (moving ρ).toRepresentation 1) ∧
      Disjoint (fixedSpace ρ ⊤) (moving ρ).toSubmodule ∧
      Module.finrank (ZMod 2) (V ⧸ centralSum ρ) = 1) := by
  rcases moving_trichotomy ρ hρ hFF with ⟨⟨e⟩, _⟩ | ⟨⟨e⟩, _⟩ | ⟨⟨q⟩, hk⟩
  · rcases natural_upper_dichotomy ρ e with h | h
    · exact Or.inl ⟨⟨e⟩, h⟩
    · exact Or.inr (Or.inr (Or.inr ⟨⟨e⟩, h⟩))
  · exact Or.inr (Or.inl ⟨⟨e⟩, doubled_isCompl hFF e⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨⟨q⟩, lower_excludes_upper ρ hFF q hk, hk⟩))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.CentralAttachments
