module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalInterfaces

/-!
# Local-factor conclusions needed before the terminal product marking

These are intermediate obligations from 12.3.7 and the calculation on
pp.811--812, with L₁, L₂ and L_e fixed by TerminalInterfaces. The module
and weight-two fields concern only the second seed [Z,L₂], not U or its
decomposition. No constructor is asserted here. The product owner must
obtain this analysis from the earlier source results, then construct the
faithful quotient and its two compatible factor images.

Source: Aschbacher--Smith, 12.3.7, 12.3.13 and completion of 12.3.1.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 BinarySevenCode
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
variable {S : Setup T L V} {D : S.LocalAnalysis}
namespace TerminalPoint
variable (P : TerminalPoint S D)

/-- The literal local factors prior to recognition of Y/O₂(Y).
This record is an unproved source obligation, not a source hypothesis. -/
structure LocalFactorAnalysis where
  omega_split : P.Z = (P.Z ⊓ centralizer (L : Set G)) ⊔ (P.Z ⊓ V)
  normalizer_image : D.model.permutation.range = ⊤
  local_product : P.Le = P.L1 ⊔ P.L2
  intersection_residual : P.L1 =
    (primeToResidual 3 (P.K ⊓ normalizer (L : Set G) : Subgroup G)).map
      (P.K ⊓ normalizer (L : Set G)).subtype
  second_quotient : (P.L2 ⧸ pCore 2 P.L2) ≃* alternatingGroup (Fin 3)
  second_natural : Representation.BinaryConjugationSection P.L2 ⁅P.Z, P.L2⁆ ⊥
    ((BinaryPermutation.alternatingCoreRepresentation (Fin 3)).comp
      (second_quotient.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P.L2))))
  second_thompson : ⁅P.L2, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆ = P.L2
  weight_two : ∃ v : V, v ≠ 1 ∧ weight (D.model.coordinates v).toAdd.val = 2 ∧
    (v : G) ∈ ⁅P.Z, P.L2⁆

end TerminalPoint
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
