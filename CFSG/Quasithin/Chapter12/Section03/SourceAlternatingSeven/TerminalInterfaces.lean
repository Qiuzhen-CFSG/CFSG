module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalSelection
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalCover
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.GroupTheory.PResidual.PrimeTo
public import Theory.Representation.BinaryConjugationSection
public import Theory.Representation.BinaryPermutationAlternatingActions

/-!
# Literal intermediate objects for the terminal A₇ argument

The selected H determines K=O²(H), its quotient-action centralizer, the
residual L_e, and L₂=O²(C_{L_e}(K/O₂(K))). The last two source objects are
Y=KL₂T and U=⟨Z^Y⟩. Thus changing an abstract factor cannot change the
quotient maps or the conjugate span used by a later proof.

`ComponentAnalysis` records the genuine conclusions of 12.3.12, including
an equivariant identification of [Z,K]. `ProductAnalysis` is the separate
construction required before applying B.5.6 on p.812. Both are intermediate
proof obligations: neither has a universal constructor in this file.
The terminal assembly must construct them; they are not source hypotheses.
Source: Aschbacher--Smith, 12.3.12--13 and completion of 12.3.1, pp.811--812.
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

/-- The literal normalizer action on K/O₂(K). -/
def quotientAction : normalizer (P.K : Set G) →* MulAut (P.K ⧸ pCore 2 P.K) :=
  (quotientAut (pCore 2 P.K)).comp P.K.normalizerMonoidHom

/-- C_G(K/O₂(K)), with its original embedding in G. -/
def quotientCentralizer : Subgroup G :=
  P.quotientAction.ker.map (normalizer (P.K : Set G)).subtype

/-- O²(C_L(e)). -/
def Le : Subgroup G :=
  (pResidual 2 (L ⊓ P.pointCentralizer : Subgroup G)).map (L ⊓ P.pointCentralizer).subtype

/-- O^{3′}(C_L(Z)), retaining the prime-to-three residual convention. -/
def L1 : Subgroup G :=
  (primeToResidual 3 (L ⊓ centralizer (P.Z : Set G) : Subgroup G)).map
    (L ⊓ centralizer (P.Z : Set G)).subtype

/-- The second local residual in the completion of 12.3.1. -/
def L2 : Subgroup G :=
  (pResidual 2 (P.Le ⊓ P.quotientCentralizer : Subgroup G)).map
    (P.Le ⊓ P.quotientCentralizer).subtype

/-- The actual generated local subgroup. The product assertion is a theorem
of the source geometry; the join makes the definition unconditional. -/
def Y : Subgroup G := P.K ⊔ P.L2 ⊔ (T : Subgroup G)

/-- The conjugate span of the actual Sylow omega center. -/
def U : Subgroup G := componentOrbit P.Z P.Y

/-- The A₅ conclusions of 12.3.12, to be constructed from the earlier inputs. -/
structure ComponentAnalysis where
  normalizes : P.pointCentralizer ≤ normalizer (P.K : Set G)
  quotient : (P.K ⧸ pCore 2 P.K) ≃* alternatingGroup (Fin 5)
  thompson : ⁅P.K, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆ = P.K
  natural : Representation.BinaryConjugationSection P.K ⁅P.Z, P.K⁆ ⊥
    ((BinaryPermutation.alternatingCoreRepresentation (Fin 5)).comp
      (quotient.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P.K))))

/-- The literal product-action hypotheses immediately preceding the B.5.6
application. The module decomposition and its contradiction are not fields. -/
structure ProductAnalysis where
  reduced : IsPReduced 2 (P.U.subgroupOf P.Y)
  centralizer_eq : P.Y ⊓ centralizer (P.U : Set G) = P.Y.pCoreIn 2
  quotient : (P.Y ⧸ pCore 2 P.Y) ≃* (Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3))
  first_image : (P.K.subgroupOf P.Y).map
    (quotient.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P.Y))) =
      (alternatingGroup (Fin 5)).prod ⊥
  second_image : (P.L2.subgroupOf P.Y).map
    (quotient.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P.Y))) =
      (⊥ : Subgroup (Equiv.Perm (Fin 5))).prod (alternatingGroup (Fin 3))
  thompson_image : ((Stellmacher.elementaryAbelianMaxJ P.Y).subgroupOf P.Y).map
    (quotient.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P.Y))) = ⊤
  second_quotient : (P.L2 ⧸ pCore 2 P.L2) ≃* alternatingGroup (Fin 3)
  second_natural : Representation.BinaryConjugationSection P.L2 ⁅P.Z, P.L2⁆ ⊥
    ((BinaryPermutation.alternatingCoreRepresentation (Fin 3)).comp
      (second_quotient.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P.L2))))
  weight_two : ∃ v : V, v ≠ 1 ∧ weight (D.model.coordinates v).toAdd.val = 2 ∧
    (v : G) ∈ ⁅P.Z, P.L2⁆

end TerminalPoint
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
