module

public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.Representation.NormalElementaryQuotient
public import Theory.Representation.HexacodeAction.CoverComparison
public import Theory.Representation.HexacodeAction

/-!
# The original binary action of an exceptional covered-six block

The defining equality C_K(U)=O₂(K) constructs a faithful binary action of
K/O₂(K) on U, whose order is 2⁶. The central quotient isomorphism gives an
actual covering map to A₆, and Schur-cover uniqueness identifies it with the
even hexacode cover while preserving that projection.

`HexacodeModel` specifies the remaining representation identification; this
module does not assert its existence. In particular no quotient by fixed
vectors is substituted for the original U.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, C.1.30,
printed p.135, A.3.5, printed p.43, and 13.6.22, printed p.932. The concrete
hexacode carrier and its licensed ATLAS attribution are preserved in the
imported `HexacodeAction.CoverComparison` and `HexacodeAction.Cover` modules.
-/

@[expose] public section
open Subgroup CFSG.Quasithin.ChapterC Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix
section Intrinsic
variable {K : Type*} [Group K] (h : IsExceptionalAhat6Block K)

section Binary
variable [IsElementaryAbelian 2 (blockU K)]

/-- The faithful quotient acts on the original six-space, without dividing out fixed vectors. -/
noncomputable def binaryAction : Representation (ZMod 2) (K ⧸ pCore 2 K)
    (Additive (blockU K)) :=
  NormalElementaryQuotient.representation (blockU K)
    (QuotientGroup.mk' (pCore 2 K)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk', h.centralizer])

/-- The source centralizer equality is exactly the kernel condition. -/
theorem binaryAction_injective : Function.Injective (binaryAction h) :=
  NormalElementaryQuotient.representation_injective (blockU K)
    (QuotientGroup.mk' (pCore 2 K)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk', h.centralizer])

/-- Quotient representatives act by their literal conjugation on U. -/
theorem binaryAction_apply (k : K) (u : Additive (blockU K)) :
    ((binaryAction h (QuotientGroup.mk' (pCore 2 K) k) u).toMul : K) =
      k * (u.toMul : K) * k⁻¹ :=
  NormalElementaryQuotient.representation_apply (blockU K)
    (QuotientGroup.mk' (pCore 2 K)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk', h.centralizer]) k u

include h in
/-- The six-dimensional clause in the block definition concerns this original U. -/
theorem binary_finrank : Module.finrank (ZMod 2) (Additive (blockU K)) = 6 := by
  let := h.1.finite
  have hc : 2 ^ Module.finrank (ZMod 2) (Additive (blockU K)) = 2 ^ 6 := by
    calc
      _ = Nat.card (Additive (blockU K)) := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
      _ = 2 ^ 6 := h.2.2.2.2.1
  exact Nat.pow_right_injective (by decide : 1 < 2) hc

/-- The representation coordinates still to be constructed from the block predicate.
Both the actor isomorphism and the vector equivalence are required; a group
family name or an abstract dimension equality does not supply this model. -/
structure HexacodeModel where
  quotientIso : (K ⧸ pCore 2 K) ≃* Atlas.Codes.HexEvenAutomorphisms
  coordinates : Additive (blockU K) ≃ₗ[ZMod 2] Atlas.Codes.hexacode
  intertwining : ∀ g u, coordinates (binaryAction h g u) =
    Hexacode.action (quotientIso g).val (coordinates u)

end Binary

include h in
/-- The comparison retains the specified central quotient map. -/
theorem exists_cover_equiv
    (e : ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) ≃*
      alternatingGroup (Fin 6)) :
    ∃ f : (K ⧸ pCore 2 K) ≃* Atlas.Codes.HexEvenAutomorphisms,
      Atlas.Codes.hexEvenCoordinate.comp f.toMonoidHom =
        e.toMonoidHom.comp (QuotientGroup.mk' (center (K ⧸ pCore 2 K))) := by
  let := h.1.finite
  let := h.2.1
  let q : Covering (K ⧸ pCore 2 K) (alternatingGroup (Fin 6)) := {
    toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (center (K ⧸ pCore 2 K)))
    surjective := e.surjective.comp (QuotientGroup.mk'_surjective _) }
  apply Hexacode.CoverComparison.exists_even_equiv_over_coordinate q
  have hk : q.toMonoidHom.ker = center (K ⧸ pCore 2 K) := by
    ext x
    change e (QuotientGroup.mk' _ x) = 1 ↔ _
    rw [map_eq_one_iff e e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  rw [hk]
  exact h.2.2.1

end Intrinsic


end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix
