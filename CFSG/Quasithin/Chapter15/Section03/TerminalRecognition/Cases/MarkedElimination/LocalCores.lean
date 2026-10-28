module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Reductions
public import Theory.SpecificGroups.SymmetricFourResidualCore

/-!
# Excluding the S₄ local marking in terminal recognition

The genuine local supplement `G₁ = Y_F T_E`, with `Y_F` two-perfect
and normalized by `T_E`, identifies `Y_F` with the embedded two-residual
of `G₁`. This identity survives the quotient by `Q₀` and every specified
model equivalence. A local S₄ has the same two-core as its two-residual.
On the other hand, `Q₀ O₂(Y_F) ≤ R ≤ C(V)` and `[V,Q₁] = F ≠ 1`
give a strict inclusion of these cores. This is the contradiction.

Both locals in F.6.18(6) are S₄, so either generator labeling is covered
for L₃(2), A₆ and the source triple cover Â₆. The argument uses only
the actual local equivalence; no replacement of the covering group or
its embeddings is needed. In F.6.18(7), only one local is S₄. The other
A₇ labeling requires the additional marked module argument and is not
asserted to follow from the strict core inequality alone.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), printed pp.309–310 and 1154–1155.
-/

public section
open Subgroup

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.MarkedElimination

variable {H : Type*} [Group H] [Finite H]

/-- The local residual identity retains the actual Sylow supplement and
passes through any homomorphism, including the marked quotient model. -/
theorem local_residual_image (T : Sylow 2 H) (Y : Subgroup H)
    (hY : IsPPerfect 2 Y) (hn : (T : Subgroup H) ≤ normalizer (Y : Set H))
    {K : Type*} [Group K] (f : H →* K) :
    (pResidual 2 ((Y ⊔ (T : Subgroup H)).map f)).map
      ((Y ⊔ (T : Subgroup H)).map f).subtype = Y.map f := by
  rw [← map_embedded_pResidual,
    embedded_pResidual_join_pGroup Y (T : Subgroup H) hY T.isPGroup' hn]

/-- The first local cannot be S₄ under a connected model equivalence.
All normality used here is relative to `Y_F T_E`. -/
theorem symmetricFour_local_excluded (T : Sylow 2 H) (Y V R F : Subgroup H)
    (hY : IsPPerfect 2 Y) (hn : (T : Subgroup H) ≤ normalizer (Y : Set H))
    (hbound : pCore 2 H ⊔ Y.pCoreIn 2 ≤ R)
    (hR : R ≤ centralizer (V : Set H))
    (hcomm : ⁅V, (Y ⊔ (T : Subgroup H)).pCoreIn 2⁆ = F) (hF : F ≠ ⊥)
    {K : Type*} [Group K] (e : coreQuotient H ≃* K)
    (localEquiv : ((Y ⊔ (T : Subgroup H)).map
      (e.toMonoidHom.comp coreProjection)) ≃* Equiv.Perm (Fin 4)) : False := by
  have hs := localCore_strict_in_model Y (Y ⊔ (T : Subgroup H)) V R F
    le_sup_left (sup_le Y.le_normalizer hn) hbound hR hcomm hF e
  have he := Theory.SpecificGroups.SymmetricFour.embedded_residual_twoCore
    ((Y ⊔ (T : Subgroup H)).map (e.toMonoidHom.comp coreProjection)) localEquiv
  rw [local_residual_image T Y hY hn] at he
  exact (ne_of_lt hs) he

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.MarkedElimination
