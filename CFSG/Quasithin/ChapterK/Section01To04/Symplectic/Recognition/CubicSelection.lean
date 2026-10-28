module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.CubicSelection.Reduction
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.CubicSelection.InnerDegree
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.CubicSelection.OuterSchurDegree

/-!
# Cubic tensor support selection for K.3.4

The original component's periodic tensor parameters have one factor repeated
once or twice. If this fails, the Schur-moving displacement estimate leaves
an actual Schur-linear cubic actor. An inner actor bounds the binary degree
by 12r through parabolic offender enlargement and conjugate generation. An
outer actor bounds it by 12r+4 through its actual tensor-swap realization
and common fixed spaces. Both bounds are below the next possible degree 16r.

The source application constructs these selected parameters from the full
catalogue on the literal component action and its marked central quotient.
No extra degree, support, tensor-realization or graph-descent premise remains.
Identification and descent of the two selected modules belong to the K.3.4
recognition assembly.

Source: Aschbacher--Smith K.3.4, printed pp.451,456--457; Guralnick--Malle,
Classification of 2F-modules II, Proposition 6.2 and Table 9, author
manuscript pp.38--40,47.
-/

public section

namespace CFSG.Quasithin.ChapterK.Symplectic.Recognition
open Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour

variable {G V F : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  [Field F] [Finite F] [Algebra (ZMod 2) F]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- The ambient cubic action selects exactly the two K.3.4 support shapes
in any tensor parameters for the actual component. In particular this holds
for the full source class `K = KnownSimple.IsKnownSimple`. -/
theorem source_support_selection {K : GroupClass}
    (h : SourceHypothesis K ρ L) {r : ℕ} (hr : 1 < r) (hF : Nat.card F = 2^r)
    (e : L ⧸ Subgroup.center L ≃* Sp F)
    (P : @TensorParameters F L V _ _ _ _ _ _ _ (ρ.comp L.subtype) h.irreducible
      (sourceDerivedEquiv h hr hF e) r) :
    letI := h.irreducible
    P.factors = 1 ∧ (P.blocks = 1 ∨ P.blocks = 2) := by
  let : IsIrreducible (ρ.comp L.subtype) := h.irreducible
  by_contra hnot
  obtain ⟨A, hA, _, hrank, hcodim, hlinear⟩ :=
    source_schurLinear_actor_of_unselected h hr hF e P hnot
  by_cases hAL : A ≤ L
  · exact hnot (InnerDegree.source_inner_selection h hr hF e P A hAL hA hcodim)
  · exact hnot (OuterSchur.source_selection h hr hF e P A hA.2 hAL hrank hcodim hlinear)

/-- The source hypotheses produce actual tensor parameters with one factor
and one or two blocks. This discharges the support-selection premise for
the natural and quadratic tensor descent applications, retaining the
catalogue's original Schur field, intertwiner and component equivalence. -/
theorem source_selected_tensorParameters {K : GroupClass}
    (h : SourceHypothesis K ρ L) {r : ℕ} (hr : 1 < r) (hF : Nat.card F = 2^r)
    (e : L ⧸ Subgroup.center L ≃* Sp F) :
    letI := h.irreducible
    ∃ P : TensorParameters (ρ.comp L.subtype) (sourceDerivedEquiv h hr hF e) r,
      P.factors = 1 ∧ (P.blocks = 1 ∨ P.blocks = 2) := by
  let : IsIrreducible (ρ.comp L.subtype) := h.irreducible
  obtain ⟨P⟩ := source_tensorParameters h hr hF e
  exact ⟨P, source_support_selection h hr hF e P⟩

end CFSG.Quasithin.ChapterK.Symplectic.Recognition
