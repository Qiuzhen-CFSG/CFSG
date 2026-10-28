module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.CubicSelection.Reduction
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.CubicSelection.OuterSchurDegree.Actors
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.CubicSelection.OuterSchurDegree.Model
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.CubicSelection.OuterSchurDegree.FixedSpace
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.CubicSelection.OuterSchurDegree.Realization

/-!
# The outer Schur-linear degree bound

The actual tensor catalogue realizes each outer Schur-linear involution as
interchange of two tensor factors over the original component Schur field.
Its displacement excludes rank one. Outer cyclicity then supplies a
commuting nonidentity inner involution, and the common fixed-space estimate
gives binary degree at most twice the actor's fixed codimension, hence at
most 12r+4. All realization and fixed-space premises are discharged in
`source_degree_le`; the earlier conditional interface is preserved.

Since 12r+4 < 16r for r > 1, `source_selection` gives the two required
support shapes in this outer branch. The inner branch and final K.3.4
assembly remain with the support-selection consumer. The proof uses the
given rank and fixed-codimension bounds and needs no further cubicity input.

Source: Aschbacher--Smith K.3.4, printed pp.451,456--457;
Guralnick--Malle, Classification of 2F-modules II, Section 3.5 and
Proposition 6.2(2--3), manuscript pp.20,39--40.
-/

public section

namespace CFSG.Quasithin.ChapterK.Symplectic.Recognition.OuterSchur
open Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour

variable {G V F : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  [Field F] [Finite F] [Algebra (ZMod 2) F]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
  [IsIrreducible (ρ.comp L.subtype)]

/-- Conditional assembly of the tensor realization and its two numerical
calculations, retained as an interface for other realizations. -/
theorem degree_le_of_tensorSwap_estimates {K : GroupClass}
    (h : SourceHypothesis K ρ L) {r : ℕ} (hr : 1 < r) (hF : Nat.card F = 2^r)
    (e : L ⧸ Subgroup.center L ≃* Sp F) (A : Subgroup G)
    (hA : IsElementaryAbelian 2 A) (hnot : ¬ A ≤ L)
    (hrank : rank A ≤ 3*r+1) (hcodim : fixedCodim ρ A ≤ 2 * rank A)
    (hlinear : ∀ a ∈ A, IsSchurLinear ρ L a)
    (hmodel : ∀ t ∈ A, t ∉ L → t ^ 2 = 1 → ∀ ht : IsSchurLinear ρ L t,
      Nonempty (TensorSwapRealization ρ L t ht))
    (hsingle : ∀ (t : G) (ht : IsSchurLinear ρ L t),
      TensorSwapRealization ρ L t ht →
      3 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)))
    (hpair : ∀ (t : G) (ht : IsSchurLinear ρ L t),
      TensorSwapRealization ρ L t ht → ∀ (u : L), u ^ 2 = 1 → u ≠ 1 →
      Commute t (u : G) → Module.finrank (ZMod 2) V ≤ 2 * pairFixedCodim ρ t u) :
    Module.finrank (ZMod 2) V ≤ 12*r+4 := by
  apply degree_le_of_outer_estimates h hr hF e A hA hnot hrank hcodim hlinear
  · intro t ht htL ht2 htl
    obtain ⟨R⟩ := hmodel t ht htL ht2 htl
    exact hsingle t htl R
  · intro t ht u _ htL ht2 huL hune hu2 htu htl
    obtain ⟨R⟩ := hmodel t ht htL ht2 htl
    have hu2' : (⟨u, huL⟩ : L) ^ 2 = 1 := Subtype.ext hu2
    have hune' : (⟨u, huL⟩ : L) ≠ 1 := fun he => hune (congrArg Subtype.val he)
    exact hpair t htl R ⟨u, huL⟩ hu2' hune' htu

omit [IsIrreducible (ρ.comp L.subtype)] in
/-- The outer Schur-linear degree estimate on the original binary module.
The tensor realization and both fixed-space calculations are proved, with
no support-selection or graph-cocycle-descent premise. This applies in
particular to `K = KnownSimple.IsKnownSimple`. -/
theorem source_degree_le {K : GroupClass}
    (h : SourceHypothesis K ρ L) {r : ℕ} (hr : 1 < r) (hF : Nat.card F = 2^r)
    (e : L ⧸ Subgroup.center L ≃* Sp F)
    (P : @TensorParameters F L V _ _ _ _ _ _ _ (ρ.comp L.subtype) h.irreducible
      (sourceDerivedEquiv h hr hF e) r)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) (hnot : ¬ A ≤ L)
    (hrank : rank A ≤ 3*r+1) (hcodim : fixedCodim ρ A ≤ 2 * rank A)
    (hlinear : ∀ a ∈ A, IsSchurLinear ρ L a) :
    Module.finrank (ZMod 2) V ≤ 12*r+4 := by
  let : IsIrreducible (ρ.comp L.subtype) := h.irreducible
  apply degree_le_of_tensorSwap_realizations h hr hF e A hA hnot hrank hcodim hlinear
  intro t _ htL ht2 ht
  exact source_tensorSwapRealization h hr hF e P t htL ht2 ht

omit [IsIrreducible (ρ.comp L.subtype)] in
/-- The degree gap selects the two K.3.4 support shapes for an actual outer
Schur-linear actor. This discharges the outer branch of cubic support selection. -/
theorem source_selection {K : GroupClass}
    (h : SourceHypothesis K ρ L) {r : ℕ} (hr : 1 < r) (hF : Nat.card F = 2^r)
    (e : L ⧸ Subgroup.center L ≃* Sp F)
    (P : @TensorParameters F L V _ _ _ _ _ _ _ (ρ.comp L.subtype) h.irreducible
      (sourceDerivedEquiv h hr hF e) r)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) (hnot : ¬ A ≤ L)
    (hrank : rank A ≤ 3*r+1) (hcodim : fixedCodim ρ A ≤ 2 * rank A)
    (hlinear : ∀ a ∈ A, IsSchurLinear ρ L a) :
    letI := h.irreducible
    P.factors = 1 ∧ (P.blocks = 1 ∨ P.blocks = 2) := by
  let : IsIrreducible (ρ.comp L.subtype) := h.irreducible
  have hd := source_degree_le h hr hF e P A hA hnot hrank hcodim hlinear
  apply P.selection_of_degree_lt
  omega

end CFSG.Quasithin.ChapterK.Symplectic.Recognition.OuterSchur
