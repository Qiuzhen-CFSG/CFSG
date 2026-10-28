module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.CubicSelection.InnerDegree.Reduction
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.CubicSelection.InnerDegree.RadicalGeometry
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.CubicSelection.InnerDegree.ConjugateGeneration

/-!
# The inner actor degree estimate for K.3.4

Every elementary abelian two-subgroup lies in a conjugate parabolic radical.
Replace an actual inner offender by a nontrivial maximizer of
`|B|² |C_V(B)|` in that radical. Its normalizer invariance identifies it as
the distinguished root or the whole radical. Five root conjugates or two
radical conjugates generate Sp₄, giving binary degree at most 10r or 12r.

All placement, invariant-subgroup and conjugate-generation premises are
discharged here. The source adapters preserve the actual component action
and its marked central quotient. The final application uses the supplied
tensor parameters and `12r < 16r` to select the two possible support shapes.
Cubicity and a separate rank bound are unnecessary for this inner estimate.
The outer-actor cases remain with the full support-selection assembly.

Source: Guralnick--Malle, *Classification of 2F-modules II*, Proposition 6.2
part 1A, author manuscript pp.38--39; Aschbacher--Smith K.3.4, printed pp.456--457.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterK.Symplectic.Recognition.InnerDegree

variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- An actual elementary offender on a binary Sp₄-module with no global
fixed vectors bounds the whole module, with no remaining geometry premises. -/
theorem finrank_le_twelve_mul
    (ρ : Representation (ZMod 2) (Sp F) V) {r : ℕ} (hr : 1 < r)
    (hF : Nat.card F = 2 ^ r) (hfix : fixedSpace ρ ⊤ = ⊥)
    (A : Subgroup (Sp F)) (hA : IsElementaryTwo A)
    (hcodim : fixedCodim ρ A ≤ 2 * rank A) :
    Module.finrank (ZMod 2) V ≤ 12 * r :=
  finrank_le_twelve_mul_of_geometry ρ hF hfix (normalized_radical_subgroup hF hr)
    exists_five_centralRoot_conjugates exists_two_radical_conjugates A hA hcodim
    (elementary_placement hF (by omega) A hA)

variable {G : Type*} [Group G] [Finite G]
  {ρG : Representation (ZMod 2) G V} {L : Subgroup G}

/-- The original component action satisfies the inner degree bound. The
equivalence used in transport is the given central quotient followed by e. -/
theorem source_inner_degree {K : GroupClass}
    (h : SourceHypothesis K ρG L) {r : ℕ} (hr : 1 < r)
    (hF : Nat.card F = 2 ^ r) (e : L ⧸ center L ≃* Sp F)
    (A : Subgroup L) (hA : IsElementaryTwo A)
    (hcodim : fixedCodim (ρG.comp L.subtype) A ≤ 2 * rank A) :
    Module.finrank (ZMod 2) V ≤ 12 * r :=
  source_inner_degree_of_geometry h hF e (elementary_placement hF (by omega))
    (normalized_radical_subgroup hF hr) exists_five_centralRoot_conjugates
    exists_two_radical_conjugates A hA hcodim

/-- An actual ambient offender contained in L bounds the binary degree by
12r. Its original rank and fixed codimension are preserved on restriction. -/
theorem source_ambient_inner_degree {K : GroupClass}
    (h : SourceHypothesis K ρG L) {r : ℕ} (hr : 1 < r)
    (hF : Nat.card F = 2 ^ r) (e : L ⧸ center L ≃* Sp F)
    (A : Subgroup G) (hAL : A ≤ L) (hA : IsElementaryTwo A)
    (hcodim : fixedCodim ρG A ≤ 2 * rank A) :
    Module.finrank (ZMod 2) V ≤ 12 * r :=
  source_ambient_inner_degree_of_radical_geometry h hF hr e
    exists_five_centralRoot_conjugates exists_two_radical_conjugates A hAL hA hcodim

omit [CharP F 2] in
/-- Literal application to the source tensor parameters: an inner offender
selects one factor repeated once or twice. No degree premise is assumed. -/
theorem source_inner_selection [Algebra (ZMod 2) F] {K : GroupClass}
    (h : SourceHypothesis K ρG L) {r : ℕ} (hr : 1 < r) (hF : Nat.card F = 2 ^ r)
    (e : L ⧸ center L ≃* Sp F)
    (P : @TensorParameters F L V _ _ _ _ _ _ _ (ρG.comp L.subtype) h.irreducible
      (sourceDerivedEquiv h hr hF e) r)
    (A : Subgroup G) (hAL : A ≤ L) (hA : IsElementaryTwo A)
    (hcodim : fixedCodim ρG A ≤ 2 * rank A) :
    letI := h.irreducible
    P.factors = 1 ∧ (P.blocks = 1 ∨ P.blocks = 2) := by
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  let : IsIrreducible (ρG.comp L.subtype) := h.irreducible
  have hd := source_ambient_inner_degree h hr hF e A hAL hA hcodim
  apply P.selection_of_degree_lt
  omega

end CFSG.Quasithin.ChapterK.Symplectic.Recognition.InnerDegree
