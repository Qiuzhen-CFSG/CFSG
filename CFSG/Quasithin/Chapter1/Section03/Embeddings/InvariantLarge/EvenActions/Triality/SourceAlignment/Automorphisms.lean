module

public import Theory.SpecificGroups.Triality.OuterOddSubgroups.CoefficientAction
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# The raw triality automorphism conventions

The graph-field fixed group acts by conjugation on its characteristic elementary
subgroup and hence on that subgroup's central quotient. `innerDiagonal` is this
concrete automorphism image. Every inner automorphism belongs to it, by lifting
its conjugating element to the elementary group.

`IsSourceFieldAutomorphism` follows GLS3 Definition 2.5.13(c)(1): an Aut-conjugate
of a cubic coefficient automorphism whose order is prime to three. It is not
membership in the full coefficient group, which also contains the graph part.
No disjointness or faithfulness assertion is built into either definition.

Source: Aschbacher–Smith, Notation A.2.5, printed p.33; GLS3 §§2.2 and 2.5,
especially 2.5.13, `refs/KGroup/GLS3/chapter2.tex`. The comparison of the concrete
fixed-point action with the source inner-diagonal group must respect the genuine
D4 model and the elementary central quotient.
-/

@[expose] public section
noncomputable section
open Subgroup
open scoped Pointwise
open Triality.Standard Triality.Standard.OuterOdd

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.Triality.SourceAlignment

/-- Conjugation on the central quotient of an ambient normal subgroup. -/
def centralQuotientConjugation {G : Type*} [Group G]
    (K : Subgroup G) [K.Normal] : G →* MulAut (K ⧸ center K) where
  toFun g := QuotientGroup.congr _ _ (MulAut.conjNormal g)
    (characteristic_iff_map_eq.mp (inferInstance : (center K).Characteristic) _)
  map_one' := by
    ext x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center K) x
    change QuotientGroup.mk' (center K) (MulAut.conjNormal (1 : G) y) =
      QuotientGroup.mk' (center K) y
    rw [map_one]
    rfl
  map_mul' g h := by
    ext x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center K) x
    change QuotientGroup.mk' (center K) (MulAut.conjNormal (g * h) y) =
      QuotientGroup.mk' (center K) (MulAut.conjNormal g (MulAut.conjNormal h y))
    rw [map_mul]
    rfl

private theorem centralQuotientConjugation_inner {G : Type*} [Group G]
    (K : Subgroup G) [K.Normal] (y : K) :
    centralQuotientConjugation K (y : G) = MulAut.conj (QuotientGroup.mk' (center K) y) := by
  ext z
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (center K) z
  change QuotientGroup.mk' (center K) (MulAut.conjNormal (y : G) w) =
    QuotientGroup.mk' (center K) y * QuotientGroup.mk' (center K) w *
      (QuotientGroup.mk' (center K) y)⁻¹
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1

private instance elementary_characteristic (P : Parameters) :
    (elementarySubgroup P).Characteristic :=
  characteristic_iff_map_eq.mpr fun e => map_power_generated P.prime e

/-- Conjugation by a graph-field fixed element, descended through the actual center. -/
def fixedConjugation (P : Parameters) : fixedSubgroup P →* MulAut (Carrier P) :=
  @centralQuotientConjugation (fixedSubgroup P) _ (elementarySubgroup P) (by infer_instance)

/-- The image of the concrete graph-field fixed-point conjugation action. -/
def innerDiagonal (P : Parameters) : Subgroup (MulAut (Carrier P)) :=
  (fixedConjugation P).range

/-- Elementary fixed elements induce the expected inner automorphism. -/
theorem fixedConjugation_inner (P : Parameters) (y : ElementaryGroup P) :
    fixedConjugation P (y : fixedSubgroup P) = MulAut.conj (toCarrier P y) :=
  centralQuotientConjugation_inner (elementarySubgroup P) y

/-- Inner automorphisms lift to conjugation by elementary fixed elements. -/
lemma inner_le_innerDiagonal (P : Parameters) :
    MulAut.innerSubgroup (Carrier P) ≤ innerDiagonal P := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, rfl⟩ := toCarrier_surjective P x
  exact ⟨(y : fixedSubgroup P), fixedConjugation_inner P y⟩

/-- The GLS source convention for field automorphisms of a triality group. -/
def IsSourceFieldAutomorphism (P : Parameters) (a : MulAut (Carrier P)) : Prop :=
  ∃ σ : CoefficientAut P, Nat.Coprime (orderOf (coefficientAction P σ)) 3 ∧
    IsConj (coefficientAction P σ) a

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.Triality.SourceAlignment
