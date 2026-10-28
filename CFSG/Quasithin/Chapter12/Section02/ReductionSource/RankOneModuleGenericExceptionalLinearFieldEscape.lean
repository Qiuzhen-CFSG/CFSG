module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscape
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeCore
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearField

/-!
# The Chapter 12 consumer of the escaping-cubic quadratic bound

The actual cubic C determines both the plane and its actor. Once the
earlier local construction and the two representation-theoretic outputs
of 5.1.23 are supplied, the proved F.9.16 application contradicts the
strict bound on the same faithful H/O₂(H)-action. The surviving branch
then gives the original field-four and Borel conclusions.

The local construction, abelian span and strict bound remain explicit
source obligations; this module does not claim their discharge. The
normalizing-cubic branch retains its separate producer.

Source: Aschbacher--Smith, 5.1.14--23, pp.638--646; 12.2.2, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open Chapter15.Section03.AbelianAmalgam
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B C : Subgroup G} {n : ℕ}

/-- The original maximal residual already supplies F.8.1's trivial
generated two-core, before constructing the plane or its module. -/
theorem linear_cubic_generated_core
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hout : ¬ C ≤ normalizer (residual H : Set G)) :
    pCore 2 ((CubicEscape.actor T C ⊔ (T : Subgroup G)) ⊔ H : Subgroup G) = ⊥ :=
  CubicEscape.generated_core_eq_bot h.simpleQTKE hH.1.1.2 hK hout

/-- The two bounds concern the very same quotient action, constructed
from the source local groups. There is no assumed upper-ratio callback. -/
theorem linear_cubic_false_of_local_and_module_sources
    (hlocal : ∃ z : G, CubicEscape.LocalData T H C z)
    (habelian : ∀ z : G, CubicEscape.LocalData T H C z →
      IsMulCommutative (conjugateSpanBy (CubicEscape.plane C z)
        (centralizer ({z} : Set G))))
    (hstrict : ∀ (z : G), CubicEscape.LocalData T H C z →
      ∀ hU : IsElementaryAbelian 2 (conjugateSpanBy (CubicEscape.plane C z) H),
        letI := hU
        ∀ a : LocalQuotientAction H (conjugateSpanBy (CubicEscape.plane C z) H) (zpowers z),
          2 < quadraticRatio a.representation) : False := by
  obtain ⟨z, d⟩ := hlocal
  let : IsMulCommutative (conjugateSpanBy (CubicEscape.plane C z)
      (centralizer ({z} : Set G))) := habelian z d
  obtain ⟨hU, a, hbound⟩ := d.exists_bounded_action
  exact (not_lt_of_ge hbound) (hstrict z d hU a)

/-- Literal Cartan assembly: only the local and module producers remain
in the escaping branch. The existing normalizing branch is unchanged. -/
theorem field_four_and_borel_of_linear_escape_sources
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (c : LinearFieldCartan T L H A B C n)
    (hinside : C ≤ normalizer (residual H : Set G) → A = B)
    (hlocal : ¬ C ≤ normalizer (residual H : Set G) →
      ∃ z : G, CubicEscape.LocalData T H C z)
    (habelian : ∀ z : G, CubicEscape.LocalData T H C z →
      IsMulCommutative (conjugateSpanBy (CubicEscape.plane C z)
        (centralizer ({z} : Set G))))
    (hstrict : ∀ (z : G), CubicEscape.LocalData T H C z →
      ∀ hU : IsElementaryAbelian 2 (conjugateSpanBy (CubicEscape.plane C z) H),
        letI := hU
        ∀ a : LocalQuotientAction H (conjugateSpanBy (CubicEscape.plane C z) H) (zpowers z),
          2 < quadraticRatio a.representation) :
    n = 2 ∧ localBorel T L ≤ omegaCentralizer T := by
  apply D.field_four_and_borel_of_linear_cubic_branches h hH hK hnf c hinside
  intro hout
  exact linear_cubic_false_of_local_and_module_sources (hlocal hout) habelian hstrict

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
