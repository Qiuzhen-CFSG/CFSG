module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief.Models.Transport
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief.Models.Orders

/-!
# The actual exceptional chief-image comparison

The surviving source alternatives force field degree two. For a nontrivial
actual quotient action of K/O₂(K), in the
PSL₂(p) branch its order is outside the small simple list. The other branch
retains the actual odd core and SL₂(p) quotient, including p = 5.

The normal-component list for the G.6.4 models and the odd-kernel obstruction
are separate remaining inputs; this module does not assert the final exclusion.
Source: Aschbacher--Smith, 11.5.8, printed p.784, using 11.4.1(2).
The partial ClassicalRefinementCase is used only as an explicit earlier-source
premise. Triangle elimination belongs to its source producer.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief.Models
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Closure.Geometry D) (g : G)

/-- Compare a nontrivial actual quotient action with the two surviving
source alternatives. The equality alternative is excluded by L₁ < K. -/
theorem source_quotient_comparison {H : Type*} [Group H]
    (hlt : E.L₁ < E.K)
    (hcase : Source.ClassicalRefinementCase L E.L₁ E.K 1 E.input.field.degree)
    (f : (E.K ⧸ pCore 2 E.K) →* H) (hne : f.range ≠ ⊥) :
    E.input.field.degree = 2 ∧
      ((∃ p : ℕ, (p = 5 ∨ (p.Prime ∧ 11 ≤ p)) ∧
          Source.IsSL (Source.TwoOddQuotient E.K) 2 p) ∨
        ¬ SmallSimpleOrder (Nat.card f.range)) := by
  cases hcase with
  | equal he => exact (hlt.ne he).elim
  | sl2Prime hi hn p hp he => exact ⟨hn, Or.inl ⟨p, hp, he⟩⟩
  | psl2Prime hi hn p hp hlarge he hL =>
    let : Nontrivial f.range := (nontrivial_iff_ne_bot _).mpr hne
    exact ⟨hn, Or.inr
      (psl2_image_not_small hp hlarge he f.rangeRestrict f.rangeRestrict_surjective)⟩


end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief.Models
