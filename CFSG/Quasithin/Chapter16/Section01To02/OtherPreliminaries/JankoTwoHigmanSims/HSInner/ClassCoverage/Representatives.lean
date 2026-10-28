module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.Statements
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.GeneratorCover

/-!
# Marked representatives for the two inner HS involution classes

The second representative is the short word `s0 s1 s2 s1 s0 s2` in the fixed
ATLAS carrier. The accompanying finite certificates prove its order and the
exhaustive conjugacy assertion. Its full centralizer, rather than an embedded
subgroup of the expected order, is the object of the separate structure proof.

Source: Aschbacher–Smith 16.1.5(10), printed p.1172; GLS3, Table 5.3m.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage
open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.EvenLocalCandidates

/-- The marked representative for the product-centralizer class. -/
def t : Carrier := s0 * s1 * s2 * s1 * s0 * s2

namespace Certificate
open Theory.GroupTheory

def localLetter : Fin 4 → Carrier := ![s0, s1, s2, s2⁻¹]
def invLetter : Fin 4 → Fin 4 := ![0, 1, 3, 2]
def ambientLetter : Fin 3 → Carrier :=
  ![generatorAElement, generatorBElement, generatorBElement⁻¹]

def checkFin {n : ℕ} (f : Fin n → Bool) : Bool :=
  (List.range n).all (fun i => if h : i < n then f ⟨i, h⟩ else true)

theorem checkedAt {n : ℕ} {f : Fin n → Bool} (h : checkFin f = true) (i : Fin n) :
    f i = true := by
  have hi := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  simpa only [dif_pos i.isLt] using hi

theorem allFin {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    (h : checkFin (fun i => decide (P i)) = true) : ∀ i, P i :=
  fun i => of_decide_eq_true (checkedAt h i)

end Certificate
end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage
