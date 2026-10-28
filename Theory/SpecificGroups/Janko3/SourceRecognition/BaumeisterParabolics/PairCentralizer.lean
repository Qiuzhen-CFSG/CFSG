module
public import Theory.SpecificGroups.Janko3.SourceRecognition.BaumeisterParabolics.Point
public import Theory.GroupTheory.CentralizerSmallKernelTransport

/-!
# The pair centralizer selected by Baumeister's cubic

In S₃ × D₁₀, an involution commuting with a nontrivial cubic has trivial
S₃ coordinate. Its D₁₀ coordinate is a reflection, with centralizer C₂.
This constructs the literal S₃ × C₂ centralizer map without an additional
marked-coordinate assumption on a given pair-group isomorphism.

The calculation discharges the second/third overlap once Lemma 2.5 has
identified the actual normalizer. Source: Baumeister, *A geometry for groups
of J₃-type* (2007), p.496, the paragraph between Lemmas 2.5 and 2.6.
-/

public noncomputable section
namespace Sporadic.Janko3.SourceRecognition.BaumeisterParabolics.PairCentralizer
open Subgroup
open Seventeen

private theorem dihedral_cube (x : DihedralGroup 5) (hx : x^3=1) : x=1 := by
  revert x; decide +kernel

private theorem symmetric_test : ∀ a b : Equiv.Perm (Fin 3),
    a^2=1 → b^3=1 → b≠1 → b*a=a*b → a=1 := by
  intro a b
  fin_cases a <;> fin_cases b <;> decide +kernel

private theorem first_eq_one (f s : PairGroup) (hf : orderOf f=2)
    (hs : orderOf s=3) (hc : Commute s f) : f.1=1 := by
  have hs3 : s^3=1 := by simpa only [hs] using pow_orderOf_eq_one s
  have hs2 : s.2=1 := dihedral_cube _ (congrArg Prod.snd hs3)
  have hs1 : s.1≠1 := by
    intro h
    have he : s=1 := Prod.ext h hs2
    rw [he,orderOf_one] at hs
    omega
  exact symmetric_test f.1 s.1 (congrArg Prod.fst (hf ▸ pow_orderOf_eq_one f))
    (congrArg Prod.fst hs3) hs1 (congrArg Prod.fst hc.eq)

private theorem reflection_test : ∀ d x : DihedralGroup 5,
    d^2=1 → d≠1 → d*x=x*d → x=1 ∨ x=d := by decide +kernel

private theorem reflection_centralizer (d : DihedralGroup 5) (hd : orderOf d=2) :
    centralizer ({d} : Set (DihedralGroup 5)) = zpowers d := by
  apply le_antisymm
  · intro x hx
    rcases reflection_test d x (hd ▸ pow_orderOf_eq_one d)
      (by intro h; rw [h,orderOf_one] at hd; omega)
      (mem_centralizer_singleton_iff.mp hx).symm with h | h
    · exact h ▸ one_mem _
    · exact h ▸ mem_zpowers _
  · exact zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)

private def reflectionEquiv (d : DihedralGroup 5) (hd : orderOf d=2) :
    centralizer ({d} : Set (DihedralGroup 5)) ≃* Multiplicative (ZMod 2) := by
  have hcard : Nat.card (zpowers d) = 2 := (Nat.card_zpowers d).trans hd
  let e : zpowers d ≃* Multiplicative (ZMod 2) := mulEquivOfCyclicCardEq (by
    rw [hcard]
    simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card])
  exact (MulEquiv.subgroupCongr (by exact reflection_centralizer d hd)).trans e

private def productCentralizer (f : PairGroup) (hf : f.1=1) :
    centralizer ({f} : Set PairGroup) ≃*
      (Equiv.Perm (Fin 3) × centralizer ({f.2} : Set (DihedralGroup 5))) where
  toFun x := (x.val.1, ⟨x.val.2,mem_centralizer_singleton_iff.mpr
    (congrArg Prod.snd (mem_centralizer_singleton_iff.mp x.property))⟩)
  invFun x := ⟨(x.1,x.2),mem_centralizer_singleton_iff.mpr (by
    apply Prod.ext
    · change x.1 * f.1 = f.1 * x.1
      simp only [hf,one_mul,mul_one]
    · exact mem_centralizer_singleton_iff.mp x.2.property)⟩
  left_inv x := rfl
  right_inv x := rfl
  map_mul' x y := rfl

/-- In the pair group, the involution commuting with a nontrivial cubic has
centralizer S₃ × C₂. The selected cubic rules out the other involution types. -/
def pairCentralizerEquiv (f s : PairGroup) (hf : orderOf f=2)
    (hs : orderOf s=3) (hc : Commute s f) :
    centralizer ({f} : Set PairGroup) ≃*
      (Equiv.Perm (Fin 3) × Multiplicative (ZMod 2)) := by
  have hfst : f.1 = 1 := by exact first_eq_one f s hf hs hc
  have hsnd : orderOf f.2=2 := by
    rw [Prod.orderOf,hfst,orderOf_one,Nat.lcm_one_left] at hf
    exact hf
  exact (productCentralizer f hfst).trans
    ((MulEquiv.refl _).prodCongr (reflectionEquiv f.2 hsnd))

end Sporadic.Janko3.SourceRecognition.BaumeisterParabolics.PairCentralizer
