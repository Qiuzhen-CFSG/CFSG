module

public import Theory.Representation.QuadraticFourGroup.Recognition.OddTranspositions.NormLattice.Coordinates
public import Theory.GroupTheory.GeneralizedFitting.ComponentSwapNormAction
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# Oriented pairs in a four-group component orbit

The marked involution moves every conjugate of the component. If all conjugates
belong to its first pair, there is one pair. Otherwise the four elements
`1, a, b, a*b` give four distinct components and two pairs. The representatives
retain their actual ambient conjugations, with the second member oriented by a.

Source: GLS2, Chapter G, Theorem 25.14, Step 2; Chapter B, Lemma 3.27.
No generation, core, or later recognition hypothesis is used here.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace Representation.QuadraticFourGroup
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L B : Subgroup G} {a : G}
namespace PairConstruction

def conj (L : Subgroup G) (b : G) : Subgroup G := L.map (MulAut.conj b).toMonoidHom
@[simp] theorem conj_one (L : Subgroup G) : conj L 1 = L := by
  change L.map (MulAut.conj 1).toMonoidHom = L
  convert L.map_id using 1
  ext x
  simp
theorem conj_mul (L : Subgroup G) (b c : G) : conj L (b*c) = conj (conj L c) b := by
  simp only [conj, map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]
theorem conj_injective (b : G) : Function.Injective (fun L : Subgroup G => conj L b) :=
  map_injective (MulAut.conj b).injective
theorem square (h : Hypotheses ρ L B a) : a*a=1 := by
  simpa only [pow_two, h.involution] using pow_orderOf_eq_one a
theorem commute (h : Hypotheses ρ L B a) (b : B) : Commute (b : G) a :=
  mem_centralizer_singleton_iff.mp (h.fourGroup_le_centralizer b.property)
theorem conj_swap (h : Hypotheses ρ L B a) (b : B) :
     conj L (a*b) ≠ conj L b := by
  rw [← (commute h b).eq, conj_mul]
  intro he
  exact h.moves (conj_injective (b : G) he)

-- Exhaustion of the actor by a marked pair of generators.
theorem actor_cases [Finite G] (h : Hypotheses ρ L B a) {b : B}
    (hb : (b : G) ≠ 1) (hba : (b : G) ≠ a) (c : B) :
    (c : G) = 1 ∨ (c : G) = a ∨ (c : G) = b ∨ (c : G) = a*b := by
  classical
  let := h.elementary
  let aa : B := ⟨a,h.mem⟩
  have ha : aa ≠ 1 := by
    intro he
    have he' : a = 1 := congrArg Subtype.val he
    simpa [he'] using h.involution
  let : Nontrivial B := ⟨⟨aa,1,ha⟩⟩
  let : IsKleinFour B := ⟨h.card_four, IsElementaryAbelian.exponent_eq_prime⟩
  let : Fintype B := Fintype.ofFinite B
  have hb' : b ≠ 1 := fun he => hb (congrArg Subtype.val he)
  have hab : aa ≠ b := fun he => hba (congrArg Subtype.val he).symm
  have hc : c ∈ ({aa*b, aa, b, 1} : Finset B) := by
    rw [IsKleinFour.eq_finset_univ ha hb' hab]
    exact Finset.mem_univ c
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with he | he | he | he
  · exact Or.inr (Or.inr (Or.inr (congrArg Subtype.val he)))
  · exact Or.inr (Or.inl (congrArg Subtype.val he))
  · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val he)))
  · exact Or.inl (congrArg Subtype.val he)

/-- Representatives of the a-pairs of actual component conjugates. -/
structure Frame (h : Hypotheses ρ L B a) where
  count : ℕ
  pos : 0 < count
  le_two : count ≤ 2
  rep : Fin count → B
  distinct : Function.Injective (fun p : Fin count × Bool =>
    conj L (if p.2 then a * rep p.1 else rep p.1))
  covers : ∀ b : B, ∃ p : Fin count × Bool,
    conj L (b : G) = conj L (if p.2 then a * rep p.1 else rep p.1)

theorem frame_exists [Finite G] (h : Hypotheses ρ L B a) : Nonempty (Frame h) := by
  classical
  have hm : conj L a ≠ L := h.moves
  by_cases hc : ∀ b : B, conj L (b : G) = L ∨ conj L (b : G) = conj L a
  · refine ⟨⟨1, by decide, by decide, fun _ => 1, ?_, ?_⟩⟩
    · rintro ⟨i,s⟩ ⟨j,t⟩ he
      have hi : i = 0 := Subsingleton.elim _ _
      have hj : j = 0 := Subsingleton.elim _ _
      subst i; subst j
      cases s <;> cases t <;>
        simp only [Bool.false_eq_true, ↓reduceIte, Subgroup.coe_one, mul_one, conj_one] at he
      all_goals first | rfl | exact (hm he).elim | exact (hm he.symm).elim
    · intro b
      rcases hc b with hb | hb
      · exact ⟨(0,false), by simpa using hb⟩
      · exact ⟨(0,true), by simpa using hb⟩
  · push Not at hc
    obtain ⟨b,hb,hba⟩ := hc
    have hb1 : (b : G) ≠ 1 := by intro he; simp_all
    have hbaa : (b : G) ≠ a := by intro he; exact hba (congrArg (conj L) he)
    have hca : conj (conj L a) a = L := by rw [← conj_mul, square h, conj_one]
    have hcab : conj L (a*b) ≠ L := by
      intro he
      have hh := congrArg (fun K => conj K a) he
      rw [← conj_mul, ← mul_assoc, square h, one_mul] at hh
      exact hba hh
    have hcaba : conj L (a*b) ≠ conj L a := by
      intro he
      have hh := congrArg (fun K => conj K a) he
      rw [← conj_mul, ← mul_assoc, square h, one_mul, hca] at hh
      exact hb hh
    have habb : conj L (a*b) ≠ conj L b := conj_swap h b
    refine ⟨⟨2, by decide, by decide, ![1,b], ?_, ?_⟩⟩
    · rintro ⟨i,s⟩ ⟨j,t⟩ he
      fin_cases i <;> fin_cases j <;> cases s <;> cases t <;>
        simp at he
      all_goals first | rfl | exact (hm he).elim | exact (hm he.symm).elim |
        exact (hb he).elim | exact (hb he.symm).elim |
        exact (hba he).elim | exact (hba he.symm).elim |
        exact (hcab he).elim | exact (hcab he.symm).elim |
        exact (hcaba he).elim | exact (hcaba he.symm).elim |
        exact (habb he).elim | exact (habb he.symm).elim
    · intro c
      rcases actor_cases h hb1 hbaa c with hc | hc | hc | hc
      · exact ⟨(0,false), by simp [hc]⟩
      · exact ⟨(0,true), by simp [hc]⟩
      · exact ⟨(1,false), by simp [hc]⟩
      · exact ⟨(1,true), by simp [hc]⟩
end PairConstruction
end Representation.QuadraticFourGroup

end
