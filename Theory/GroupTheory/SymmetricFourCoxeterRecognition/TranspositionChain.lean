module
public import Theory.GroupTheory.SymmetricFourCoxeterRecognition.TranspositionLifts

/-!
# Three transpositions forming a chain

Three distinct transpositions in S₄ whose ends commute satisfy the A₃
relations and generate S₄. This supplies the quotient generation and the
adjacent cubic relations for Goldschmidt's radius-three source labels.
-/

public section
namespace Theory.GroupTheory.SymmetricFourCoxeterRecognition
open Subgroup

private def sixSwap (i : Fin 6) : Equiv.Perm (Fin 4) :=
  ![Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 0 3,
    Equiv.swap 1 2, Equiv.swap 1 3, Equiv.swap 2 3] i

private theorem sixSwap_surjective (a : Transposition) : ∃ i, sixSwap i = a.val := by
  obtain ⟨x,y,hxy,h⟩ := a.property
  rw [h]
  fin_cases x <;> fin_cases y
  all_goals first
    | exact (hxy rfl).elim
    | exact ⟨0,rfl⟩ | exact ⟨1,rfl⟩ | exact ⟨2,rfl⟩
    | exact ⟨3,rfl⟩ | exact ⟨4,rfl⟩ | exact ⟨5,rfl⟩
    | exact ⟨0,Equiv.swap_comm _ _⟩ | exact ⟨1,Equiv.swap_comm _ _⟩
    | exact ⟨2,Equiv.swap_comm _ _⟩ | exact ⟨3,Equiv.swap_comm _ _⟩
    | exact ⟨4,Equiv.swap_comm _ _⟩ | exact ⟨5,Equiv.swap_comm _ _⟩

private theorem sixSwap_chain : ∀ i j k : Fin 6,
    sixSwap i * sixSwap k = sixSwap k * sixSwap i →
    sixSwap i ≠ sixSwap k → sixSwap i ≠ sixSwap j → sixSwap j ≠ sixSwap k →
    (sixSwap i*sixSwap j)^3=1 ∧ (sixSwap j*sixSwap k)^3=1 := by
  decide +kernel

theorem transposition_chain_cubes (a b c : Transposition)
    (hac : Commute a.val c.val) (hneac : a ≠ c) (hneab : a ≠ b) (hnebc : b ≠ c) :
    (a.val*b.val)^3=1 ∧ (b.val*c.val)^3=1 := by
  obtain ⟨i,hi⟩ := sixSwap_surjective a
  obtain ⟨j,hj⟩ := sixSwap_surjective b
  obtain ⟨k,hk⟩ := sixSwap_surjective c
  have hs := sixSwap_chain i j k
  rw [hi,hj,hk] at hs
  exact hs hac.eq (fun h => hneac (Subtype.ext h))
    (fun h => hneab (Subtype.ext h)) (fun h => hnebc (Subtype.ext h))

theorem closure_three_transpositions_eq_top (a b c : Transposition)
    (hac : Commute a.val c.val) (hneac : a ≠ c) (hneab : a ≠ b) (hnebc : b ≠ c) :
    closure ({a.val,b.val,c.val} : Set (Equiv.Perm (Fin 4))) = ⊤ := by
  let H := closure ({a.val,b.val,c.val} : Set (Equiv.Perm (Fin 4)))
  let A : H := ⟨a.val, subset_closure (by simp)⟩
  let B : H := ⟨b.val, subset_closure (by simp)⟩
  let C : H := ⟨c.val, subset_closure (by simp)⟩
  obtain ⟨hAB,hBC⟩ := transposition_chain_cubes a b c hac hneac hneab hnebc
  have hgen : closure ({A,B,C} : Set H)=⊤ := by
    apply (Subgroup.map_injective H.subtype_injective)
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype, MonoidHom.map_closure,
      Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
    rfl
  have sq (x : Transposition) : x.val^2=1 := by
    obtain ⟨i,j,_,hh⟩ := x.property
    rw [hh, pow_two, Equiv.swap_mul_self]
  have ha : A^2=1 := Subtype.ext (sq a)
  have hb : B^2=1 := Subtype.ext (sq b)
  have hc : C^2=1 := Subtype.ext (sq c)
  obtain ⟨e, _, _, _⟩ := exists_marked_equiv A B C ha hb hc
    (Subtype.ext hAB) (Subtype.ext hBC) (Subtype.ext hac.eq) hgen
    (fun hh => by
      have hv : (a : Equiv.Perm (Fin 4)) = c :=
        congrArg (fun x : H => (x : Equiv.Perm (Fin 4))) hh
      exact hneac (Subtype.ext hv))
  have hf : Function.Surjective H.subtype :=
    (Function.Injective.bijective_of_nat_card_le H.subtype_injective
      (le_of_eq (Nat.card_congr e.toEquiv).symm)).2
  have htop := MonoidHom.range_eq_top.mpr hf
  simpa only [Subgroup.range_subtype] using htop

end Theory.GroupTheory.SymmetricFourCoxeterRecognition

