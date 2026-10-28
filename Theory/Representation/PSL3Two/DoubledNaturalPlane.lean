module
public import Theory.Representation.PSL3Two.NaturalSylowFixed

/-!
# Natural copies containing a Sylow-fixed point in the doubled binary module

The fixed space of a Sylow two-subgroup on the natural SL₃(2)-module has
at most two elements. Thus a fixed pair has one zero coordinate or equal
coordinates. It lies in one of the two summands or their diagonal, each an
invariant subgroup of order eight. The moving-plane consumer uses this point
and the transitivity of a two-perfect action on the nonidentity plane elements.

Source: Aschbacher--Smith, original 14.6.10(5), printed p.1029.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace BinaryLinearThree.DoubledNaturalPlane

/-- The two summands and their diagonal. -/
def copyMap (i : Fin 3) : Multiplicative Vector →* Multiplicative (Vector × Vector) where
  toFun x := Multiplicative.ofAdd <| if i = 0 then (0,x.toAdd)
    else if i = 1 then (x.toAdd,0) else (x.toAdd,x.toAdd)
  map_one' := by split_ifs <;> rfl
  map_mul' x y := by split_ifs <;> rfl

theorem copyMap_injective (i : Fin 3) : Function.Injective (copyMap i) := by
  intro x y h
  fin_cases i
  · exact congrArg (fun z => z.toAdd.2) h
  · exact congrArg (fun z => z.toAdd.1) h
  · exact congrArg (fun z => z.toAdd.1) h

theorem card_copy (i : Fin 3) : Nat.card (copyMap i).range = 8 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (copyMap_injective i)).toEquiv]
  change Nat.card Vector = 8
  simp [Vector, Matrix.PSL3Two.Fano.Vector]

theorem copy_stable (i : Fin 3) (g : Group) (x : Multiplicative (Vector × Vector))
    (hx : x ∈ (copyMap i).range) :
    Multiplicative.ofAdd ((W.prod W) g x.toAdd) ∈ (copyMap i).range := by
  obtain ⟨y,rfl⟩ := hx
  refine ⟨Multiplicative.ofAdd (W g y.toAdd), ?_⟩
  fin_cases i <;> apply Multiplicative.toAdd.injective <;>
    simp [copyMap, Representation.prod, map_zero]

theorem fixed_pair_mem_copy (P : Sylow 2 Group) (x : Vector × Vector)
    (hx : ∀ p : P, (W.prod W) p x = x) :
    ∃ i : Fin 3, Multiplicative.ofAdd x ∈ (copyMap i).range := by
  let D := fixedSpace W (P : Subgroup Group)
  have hx1 : x.1 ∈ D := fun p => congrArg Prod.fst (hx p)
  have hx2 : x.2 ∈ D := fun p => congrArg Prod.snd (hx p)
  by_cases h1 : x.1 = 0
  · exact ⟨0,Multiplicative.ofAdd x.2,Prod.ext h1.symm rfl⟩
  by_cases h2 : x.2 = 0
  · exact ⟨1,Multiplicative.ofAdd x.1,Prod.ext rfl h2.symm⟩
  have hn : Nontrivial D := ⟨⟨⟨x.1,hx1⟩,0,fun he => h1 (congrArg Subtype.val he)⟩⟩
  let := hn
  have hc : Nat.card D = 2 := le_antisymm (card_sylow_natural_fixed_le_two P)
    (Nat.succ_le_of_lt (Finite.one_lt_card (α := D)))
  have he := ((Nat.card_eq_two_iff' (0 : D)).mp hc).unique
    (show (⟨x.1,hx1⟩ : D) ≠ 0 from fun h => h1 (congrArg Subtype.val h))
    (show (⟨x.2,hx2⟩ : D) ≠ 0 from fun h => h2 (congrArg Subtype.val h))
  exact ⟨2,Multiplicative.ofAdd x.1,Prod.ext rfl (congrArg Subtype.val he)⟩
end BinaryLinearThree.DoubledNaturalPlane
