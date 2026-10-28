module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.OrdinaryConstruction.GeneralizedRows.PowerLabels.Orbits

/-!
# Orienting the ordinary class labels

Disjoint swaps on the two order-ten classes, the two order-fifteen classes,
and the last two order-nineteen classes preserve both census functions and
fix the identity. The prime and mixed-order orbit theorems choose these swaps
so that 10A squared and 15A cubed belong to 5B, and squaring cycles 19A to 19B
to 19C. The relabelled census retains its actual representatives and classes.

The finite seeds recorded here are proved from the census and order, and
are expanded to all powers in `Table`. Source: Janko's ordinary-class
calculation, J. Algebra 3 (1966), 147–186; Gorenstein, printed p.482.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters
namespace PowerLabelConstruction
variable {G : Type*} [Group G] [Finite G] (c : OrdinaryClassData G)

@[expose] public def labelPerm (a b d : Bool) : Fin 15 ≃ Fin 15 :=
  ((if a then Equiv.swap 7 8 else Equiv.refl _).trans
    (if b then Equiv.swap 10 11 else Equiv.refl _)).trans
    (if d then Equiv.swap 13 14 else Equiv.refl _)

public theorem labelPerm_zero (a b d : Bool) : labelPerm a b d 0 = 0 := by
  revert a b d; decide +kernel

public theorem labelPerm_order (a b d : Bool) (j : Fin 15) :
    classOrder (labelPerm a b d j) = classOrder j := by
  revert a b d j; decide +kernel

public theorem labelPerm_centralizer (a b d : Bool) (j : Fin 15) :
    centralizerOrder (labelPerm a b d j) = centralizerOrder j := by
  revert a b d j; decide +kernel

@[expose] public noncomputable def relabel (a b d : Bool) : OrdinaryClassData G where
  representatives j := c.representatives (labelPerm a b d j)
  classes := (labelPerm a b d).trans c.classes
  classes_eq j := c.classes_eq _
  identity := by rw [labelPerm_zero, c.identity]
  orders j := (c.orders _).trans (labelPerm_order a b d j)
  centralizers j := (c.centralizers _).trans (labelPerm_centralizer a b d j)

public theorem power_relabel (a b d : Bool) (j : Fin 15) (n : ℕ) :
    power (relabel c a b d) j n =
      (labelPerm a b d).symm (power c (labelPerm a b d j) n) := rfl

public structure Aligned (c : OrdinaryClassData G) : Prop where
  five : power c 3 2 = 4 ∧ power c 4 2 = 3
  ten : power c 7 2 = 4 ∧ power c 8 2 = 3
  fifteen : power c 10 3 = 4 ∧ power c 11 3 = 3
  nineteen : power c 12 2 = 13 ∧ power c 13 2 = 14 ∧ power c 14 2 = 12

public theorem exists_aligned (horder : Nat.card G = 175560) :
    ∃ a b d, Aligned (relabel c a b d) := by
  have h5 := square_five c horder
  have h10 := mixed_ten c h5
  have h15 := mixed_fifteen c h5
  have h19 := square_nineteen c horder
  rcases h10 with h10 | h10 <;>
    rcases h15 with h15 | h15 <;>
    rcases h19 with h19 | h19
  · refine ⟨true, true, false, ?_⟩
    constructor <;>
      simp [power_relabel, labelPerm, Equiv.swap_apply_def, h5.1, h5.2,
        h10.1, h10.2, h15.1, h15.2, h19.1, h19.2.1, h19.2.2]
  · refine ⟨true, true, true, ?_⟩
    constructor <;>
      simp [power_relabel, labelPerm, Equiv.swap_apply_def, h5.1, h5.2,
        h10.1, h10.2, h15.1, h15.2, h19.1, h19.2.1, h19.2.2]
  · refine ⟨true, false, false, ?_⟩
    constructor <;>
      simp [power_relabel, labelPerm, Equiv.swap_apply_def, h5.1, h5.2,
        h10.1, h10.2, h15.1, h15.2, h19.1, h19.2.1, h19.2.2]
  · refine ⟨true, false, true, ?_⟩
    constructor <;>
      simp [power_relabel, labelPerm, Equiv.swap_apply_def, h5.1, h5.2,
        h10.1, h10.2, h15.1, h15.2, h19.1, h19.2.1, h19.2.2]
  · refine ⟨false, true, false, ?_⟩
    constructor <;>
      simp [power_relabel, labelPerm, Equiv.swap_apply_def, h5.1, h5.2,
        h10.1, h10.2, h15.1, h15.2, h19.1, h19.2.1, h19.2.2]
  · refine ⟨false, true, true, ?_⟩
    constructor <;>
      simp [power_relabel, labelPerm, Equiv.swap_apply_def, h5.1, h5.2,
        h10.1, h10.2, h15.1, h15.2, h19.1, h19.2.1, h19.2.2]
  · refine ⟨false, false, false, ?_⟩
    constructor <;>
      simp [power_relabel, labelPerm, h5.1, h5.2,
        h10.1, h10.2, h15.1, h15.2, h19.1, h19.2.1, h19.2.2]
  · refine ⟨false, false, true, ?_⟩
    constructor <;>
      simp [power_relabel, labelPerm, Equiv.swap_apply_def, h5.1, h5.2,
        h10.1, h10.2, h15.1, h15.2, h19.1, h19.2.1, h19.2.2]
end PowerLabelConstruction
end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters
