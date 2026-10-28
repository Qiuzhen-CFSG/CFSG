module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Base
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.StabilizerWords
public import Theory.GroupAction.GeneratorStabilizerReduction

/-!
# Faithfulness reductions for the Fi₂₃ lift

The eight word-defined points in `Base` belong to the literal restriction
orbit. A certified Schreier chain ending in the trivial subgroup therefore
proves faithfulness. Alternatively, the chain can be split after four points:
the first half places a kernel element in a specified intermediate subgroup,
and the second half proves that its remaining four fixed points force identity.

The concrete Schreier transitions remain to be certified. These conditional
results are not the unconditional theorem `action_injective` and do not identify
the lifted subgroup with Fi₂₃. Source: GLS3 Table 5.3v and the Fi₂₄′ paragraph
in `refs/KGroup/GLS3/Chapter5(sec3-).tex`, line 1053; ATLAS F24G1-p306936B0.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift

/-- The shared word lists give the initial and terminal groups. Only their
eight actual point-stabilizer inclusions remain to be checked. -/
theorem action_injective_of_wordStage_reductions
    (step : ∀ i : Fin 8, ∀ g : Carrier, g ∈ wordStage i.castSucc →
      g.val (basePoint i) = basePoint i → g ∈ wordStage i.succ) :
    Function.Injective action := by
  apply action_injective_iff.mpr
  intro g hfix
  have hmem : ∀ i : Fin 9, g.val ∈ wordStage i := by
    intro i
    induction i using Fin.induction with
    | zero => rw [wordStage_zero]; exact g.property
    | succ i ih => exact step i g.val ih (hfix (baseLetter i))
  have ht := hmem (Fin.last 8)
  rw [wordStage_last, Subgroup.mem_bot] at ht
  exact Subtype.ext ht

/-- Independent certificates for the first and last four transitions compose
at the literal shared subgroup `wordStage 4`. -/
theorem action_injective_of_wordStage_halves
    (first : ∀ i : Fin 4, ∀ g : Carrier, g ∈ wordStage (i.castAdd 4).castSucc →
      g.val (basePoint (i.castAdd 4)) = basePoint (i.castAdd 4) →
      g ∈ wordStage (i.castAdd 4).succ)
    (last : ∀ i : Fin 4, ∀ g : Carrier, g ∈ wordStage (i.natAdd 4).castSucc →
      g.val (basePoint (i.natAdd 4)) = basePoint (i.natAdd 4) →
      g ∈ wordStage (i.natAdd 4).succ) : Function.Injective action := by
  apply action_injective_of_wordStage_reductions
  intro i
  induction i using Fin.addCases (m := 4) (n := 4) with
  | left i => exact first i
  | right i => exact last i

/-- A chain of actual generator/representative equalities discharges faithfulness
of the exact orbit restriction. No group-order comparison is involved. -/
theorem action_injective_of_generator_reductions {A : Type*}
    (groups : Fin 9 → Subgroup Carrier)
    (generators : Fin 8 → A → Carrier)
    (generated : ∀ i, Subgroup.closure (Set.range (generators i)) = groups i.castSucc)
    (indices : Fin 8 → Type*)
    (certificates : ∀ i,
      Subgroup.GeneratorStabilizerReduction (generators i) (groups i.succ)
        (basePoint i) (indices i))
    (initial : groups 0 = liftedGroup) (terminal : groups (Fin.last 8) = ⊥) :
    Function.Injective action := by
  apply action_injective_iff.mpr
  intro g hfix
  have hg : g.val ∈ groups 0 := by rw [initial]; exact g.property
  have ht := Subgroup.mem_of_generatorStabilizerReductions groups basePoint
    generators generated indices certificates hg (fun i => hfix (baseLetter i))
  rw [terminal, Subgroup.mem_bot] at ht
  exact Subtype.ext ht

/-- The concrete chain may be checked in two independent halves sharing an
explicit intermediate subgroup. Both remaining certificate obligations stay
visible in this assembly theorem. -/
theorem action_injective_of_split_stabilizer (middle : Subgroup Carrier)
    (first : ∀ g : liftedGroup,
      (∀ i : Fin 4, g.val.val (basePoint (i.castAdd 4)) = basePoint (i.castAdd 4)) →
      g.val ∈ middle)
    (last : ∀ g : Carrier, g ∈ middle →
      (∀ i : Fin 4, g.val (basePoint (i.natAdd 4)) = basePoint (i.natAdd 4)) → g = 1) :
    Function.Injective action := by
  apply action_injective_iff.mpr
  intro g hfix
  apply Subtype.ext
  exact last g.val (first g (fun i => hfix (baseLetter (i.castAdd 4))))
    (fun i => hfix (baseLetter (i.natAdd 4)))

end Sporadic.Fischer.Fi24Prime.Fi23Lift
