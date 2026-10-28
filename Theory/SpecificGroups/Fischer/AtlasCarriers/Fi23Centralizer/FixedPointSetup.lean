module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23
public import Theory.GroupAction.CentralizerFixedPointSection

/-!
# Explicit Fi23 word and fixed-point action

These definitions fix the exact permutation data for the centralizer calculation.
The candidate is the seventh power of `(a*b^2)*(a*b^2)*(a*b)^3` in the ATLAS
carrier. Its centralizer acts on its fixed letters by restriction. No order,
image identification, or kernel-size claim is part of these definitions.

Source: the Fi23 representation `F23G1-p31671B0`; the centralizer to be
constructed is the `2Fi22` in GLS volume 3, Table 5.3u and its explanatory
Fischer paragraph in `refs/KGroup/GLS3/Chapter5(sec3-).tex`, line 1042.
-/

@[expose] public section

namespace Sporadic.Fischer.Fi23.CentralizerSection

open Theory.GroupAction

/-- The first published generator as an element of the generated group. -/
def a : Carrier := ⟨generatorA, Subgroup.subset_closure (by simp)⟩

/-- The second published generator as an element of the generated group. -/
def b : Carrier := ⟨generatorB, Subgroup.subset_closure (by simp)⟩

/-- An explicit word whose order-14 certificate is still needed. -/
def word : Carrier := (a * b ^ 2) * (a * b ^ 2) * (a * b) ^ 3

/-- The proposed class-2A involution; its order is not assumed by this definition. -/
def candidate : Carrier := word ^ 7

/-- The centralizer in the actual ATLAS Fi23 group. -/
abbrev numerator : Subgroup Carrier :=
  CentralizerFixedPointSection.Centralizer candidate

/-- The exact fixed-point set on the 31671 ATLAS letters. -/
abbrev FixedLetters := CentralizerFixedPointSection.FixedPoints inclusion candidate

/-- Restriction of the centralizer action to the exact fixed-point set. -/
def fixedPointAction : numerator →* Equiv.Perm FixedLetters :=
  CentralizerFixedPointSection.action inclusion candidate

end Sporadic.Fischer.Fi23.CentralizerSection
