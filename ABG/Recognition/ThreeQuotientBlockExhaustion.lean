module

public import ABG.Recognition.ThreeQuotientSections
public import Theory.Character.ModularBlock.OddClassNonvanishing

/-!
# Exhausting the ambient principal block

For an involution with odd conjugacy-class cardinality and odd-core centralizer
quotient GL₂(3), the eight induced candidates exhaust any prescribed principal
congruence block. A row outside the catalog vanishes at the involution by the
restriction calculation, whereas principal-block congruence forbids that zero.
Source: ABG III.5--6 and the ordinary central-character congruence criterion.
-/

namespace ABG
open ModularBlock.PrincipalBlockConstruction
noncomputable section
attribute [local instance] Fintype.ofFinite

variable {G : Type*} [Group G] [Finite G] (x : G)
local notation "C" => Subgroup.centralizer (Set.singleton x)

/-- Every actual principal-block row is one of the eight induced candidates. -/
public theorem threeQuotient_principalBlock_exhaustion (hx : orderOf x = 2)
    (hodd : Odd (Nat.card (ConjClasses.mk x).carrier))
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1)
    (d : ThreeCharacterDecomposition (threeQuotientInducedGenerator x e))
    (b : PrincipalCongruenceBlockData G) (i : b.I) (hi : i ∈ b.block) :
    ∃ j : Fin 8, b.chi i = d.principalConjCandidate j := by
  classical
  by_contra hn
  push Not at hn
  have hz := threeQuotient_principalBlock_other_vanishes x e d b hx i hi hn
    ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ (Subgroup.mem_zpowers x)
  exact b.character_ne_zero_of_odd_class i hi (ConjClasses.mk x) hodd hz

/-- Odd involution-class size promotes the eight principal candidates to the
whole ambient principal block, independently of any degree congruences. -/
public theorem threeQuotient_principalBlock_card (hx : orderOf x = 2)
    (hodd : Odd (Nat.card (ConjClasses.mk x).carrier))
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1)
    (d : ThreeCharacterDecomposition (threeQuotientInducedGenerator x e))
    (b : PrincipalCongruenceBlockData G) : b.block.card = 8 := by
  classical
  choose f hf he using threeQuotient_principalConjCandidate_mem x e d b hx
  let row : Fin 8 → {i : b.I // i ∈ b.block} := fun j => ⟨f j, hf j⟩
  have hinj : Function.Injective row := by
    intro j k hjk
    apply d.principalConjCandidate_injective
    rw [← he j, ← he k]
    exact congrArg b.chi (congrArg Subtype.val hjk)
  have hsurj : Function.Surjective row := by
    intro i
    obtain ⟨j, hj⟩ := threeQuotient_principalBlock_exhaustion x hx hodd e d b i.val i.property
    refine ⟨j, Subtype.ext (b.complete.2.2 ?_)⟩
    exact (he j).trans hj.symm
  have hc := Fintype.card_congr (Equiv.ofBijective row ⟨hinj, hsurj⟩)
  simpa using hc.symm

end
end ABG
