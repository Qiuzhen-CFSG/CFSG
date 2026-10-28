module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Contracts
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.ThreeElements
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.FixedNine.FixedElements
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.FixedNine.Permutation
public import Stellmacher.CharacteristicTwoCoreOvergroup
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# The fixed nine in the block-selection argument

A cubic actor cannot move a block to a distinct commuting conjugate in
three-rank at most two: its three conjugate three-elements would generate
an elementary group of order twenty-seven. Once the actor normalizes both
blocks, orbit counting constructs a fixed three-element in each. The two
fixed elements generate the required elementary nine.

The remaining structural input below is the specialization of C.1.9 to
a block and its conjugate. It is explicitly a premise, not an assertion
that C.1.9 has been proved. Its extra A₃ hypothesis is discharged here for
the actual upper core O₂,₃(H), the preimage of O₃(H/O₂(H)). Final assembly
still needs the block-commutation theorem and transport of the block data
to the relative ambient group H.

Source: Aschbacher–Smith, proof of E.6.14, printed p.251 (PDF p.262),
and C.1.9, printed p.123 (PDF p.134).
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection

/-- The exact remaining specialization of block commutation. Neither
normalization of L by x nor any fixed element is assumed. -/
def ConjugateBlockCommutationInput (G : Type*) [Group G] : Prop :=
  ∀ H L : Subgroup G, HasCharacteristicTwo H → L ≤ H →
    ChapterC.IsChiZeroBlock L → (L.subgroupOf H).IsSubnormal →
    ∀ x ∈ normalizer (H : Set G), orderOf x = 3 →
      L.map (MulAut.conj x) ≠ L →
        L.map (MulAut.conj x) ≤ centralizer (L : Set G)

variable {G : Type*} [Group G] [Finite G]

/-- Characteristic two discharges the extra O₂,₃ hypothesis of C.1.9,
including when the ambient group has an A₃-block. The subgroup is the
literal preimage of the three-core of the two-core quotient. -/
theorem twoThreeCore_generalizedFitting (h : HasCharacteristicTwo G) :
    let D := (pCore 3 (G ⧸ pCore 2 G)).comap (QuotientGroup.mk' (pCore 2 G))
    generalizedFitting D = pCore 2 D := by
  dsimp only
  apply generalizedFitting_eq_pCore_of_selfCentralizing 2
  apply Stellmacher.characteristicTwo_of_contains_core h
  intro g hg
  change QuotientGroup.mk' (pCore 2 G) g ∈ pCore 3 (G ⧸ pCore 2 G)
  have hk : g ∈ (QuotientGroup.mk' (pCore 2 G)).ker := by
    simpa only [QuotientGroup.ker_mk'] using hg
  rw [MonoidHom.mem_ker.mp hk]
  exact one_mem _

/-- Conditional assembly of the requested fixed-nine statement. Only the
specialization of C.1.9 remains; all normalization, actual fixed elements,
independence and elementary-group cardinalities are proved here. -/
theorem fixedNineInput_of_conjugate_commutation
    (hc : ConjugateBlockCommutationInput G) : FixedNineInput G := by
  intro N H L₁ L₂ hHN hnormal hchar hrank h₁H h₂H h₁ h₂ hs₁ hs₂ hcomm x hxN hx
  have hxH : x ∈ normalizer (H : Set G) :=
    ((normal_subgroupOf_iff_le_normalizer hHN).mp hnormal) hxN
  have hn₁ := normalizes_of_conjugate_commutation (h₁H.trans hHN) hrank h₁ hxN hx
    (hc H L₁ hchar h₁H h₁ hs₁ x hxH hx)
  have hn₂ := normalizes_of_conjugate_commutation (h₂H.trans hHN) hrank h₂ hxN hx
    (hc H L₂ hchar h₂H h₂ hs₂ x hxH hx)
  obtain ⟨E, he, hcard, hEL, hEx⟩ := fixed_nine_of_normalizes h₁ h₂ hcomm hx hn₁ hn₂
  exact ⟨E, he, hcard, hEL.trans (sup_le h₁H h₂H), hEx⟩

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
