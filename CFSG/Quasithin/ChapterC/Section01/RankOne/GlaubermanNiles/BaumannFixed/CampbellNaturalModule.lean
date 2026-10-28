module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellNaturalModule.Section
public import Theory.SpecificGroups.SL2.NaturalFixedIndex

/-!
# Campbell's fixed-point bound from the actual natural section

The no-partial-complement condition gives S ∩ ker(actor) = Q. Thus an
outside maximum elementary subgroup A has nontrivial two-group image B and
|A:A ∩ Q| = |B|. On the natural plane, |B| is at most the fixed-point index.
The surjective equivariant projection W → F² maps C_W(A) into the fixed
subgroup, so its fixed-point index is at most |W:C_W(A)|. Finally W ≤ E
implies |W:C_W(A)| ≤ |E:C_E(A)|, where E = Ω₁(Z(Q)).

This proves the exact index premise consumed by `CampbellContainment` from
`NaturalSection`. Constructing that section from factorization failure is
still a separate source obligation; this module does not assert it.
The argument needs only that B is a nontrivial two-subgroup, and hence avoids
requiring the stronger S = AQ conclusion of Campbell II.3.2.

Source: N. R. Campbell, *Pushing up in Finite Groups* (1979), Chapter II,
Lemmas 3.1–3.2 and the opening of 4.1, printed pp.24–25.
-/

@[expose] public section

open Theory.GroupTheory Stellmacher Subgroup
open Theory.SpecificGroups.SL2

namespace CFSG.Quasithin.ChapterC.GlaubermanNiles.Campbell

variable {T G : Type*} [Group T] [Group G] [Finite G]

/-- The fixed-index comparison on the literal subgroup and equivariant quotient.
The missing Campbell II.3.2 existence theorem must supply `m`. -/
theorem NaturalSection.omegaFixedIndexBound (d : Embedding T G) (m : NaturalSection d) :
    d.OmegaFixedIndexBound := by
  intro A hA hAQ
  let B := A.map m.actor
  have hSK : (d.sylow : Subgroup G) ⊓ m.actor.ker = pCore 2 G :=
    d.sylow_inf_eq_core _ m.core_le_kernel m.noPartialComplement
  have hAK : m.actor.ker.subgroupOf A = (pCore 2 G).subgroupOf A := by
    ext a
    exact ⟨fun ha => hSK ▸ (show (a : G) ∈ (d.sylow : Subgroup G) ⊓ m.actor.ker from
      ⟨hA.1 a.property, ha⟩), fun ha => m.core_le_kernel ha⟩
  have hcard : (pCore 2 G).relIndex A = Nat.card B := by
    rw [← Subgroup.relIndex_ker A m.actor]
    change ((pCore 2 G).subgroupOf A).index = (m.actor.ker.subgroupOf A).index
    rw [hAK]
  have hB : B ≠ ⊥ := by
    intro hB
    apply hAQ
    intro a ha
    have hma : m.actor a = 1 := by
      have hh : m.actor a ∈ B := Subgroup.mem_map_of_mem m.actor ha
      simpa only [hB, mem_bot] using hh
    have hk : (⟨a, ha⟩ : A) ∈ m.actor.ker.subgroupOf A := hma
    rw [hAK] at hk
    exact hk
  let : IsElementaryAbelian 2 A := hA.2.1
  have hpB : IsPGroup 2 B := (IsElementaryAbelian.isPGroup 2 A).map m.actor
  have hpre : (centralizer (A : Set G)).subgroupOf d.centerClosure ≤
      (NaturalFixedIndex.fixed B).comap m.projection := by
    intro w hw b hb
    obtain ⟨a, ha, rfl⟩ := hb
    have hc : MulAut.conjNormal a w = w := by
      apply Subtype.ext
      change a * (w : G) * a⁻¹ = (w : G)
      have hw' : a * (w : G) = (w : G) * a := hw a ha
      rw [hw', mul_assoc, mul_inv_cancel, mul_one]
    simpa only [hc] using (m.equivariant a w).symm
  have hindex : (NaturalFixedIndex.fixed B).index ≤
      (centralizer (A : Set G)).relIndex d.centerClosure := by
    rw [← (NaturalFixedIndex.fixed B).index_comap_of_surjective m.projection_surjective]
    exact Subgroup.index_antitone hpre
  rw [hcard]
  exact (NaturalFixedIndex.card_le_fixed_index hB hpB).trans
    (hindex.trans (Subgroup.relIndex_le_of_le_right d.centerClosure_le_omegaCore
      Subgroup.index_ne_zero_of_finite))

end CFSG.Quasithin.ChapterC.GlaubermanNiles.Campbell

end
