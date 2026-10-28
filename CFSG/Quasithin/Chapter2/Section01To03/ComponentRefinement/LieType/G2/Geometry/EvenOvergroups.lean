module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.Geometry.EvenOvergroups.Pullback
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.Setup
public import Theory.GroupTheory.ComponentLocalOrbitEmbedding

/-!
# Even overgroups of the marked G₂ parabolics

Each pulled-back parabolic has characteristic two. Apply the component-orbit
core calculation inside H: distinct component conjugates commute, repeated
local factors agree by relative-normalizer invariance, and the orbit has a
two-group upper quotient after adjoining the whole Sylow subgroup. The
resulting overgroup therefore has a self-centralizing two-core. It contains
the source involution z, so this core is nontrivial, proving every clause of
HeOver, not merely the centralizer condition.

The first assertion takes precisely the nonbinary short-parabolic core
calculation as an additional input. The long assertion is unconditional.
Both retain the derived binary model and arbitrary permitted central covers
of G₂(4); the Sylow subgroup may permute components. Once coordinates have
been supplied, the inner-action witness is no longer needed for this transfer.
It is retained in the paired entry point for the source assembly contract.

Source: Aschbacher–Smith, 1.1.5(3)(a,b), printed pp.501–502, and the proof
of 2.3.9(7), p.526. This completes the conditional transfer helper; the parent
geometry assembly must discharge the nonbinary short-parabolic premise.
-/

public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2

open Subgroup Atlas.G2.LieParabolicSetup Theory.GroupTheory
variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

private theorem local_overgroup_mem_HeOver
    (h : LocalSetup H L M S z) (K : Subgroup L)
    (hinv : (S : Subgroup H).map H.subtype ⊓ normalizer (L : Set G) ≤
      normalizer (K.map L.subtype : Set G))
    (hself : centralizer (pCore 2 K : Set K) ≤ pCore 2 K) :
    K.map L.subtype ⊔ (S : Subgroup H).map H.subtype ∈
      Chapter1.HeOver G ((S : Subgroup H).map H.subtype : Set G) := by
  let := h.finite
  have hselfP : K.map L.subtype ⊓ centralizer ((K.map L.subtype).pCoreIn 2 : Set G) ≤
      (K.map L.subtype).pCoreIn 2 := by
    rw [← map_pCoreIn_of_injective 2 K L.subtype L.subtype_injective]
    exact (inf_centralizer_map_le_iff K (K.pCoreIn 2) L.subtype L.subtype_injective).mpr
      ((inf_centralizer_pCoreIn_le_iff 2 K).mpr hself)
  have he := h.component.relative_local_adjoin_centralizer h.component_le
    (map_subtype_le K) (map_subtype_le (S : Subgroup H))
    (S.isPGroup'.map H.subtype) hinv hselfP
  refine ⟨he, ?_, fun x hx => (le_sup_right : (S : Subgroup H).map H.subtype ≤
    K.map L.subtype ⊔ (S : Subgroup H).map H.subtype) hx⟩
  intro hbot
  rw [hbot] at he
  have hz := he ⟨(le_sup_right : (S : Subgroup H).map H.subtype ≤
    K.map L.subtype ⊔ (S : Subgroup H).map H.subtype) h.mem_sylow, by
      apply mem_centralizer_iff.mpr
      intro y hy
      have hy1 : y = 1 := hy
      simp [hy1]⟩
  have hz1 : z = 1 := hz
  simpa [hz1] using h.involution

namespace ParabolicCoordinates

/-- The short overgroup has a nontrivial self-centralizing two-core and
contains the full supplied Sylow subgroup. -/
theorem firstOvergroup_mem_HeOver (h : LocalSetup H L M S z)
    (d : ParabolicCoordinates L ((S : Subgroup H).map H.subtype))
    (hshort : 2 < Nat.card d.field →
      centralizer (pCore 2 (parabolic₁ (F := d.field)) : Set (parabolic₁ (F := d.field))) ≤
        pCore 2 (parabolic₁ (F := d.field))) :
    d.firstOvergroup ∈ Chapter1.HeOver G ((S : Subgroup H).map H.subtype : Set G) := by
  let := h.finite
  exact local_overgroup_mem_HeOver h (parabolic₁.comap d.modelMap) d.first_invariant
    (d.first_pullback_centralizer_pCore hshort)

/-- The long overgroup belongs to HeOver in all the permitted model cases. -/
theorem secondOvergroup_mem_HeOver (h : LocalSetup H L M S z)
    (d : ParabolicCoordinates L ((S : Subgroup H).map H.subtype)) :
    d.secondOvergroup ∈ Chapter1.HeOver G ((S : Subgroup H).map H.subtype : Set G) := by
  let := h.finite
  exact local_overgroup_mem_HeOver h (parabolic₂.comap d.modelMap) d.second_invariant
    d.second_pullback_centralizer_pCore

/-- Conditional G₂ transfer for the source assembly, including nontriviality
of both embedded two-cores. The only remaining model input is the nonbinary
short-parabolic calculation. -/
theorem overgroups_mem_HeOver (h : LocalSetup H L M S z)
    (d : ParabolicCoordinates L ((S : Subgroup H).map H.subtype))
    (_hinner : ∃ t : L, IsConjugationProjection L z t)
    (hshort : 2 < Nat.card d.field →
      centralizer (pCore 2 (parabolic₁ (F := d.field)) : Set (parabolic₁ (F := d.field))) ≤
        pCore 2 (parabolic₁ (F := d.field))) :
    d.firstOvergroup ∈ Chapter1.HeOver G ((S : Subgroup H).map H.subtype : Set G) ∧
      d.secondOvergroup ∈ Chapter1.HeOver G ((S : Subgroup H).map H.subtype : Set G) :=
  ⟨d.firstOvergroup_mem_HeOver h hshort, d.secondOvergroup_mem_HeOver h⟩

end ParabolicCoordinates
end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2

end
