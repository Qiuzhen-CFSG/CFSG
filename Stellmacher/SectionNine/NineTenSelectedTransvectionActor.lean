module

public import Stellmacher.SectionNine.NineTenGeneratingCriticalPair
public import Stellmacher.SectionNine.NineTenTransvectionCoatom

/-!
# Select a transvection outside the retained first coatom

For the actual normalized terminal neighbor, choose an initial-center element
outside its stabilizer. The first coatom centralizes the neighbor center, so
noncommutation with the initial center guarantees an actor outside that coatom.
Since the initial center lies in first V, this actor escapes the neighbor
stabilizer itself. The terminal two-core fixes that neighbor and is contained
in its stabilizer, so the actor also escapes the terminal core.

The actual second-coatom index then gives full displacement of order two and
quotient displacement of order two for this same actor by the proved
transvection theorem. It can therefore select a canonical factor while also
satisfying the retained first extraction's outside-coatom residual bound.

This makes the support choice after Stellmacher (9.10)(3)--(4), printed p.57,
compatible with both actual extraction witnesses. Both source center
noncontainments and the actual second-coatom index remain explicit inputs.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

public theorem nine_ten_initial_transvection_outside_first_coatom
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hterminalNot : ¬ ZAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.firstStep)
    (hfirstNot : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤ VAt ctx.Γ ctx.criticalPath.a')
    (neighbor : ctx.Γ.Vertex)
    (hneighbor : neighbor ∈ neighborhood ctx.Γ ctx.criticalPath.a')
    (hcenters : ⁅ZAt ctx.Γ ctx.criticalPath.a, ZAt ctx.Γ neighbor⁆ ≠ ⊥)
    (hindex : QuotientCardEq (VAt ctx.Γ ctx.criticalPath.a')
      (VAt ctx.Γ ctx.criticalPath.a' ⊓ GAt ctx.Γ ctx.criticalPath.a) 2) :
    ∃ actor : G, actor ∈ ZAt ctx.Γ ctx.criticalPath.a ∧
      actor ∉ GAt ctx.Γ neighbor ∧ actor ∉ QAt ctx.Γ ctx.criticalPath.a' ∧
      Nat.card (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ : Subgroup G) = 2 ∧
      QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2 := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hcoatom := nine_ten_terminal_neighbor_center_centralizes_first_coatom ctx hb
    hterminalNot neighbor hneighbor
  have hnot : ¬ ZAt Γ cp.a ≤ VAt Γ cp.firstStep ⊓ GAt Γ neighbor := by
    intro hle
    apply hcenters
    apply le_antisymm _ bot_le
    exact (Subgroup.commutator_mono hle le_rfl).trans hcoatom.le
  obtain ⟨actor, hactor, hactorNot⟩ := Set.not_subset.mp hnot
  have hcontain := (lemma_seven_four ctx.sectionSeven Γ cp).first_containment
  have hactorNotGroup : actor ∉ GAt Γ neighbor := by
    intro hgroup
    exact hactorNot ⟨hcontain.1 hactor, hgroup⟩
  have hcore : QAt Γ cp.a' ≤ GAt Γ neighbor :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core cp.a' neighbor hneighbor default).2.2
  have hactorNotCore : actor ∉ QAt Γ cp.a' := fun hmem => hactorNotGroup (hcore hmem)
  obtain ⟨hcard, hquotient⟩ := nine_ten_transvection_of_coatom ctx hb hfirstNot
    hindex actor hactor hactorNotCore
  exact ⟨actor, hactor, hactorNotGroup, hactorNotCore, hcard, hquotient⟩

end Stellmacher.SectionNine
