module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.CharacteristicAmalgams.LocalLonger.NormalizedGeometry
public import Theory.GroupTheory.CubicCommutatorQuotient

/-!
# The actual extracted Baumann commutator has cubic quotient

After normalizing the two extractions, their second residual and the
prescribed Baumann subgroup lie in the first-step vertex. That vertex
has quotient S₃ over its two-core. The literal commutator therefore has
a three-group quotient over its own two-core. The original Goldschmidt
triple constructs all witnesses and both S₃ quotient maps.

This discharges the odd-prime quotient step in Stellmacher (9.3), Journal
of Algebra 190 (1997), p.49, for the cubic local problem. Subnormality in
the centralizer of the mixed-center subgroup remains a separate issue.
-/

namespace Stellmacher.SectionNine.LocalLonger
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

/-- The normalized, actually selected residual commutator has a three-group quotient. -/
public theorem residual_baumann_quotient_three
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (e : ((stabilizer ctx.Γ ctx.criticalPath.firstStep) ⧸
      pCore 2 (stabilizer ctx.Γ ctx.criticalPath.firstStep)) ≃* Equiv.Perm (Fin 3))
    (first : FirstConfigurationData ctx) (second : SecondConfigurationData ctx first)
    (config : NormalizedGeometry ctx first second) :
    let R := twoResidualIn (second.E.map (MulAut.conj config.g⁻¹).toMonoidHom)
    let F := ⁅R,baumannIn T⁆
    IsPGroup 3 (F ⧸ pCore 2 F) := by
  let R := twoResidualIn (second.E.map (MulAut.conj config.g⁻¹).toMonoidHom)
  have hRP : R ≤ GAt ctx.Γ ctx.criticalPath.firstStep :=
    (Subgroup.map_subtype_le _).trans config.second_geometry.group_le
  have hBP : baumannIn T ≤ GAt ctx.Γ ctx.criticalPath.firstStep :=
    inf_le_left.trans (ctx.criticalPath.S_le_edge_stabilizers.trans inf_le_right)
  exact SymmetricThreeTwoCore.ambient_commutator_core_quotient_three
    (GAt ctx.Γ ctx.criticalPath.firstStep) R (baumannIn T) e hRP hBP

end Stellmacher.SectionNine.LocalLonger

namespace CFSG.Quasithin.ChapterF
open Theory.GroupTheory Stellmacher Stellmacher.Later Stellmacher.SectionsFiveToSeven
open Stellmacher.SectionsFiveToSeven.CosetGraphContext
open Stellmacher.SectionsFiveToSeven.SevenSix Stellmacher.SectionNine
universe u
variable {G : Type u} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

/-- Construct the normalized extraction and its odd quotient on the original cubic triple. -/
public theorem IsGoldschmidtTriple.exists_normalized_extractions_with_cubic_quotient
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hgood₁ : generalizedFitting G₁ = pCore 2 G₁)
    (hgood₂ : generalizedFitting G₂ = pCore 2 G₂)
    (Γ : CosetGraphContext.{u,u} G (G₁ ⊓ G₂) G₁ G₂) (cp : CriticalPath Γ)
    (hcomm : ⁅z Γ cp.a,z Γ cp.a'⁆ = ⊥)
    (hlarge : 4 < Nat.card (ZAt Γ cp.a)) :
    let ctx : SectionNineLocalContext G (G₁ ⊓ G₂) G₁ G₂ :=
      ⟨h.sectionSeven_of_characteristic_two hcore hgood₁ hgood₂, Γ, cp, hcomm⟩
    ∃ first : LocalLonger.FirstConfigurationData ctx,
      ∃ second : LocalLonger.SecondConfigurationData ctx first,
        ∃ config : LocalLonger.NormalizedGeometry ctx first second,
          let R := twoResidualIn (second.E.map (MulAut.conj config.g⁻¹).toMonoidHom)
          let F := ⁅R,baumannIn (G₁ ⊓ G₂)⁆
          IsPGroup 3 (F ⧸ pCore 2 F) := by
  classical
  let ctx : SectionNineLocalContext G (G₁ ⊓ G₂) G₁ G₂ :=
    ⟨h.sectionSeven_of_characteristic_two hcore hgood₁ hgood₂, Γ, cp, hcomm⟩
  obtain ⟨first, second, ⟨config⟩⟩ := h.exists_normalized_extractions_of_large_center
    hcore hgood₁ hgood₂ Γ cp hcomm hlarge
  have he : Nonempty (((stabilizer Γ cp.firstStep) ⧸
      pCore 2 (stabilizer Γ cp.firstStep)) ≃* Equiv.Perm (Fin 3)) := by
    rcases cp.edge_stabilizers_are_P with he | he
    · rw [show stabilizer Γ cp.firstStep = G₂ from he.2]
      exact h.quotient_right
    · rw [show stabilizer Γ cp.firstStep = G₁ from he.2]
      exact h.quotient_left
  exact ⟨first, second, config,
    LocalLonger.residual_baumann_quotient_three ctx he.some first second config⟩

end CFSG.Quasithin.ChapterF
