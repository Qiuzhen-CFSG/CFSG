module

public import Stellmacher.SectionEight.EightTwoBackwardHallOrbitReduction
public import Stellmacher.SectionEight.EightTwoBackwardNativeModuleUpper

/-!
# The actual native-module Hall orbit in Stellmacher (8.2)

Assume first-step noncentrality, critical length greater than one, and
normality of the first-edge core intersection in the initial stabilizer.
For the smaller group L = Ea Qfirst, retain any supplied Sylow T with
ambient image Qfirst. Its native Section Two module has Hall orbit exactly
Vfirst under any supplied odd complement to the edge Sylow in Gfirst.

The native-module upper bound places each generator in Vfirst, which is
normalized by Gfirst, so its Hall orbit remains there. Conversely, the
normal-supplement comparison puts Za inside the ambient native module.
The Hall orbit of Za is Vfirst by local graph transitivity and the exact
Sylow-complement factorization. Monotonicity gives the reverse inclusion.
No identification of L with Ga or of the native module with Za is needed.
Oddness is retained for the subsequent application of (2.5), although
the orbit comparison itself only needs the complement property.

Source: Stellmacher (8.2), first containment case, Journal of Algebra 190
(1997), printed pp.37–38, refs/latex/stellmacher-n-group.tex. This supplies
the actual orbit identification for the separate (2.5) normality assembly.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem eight_two_backward_hall_module_orbit
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlen : 1 < ctx.criticalPath.length)
    (hnormal : NormalIn
      (QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
      (GAt ctx.Γ ctx.criticalPath.a)) :
    let L := EAt ctx.Γ ctx.criticalPath.a ⊔ QAt ctx.Γ ctx.criticalPath.firstStep
    let Pb := GAt ctx.Γ ctx.criticalPath.firstStep
    ∀ (T : Sylow 2 L), (T : Subgroup L).map L.subtype = QAt ctx.Γ ctx.criticalPath.firstStep →
    ∀ (W : Sylow 2 Pb), (W : Subgroup Pb).map Pb.subtype = S →
    ∀ (U : Subgroup Pb), Odd (Nat.card U) → (W : Subgroup Pb).IsComplement' U →
      conjugateClosure ((SectionTwo.vSubgroup T).map L.subtype) (U.map Pb.subtype) =
        VAt ctx.Γ ctx.criticalPath.firstStep := by
  dsimp only
  intro T hT W hW U _hodd hcomp
  have hupper := eight_two_backward_native_module_le_neighbor ctx hcenter hlen hnormal T hT
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro element ⟨actor, generator, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp
      (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.firstStep
        (Subgroup.map_subtype_le U actor.property)) generator).mp
          (hupper generator.property)
  · rw [← eight_two_backward_vertex_hall_orbit ctx W hW U hcomp]
    apply Subgroup.closure_mono
    rintro element ⟨actor, generator, rfl⟩
    exact ⟨actor, ⟨generator,
      eight_two_backward_vertex_le_native_module ctx hnormal T hT generator.property⟩, rfl⟩

end Stellmacher.SectionEight
