module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicExclusionCoreGeometry
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicConstructionSmallAssembly

/-!
# The cyclic-block consumer at the remaining core module reconstruction

All odd-subgroup construction, numerical reduction, component placement,
core displacement, central-cover exclusion and the final T-orbit contradiction
are applied here on the original subgroups. The remaining explicit premise
is the source construction of a Frattini-fixed q in O₂(H) whose T-orbit
and V generate O₂(L). Its L₃(2) module proof and final cyclic-block assembly
remain with qt-d-12213-cyclic-block. This conditional theorem does not claim
the completed source result. The earlier natural analysis is discharged by
qt-d-12213-local-configuration.
Source: Aschbacher–Smith, 12.2.21–24, printed pp.802–804.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {d : ℕ}

/-- Apply every proved local calculation and the terminal orbit contradiction.
Only the actual fixed orbit generator remains to be constructed by this owner. -/
theorem cyclicLocalAnalysis_of_extraspecial_core_orbits
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (orbitStep : ∀ p H P U W g v,
      InvariantOddLocalAnalysis T L V d p H P U W g v →
      IsExtraspecial p P → Nat.card P = p ^ 3 → Monoid.exponent P = p →
      W ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) = ⊥ →
      p = 3 → d = 3 → Nat.card W = 64 →
      (frattini P).map P.subtype ≤ L → W ≤ L →
      Nat.card (W ⊓ L.pCoreIn 2 : Subgroup G) = 16 →
      ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2, L⁆ = L.pCoreIn 2 →
      ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2, (frattini P).map P.subtype⁆ =
        W ⊓ (L ⊔ (T : Subgroup G)).pCoreIn 2 →
      W ≤ centralizer (H.pCoreIn 2 : Set G) →
      H ≤ normalizer ((H.pCoreIn 2 ⊓ centralizer
        (((frattini P).map P.subtype : Subgroup G) : Set G) : Subgroup G) : Set G) →
      ∃ q ∈ H.pCoreIn 2 ⊓ centralizer
          (((frattini P).map P.subtype : Subgroup G) : Set G),
        L.pCoreIn 2 = componentOrbit (zpowers q) (T : Subgroup G) ⊔ V) :
    ∃ H P U, CyclicLocalAnalysis T L V d H P U := by
  have hTV := ((structural G T L h).2.2 V D).1
  apply cyclicLocalAnalysis_of_terminal_core h D structural A hnone hTI
  intro p H P U W g v S he hc hx hf hp hd hW hcent _ hnorm
  apply S.extraspecial_false_of_core_orbit D A hTV he hc hf hp hd hW
  exact orbitStep p H P U W g v S he hc hx hf hp hd hW
    (S.extraspecial_frattini_le_component D A hTV he hf hd)
    (S.extraspecial_module_le_component D A hTV he hf hd)
    (S.extraspecial_module_intersection_component_core_card D A hTV he hf hd hW)
    (S.extraspecial_join_core_component_commutator h D A hTV he hf hd hW)
    (S.extraspecial_join_core_displacement D A hTV he hf hd) hcent hnorm

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
