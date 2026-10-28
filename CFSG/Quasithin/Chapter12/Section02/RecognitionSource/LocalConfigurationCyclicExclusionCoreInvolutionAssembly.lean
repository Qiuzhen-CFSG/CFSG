module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicExclusionCoreInvolutions
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicConstructionSmallAssembly

/-!
# Applying the fixed-involution reduction in the cyclic-block branch

The literal star quotient and the extraspecial automorphism bound place
any Frattini-fixed involution in O₂(H) times the original inverter. Removing
that inverter preserves the T-orbit span modulo V, so the proved final
contradiction now consumes an involutory orbit generator in O₂(L).

Constructing that generator from the L₃(2) action on O₂(L)/V is still the
terminal source obligation of qt-d-12213-cyclic-block. This conditional
application does not claim 12.2.23. The final source-theorem owner
qt-d-12213-local-configuration discharges the earlier natural analysis.
Source: Aschbacher–Smith, 12.2.23–24, printed p.804.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {d : ℕ}

/-- Apply the original subgroup calculations and the fixed-involution
placement to the cyclic-block consumer. Its remaining module premise is
discharged by this same source owner, qt-d-12213-cyclic-block. -/
theorem cyclicLocalAnalysis_of_extraspecial_fixed_involution_orbits
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (moduleStep : ∀ p H P U W g v,
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
      ∃ t ∈ L.pCoreIn 2 ⊓ centralizer
          (((frattini P).map P.subtype : Subgroup G) : Set G),
        t ^ 2 = 1 ∧ L.pCoreIn 2 = componentOrbit (zpowers t) (T : Subgroup G) ⊔ V) :
    ∃ H P U, CyclicLocalAnalysis T L V d H P U := by
  have hTV := ((structural G T L h).2.2 V D).1
  apply cyclicLocalAnalysis_of_terminal_core h D structural A hnone hTI
  intro p H P U W g v S he hc hx hf hp hd hW hcent _ hnorm
  apply S.extraspecial_false_of_fixed_involution_orbit D A hTV he hc hf hp hd hW
  exact moduleStep p H P U W g v S he hc hx hf hp hd hW
    (S.extraspecial_frattini_le_component D A hTV he hf hd)
    (S.extraspecial_module_le_component D A hTV he hf hd)
    (S.extraspecial_module_intersection_component_core_card D A hTV he hf hd hW)
    (S.extraspecial_join_core_component_commutator h D A hTV he hf hd hW)
    (S.extraspecial_join_core_displacement D A hTV he hf hd) hcent hnorm

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
