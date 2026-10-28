module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.NaturalCoreModels.SourceWitnesses.Summands
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.NaturalCoreModels.SourceWitnesses.StarCentralizer
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.NaturalCoreModels.SourceWitnesses.SourceMarking

/-!
# Excluding the two natural small-core alternatives

The genuine whole-core C.1.34 models and marked V₂-plane supply the same
quotient marking for the full star-centralizer calculation and each natural
summand. The cubic residual element gives nonzero intersections and hence
conjugate generation. The checked perfectness reduction then centralizes Q,
and the existing marked central-cover argument gives the source contradiction.

The earlier MS classification and construction of the marked whole-core
coordinates remain the responsibility of their source producers. No
centralizer, summand, generation or centralization conclusion is assumed here.

Source: Aschbacher–Smith, proof of 15.3.31, printed p.1132 (PDF p.1149).
-/

@[expose] public section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.NaturalCoreModels.SourceWitnesses
open CentralCover CentralCover.LinearModels LinearThree
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {L : Subgroup G} {ρ : Representation (ZMod 2) SL V}

private def recoordinateCore (m : AbelianCore L ρ) (a : SL) : AbelianCore L ρ where
  quotientIso := m.quotientIso.trans (MulAut.conj a)
  equiv := m.equiv.trans (FullCenter.actionEquiv (ρ := ρ) a)
  action l x y hxy := by
    change Multiplicative.ofAdd (ρ a (m.equiv y).toAdd) = _
    rw [m.action l x y hxy]
    apply congrArg Multiplicative.ofAdd
    change ρ a (ρ (m.quotientIso (QuotientGroup.mk' (pCore 2 L) l)) (m.equiv x).toAdd) =
      ρ (a * m.quotientIso (QuotientGroup.mk' (pCore 2 L) l) * a⁻¹)
        (ρ a (m.equiv x).toAdd)
    rw [map_mul, map_mul]
    simp only [Module.End.mul_apply, inv_self_apply]

private theorem recoordinateCore_actor (m : AbelianCore L ρ)
    {Y : Subgroup G} (n : MarkedModel m.fullCenter Y) :
    (recoordinateCore m n.changeOfCoordinates).fullCenter.actor = n.model.actorMap := by
  apply MonoidHom.ext
  intro l
  change (m.quotientIso.trans (MulAut.conj n.changeOfCoordinates))
      (QuotientGroup.mk' (pCore 2 L) l) =
    n.model.quotientIso (QuotientGroup.mk' (pCore 2 L) l)
  rw [n.quotient_marking]
  rfl

variable [Finite G] {κ : GroupClass} {d : LocalData G} {I : Subgroup G}
  {c : ComponentWitness d I}

/-- The first natural source case centralizes the actual core, with no generation premise. -/
theorem one_centralizes_core (s : SourceData κ d c)
    [IsSimpleGroup (c.L ⧸ pCore 2 c.L)]
    (m : AbelianCore c.L natural) (p : MarkedPlane m.fullCenter d.V₂) :
    yplusCentralizer d I ≤ centralizer (extensionCore c.L : Set G) := by
  obtain ⟨n⟩ := LinearModels.caseOne m p s.component_parabolic s.component_residual
  have hr : planeRotation ∈ (d.Yplus.subgroupOf c.L).map
      (recoordinateCore m n.changeOfCoordinates).fullCenter.actor := by
    rw [recoordinateCore_actor m n]
    exact n.rotation_mem
  have hQ : IsMulCommutative (extensionCore c.L) := by
    rw [← m.center_eq]
    exact m.fullCenter.elementary.toIsMulCommutative
  exact s.centralizes_core_of_star_centralizer_and_generation
    (star_centralizer_eq_bot s n) hQ
    (one_generation s (recoordinateCore m n.changeOfCoordinates) hr)

/-- The doubled natural source case uses one actor marking on both actual copies. -/
theorem two_centralizes_core (s : SourceData κ d c)
    [IsSimpleGroup (c.L ⧸ pCore 2 c.L)]
    (m : AbelianCore c.L (natural.prod natural)) (p : MarkedPlane m.fullCenter d.V₂) :
    yplusCentralizer d I ≤ centralizer (extensionCore c.L : Set G) := by
  obtain ⟨n⟩ := LinearModels.caseTwo m p s.component_parabolic s.component_residual
  have hr : planeRotation ∈ (d.Yplus.subgroupOf c.L).map
      (recoordinateCore m n.changeOfCoordinates).fullCenter.actor := by
    rw [recoordinateCore_actor m n]
    exact n.rotation_mem
  have hQ : IsMulCommutative (extensionCore c.L) := by
    rw [← m.center_eq]
    exact m.fullCenter.elementary.toIsMulCommutative
  exact s.centralizes_core_of_star_centralizer_and_generation
    (star_centralizer_eq_bot s n) hQ
    (two_generation s (recoordinateCore m n.changeOfCoordinates) hr)

/-- The actual first natural case contradicts the source V₁ normalizer bound. -/
theorem excluded_one (s : SourceData κ d c)
    [IsSimpleGroup (c.L ⧸ pCore 2 c.L)]
    (m : AbelianCore c.L natural) (p : MarkedPlane m.fullCenter d.V₂) : False :=
  s.excluded_of_models (.linearOne m p) (one_centralizes_core s m p)

/-- The actual doubled case contradicts the same source bound without dropping a copy. -/
theorem excluded_two (s : SourceData κ d c)
    [IsSimpleGroup (c.L ⧸ pCore 2 c.L)]
    (m : AbelianCore c.L (natural.prod natural)) (p : MarkedPlane m.fullCenter d.V₂) : False :=
  s.excluded_of_models (.linearTwo m p) (two_centralizes_core s m p)

/-- The literal C.1.34(1) section from the original MS output is excluded. -/
theorem excluded_one_source (s : SourceData κ d c)
    (ms : MarkedMS.SmallMSConclusion κ d c s.normal s.generated s.characteristicTwo
      s.sylow s.sylow_eq)
    (e : (c.L ⧸ pCore 2 c.L) ≃* SL)
    (h : Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.HasSectionModel
      c.L (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.msQ c.L d.S) ⊥
      (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.linearThreeActor e)
      natural) : False := by
  let := ms.simple
  obtain ⟨m, _⟩ := abelianCore_of_section e natural (by
    simpa only [ms.core_eq,
      Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.linearThreeActor]
      using h)
  obtain ⟨p⟩ := SourceMarking.one s m
  exact excluded_one s m p

/-- The literal C.1.34(2) section is excluded with both copies and its original actor. -/
theorem excluded_two_source (s : SourceData κ d c)
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    (ms : MarkedMS.SmallMSConclusion κ d c s.normal s.generated s.characteristicTwo
      s.sylow s.sylow_eq)
    (e : (c.L ⧸ pCore 2 c.L) ≃* SL)
    (h : Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.HasSectionModel
      c.L (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.msQ c.L d.S) ⊥
      (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.linearThreeActor e)
      (natural.prod natural)) : False := by
  let := ms.simple
  obtain ⟨m, _⟩ := abelianCore_of_section e (natural.prod natural) (by
    simpa only [ms.core_eq,
      Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.linearThreeActor]
      using h)
  obtain ⟨p⟩ := SourceMarking.two s hm ms m
  exact excluded_two s m p

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.NaturalCoreModels.SourceWitnesses
