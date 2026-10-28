module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation.Assembly

/-!
# The actual core action from the earlier commutator identity

The original section map U → U/V₁ is onto and equivariant. If the
commutator [U,O₂(H)] lies in V₁, every element of O₂(H) therefore acts
trivially on this section. This constructs the descent input used by the
permitted rechoice and all rank-three calculations from the genuine
14.5.21 commutator identity, without a second action hypothesis.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
14.5.15(4), 14.5.21(1), and proof of 14.7.70, printed pp.1073–1074.
-/

public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.SourceCompletion
open Subgroup Representation Chapter12.Section08 LocalGeometry LocalGeometry.Preparation
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

/-- Literal conjugation makes the two-core trivial on the original quotient. -/
theorem core_action_of_commutator_le (hc : ⁅F.U, F.H.pCoreIn 2⁆ ≤ F.Vi 1) :
    ∀ x : F.H, x ∈ pCore 2 F.H → d.action x = 1 := by
  intro x hx
  apply LinearMap.ext
  intro w
  obtain ⟨a, ha⟩ := d.conjugationSection.onto (Multiplicative.ofAdd w)
  have hw : w ∈ tilde d F.U :=
    (d.conjugationSection.mem_imageSpace_iff _ _).mpr ⟨a, a.property,
      congrArg Multiplicative.toAdd ha⟩
  have hcomm : ⁅F.H.pCoreIn 2, F.U⁆ ≤ F.Vi 1 := by
    rwa [commutator_comm]
  exact d.conjugationSection.fixed_on_imageSpace_of_commutator_le
    (F.H.pCoreIn 2) F.U hcomm x (mem_map.mpr ⟨x, hx, rfl⟩) w hw

/-- The permitted rechoice uses only the earlier nontrivial commutator
identity; its separate core-action premise has been discharged. -/
theorem exists_prepared_of_commutator (c : CriticalPath (L := L) F)
    (earlier : c.EarlierImages) (selection : c.RankSelection)
    (h69 : Nat.card (star F c.Uα) = 2) (separation : d.ModuleSeparation)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (h68 : {x : G | IsConj d.z x} ∩ (d.U₀ : Set G) = {d.z})
    (mark : UpperMarking d) (actors : MarkedSpans.LocalActors d)
    (hUH : F.U ≤ conjugate F.H c.conjugator)
    (heven : (F.U.subgroupOf (conjugate F.H c.conjugator)).map (reciprocalQuotient d c) ≤
      alternatingGroup (Fin 5)) :
    ∃ n : group F L, (n : G) ∈ F.Li L 1 ∧
      Prepared d (c.reselect n)
        (d.actionDescentOfCore (core_action_of_commutator_le d hcomm.le)) :=
  exists_prepared_rechoice d c earlier selection h69 separation
    (core_action_of_commutator_le d hcomm.le) hcomm h68 mark actors hUH heven

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.SourceCompletion
