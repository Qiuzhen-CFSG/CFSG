module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Normalizers
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.ModuleCover
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.ModuleTransport
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.Selection
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.ForwardAssembly
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.PartitionFusion
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.Reversal

/-!
# The critical image has order two: 14.7.69

Positive relative rank in the actual critical selection gives nontriviality
of Uα*. The Sylow calculation leaves order two or Uα*=Q*. In the latter
branch the original marked module and the genuine dual sections give
V₁≰Uα and E×V₁=U₀V, where E=U∩Uα.

The equal critical ranks permit the universal earlier 14.7.39/F.9.17
reversal. Its two path markings transport the actual point centralizers,
two-core kernels, original module partitions and single-commutator set.
No element interchanging both endpoints is assumed. Hyperplane uniqueness
excludes |U₀|=2 and 8; the original-section fixedness and 14.7.68(2)
exclude |U₀|=4. This proves the literal order-two conclusion.

Only the authorized preceding source results remain explicit. In particular
`EarlierSymmetry` produces a reversed geometric path and critical selection;
it contains no local target conclusion. `SourceSelection` retains the rank
comparison and the actual quadratic action of Notation 14.7.1. The module
marking inputs identify V by its L₁ action. The source owners of the earlier
implications are listed at the theorem. Final 14.7.66–70 assembly remains
with qt-14-07-local-critical-fusion.

The re-exported original-section identities and displacement formulas retain
W, its projection p, the actual H action and the quotient kernel V₁ for the
subsequent 14.7.70 application.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 14.7.1 and Remark 14.7.39, printed pp.1043, 1060;
Lemmas 14.7.66–69, pp.1070–1073.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Subgroup Representation Chapter12.Section08
open scoped commutatorElement
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {X Y : Type u} [AddCommGroup X] [Module (ZMod 2) X]
  [AddCommGroup Y] [Module (ZMod 2) Y]

namespace Data
variable (d : Data T L V F W)

/-- Aschbacher–Smith 14.7.69, using the literal star map and critical actor.

The retained premises are earlier source facts: 14.5.15(4), 14.5.21,
14.7.2(1), the 14.3.3(6)/14.7 local actor implications, universal
14.7.39/F.9.17 symmetry, and the two conclusions of 14.7.68. Their
producers are qt-14-05, qt-14-05-terminal-duality, qt-14-03, qt-14-07,
and qt-14-07-critical-residual-fusion. No critical intersection,
partition, reciprocal centralizer, rank exclusion or nontrivial star
image is assumed. The positive rank and quadratic selection retain
Notation 14.7.1 on the actual critical path. -/
theorem lemma_14_7_69
    (hc : d.SectionCentralizer) (sep : d.ModuleSeparation)
    (s : CriticalIntersections.SourceDuality F X Y)
    (actors : ∀ (a : CriticalPath (L := L) F), a.EarlierImages →
      ∀ b : d.CriticalChart hc a, b.LocalActors)
    (symmetry : d.EarlierSymmetry)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (fusion : {x : G | IsConj d.z x} ∩ (d.U₀ : Set G) = {d.z})
    (unique : ∀ u : F.U, (u : G) ∈ d.U₀ → (u : G) ≠ 1 →
      (∀ t : T, d.action ⟨t, F.invariant 1 t.property⟩
        (d.conjugationSection.coordinates u).toAdd =
          (d.conjugationSection.coordinates u).toAdd) →
      centralizer ({(u : G)} : Set G) ≤ F.H ∧
        ∀ g : G, (u : G) ∈ conjugate d.U₀ g → conjugate d.U₀ g = d.U₀)
    (c : CriticalPath (L := L) F) (earlier : c.EarlierImages)
    (selection : c.SourceSelection d)
    (hUH : F.U ≤ conjugate F.H c.conjugator) :
    Nat.card (star F c.Uα) = 2 := by
  rcases c.order_two_or_full d earlier selection.toRankSelection with htwo | hfull
  · exact htwo
  exfalso
  obtain ⟨b⟩ := d.exists_criticalChart hc c earlier hfull
  have hb := actors c earlier b
  have hm := b.moduleCalculations earlier sep hb
  have hrank := CriticalIntersections.equal_critical_ranks d hc sep c earlier hUH hm hcomm hfull
  obtain ⟨r⟩ := symmetry c earlier selection (hrank.1.trans hrank.2.symm)
  have hrfull := r.full_image d earlier hfull
  obtain ⟨b'⟩ := d.exists_criticalChart hc r.path r.earlier hrfull
  have hb' := actors r.path r.earlier b'
  have hUH' := r.reverse_placement d earlier
  have h := b.ambientComplement_of_full_image earlier sep hb s hUH hcomm hfull
  have h' := b'.ambientComplement_of_full_image r.earlier sep hb' s hUH' hcomm hrfull
  have hpoint := b.point_not_le_critical earlier sep hb s hUH hcomm hfull
  rcases d.card_U₀_cases hc with htwo | hfour | height
  · exact b.rank_one_fusion_contradiction h earlier sep hb hpoint htwo b' h'
      r.conjugator r.base_U r.tip_U
  · have hp := b.rank_two_partition_right_transport h earlier sep hb hUH hcomm hfour
      b' h' r.earlier hb' hUH' r.conjugator r.base_U r.tip_U
    exact b.rank_two_fusion_contradiction h earlier sep hb hUH hpoint hfour fusion unique
      r.conjugator r.base_U hp
  · have hp := b.rank_three_partition_right_transport h earlier sep hb hUH hcomm
      b' h' r.earlier hb' hUH' r.conjugator r.base_U r.tip_U
    exact b.rank_three_fusion_contradiction h earlier sep hb hUH hpoint height fusion
      r.conjugator r.base_U hp

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
