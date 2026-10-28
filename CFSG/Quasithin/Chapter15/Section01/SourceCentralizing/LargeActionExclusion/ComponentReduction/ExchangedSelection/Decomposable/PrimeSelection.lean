module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Decomposable.PrimeResidual
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Decomposable.SylowGeometry

/-!
# The original decomposable marker in prime three

The original Thompson four-group has prime residual order, the required
Sylow centralizer and central-seed bound, and generates M together with T.
These facts construct the pre-exclusion marker directly from the original
decomposition and action. Its fixed and moved planes are the same two
sixteen-element supports. The parent Decomposable module applies component
selection to this marker and retains the same pre-exclusion witness through
the exchanged-source construction.

The prime-five marker and its exclusion remain with the exchanged-selection
owner. The earlier 15.1.14 residual is discharged by the parent large-component
reduction; it is not needed to construct the marker itself.

Source: Aschbacher--Smith 15.1.16(a)--18 and 15.1.25, printed pp.1092--1093
and 1102, with the prime-three calculation of 15.1.10, printed p.1089.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.DecomposableMarker
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Construct every source-marker field and its actual exchanged-plane
geometry for the same original prime-three Thompson marking. -/
theorem ThompsonPair.preExclusionMarker_of_prime_three
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M) (hfull : V = Section03.localModule T M)
    (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (hd : d.FittingFull)
    (s : ThompsonPair (T := T) hn c d)
    (π : internalActionImage M V hn →* Equiv.Perm d.Index)
    (hp : ∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g k)).actor)
    (hs : ∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V hn g) =
      (c.ambientFactor d (π g k)).space)
    (hJ : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict =
      ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict ⊓
        Jhat (imageRepresentation M V hn))
    (hthree : s.prime = 3) :
    ∃ m : CaseIPreExclusionMarker T M V hn,
      m.Z1 = thompsonPlane T V (c.ambientFactor d s.first).space ∧
      m.prime = s.prime ∧ m.row = .six ∧
      ∀ {Mc : Subgroup G} (e : CaseIComponentData T M Mc V),
        e.Z1 = m.Z1 → e.row = m.row → e.ExchangedPlaneGeometry := by
  have hfour := s.support_four_not_dvd_of_prime_three hG T hM hfull hn c d hd π hp hs hthree s.first
  let Z := thompsonPlane T V (c.ambientFactor d s.first).space
  have hZne : Z ≠ ⊥ := by
    intro he
    have hc : Nat.card Z = 4 := s.thompson_card s.first
    rw [he,card_bot] at hc
    norm_num at hc
  let m : CaseIPreExclusionMarker T M V hn := {
    row := .six
    Z1 := Z
    prime := s.prime
    prime_prime := hthree ▸ Nat.prime_three
    marked_fixed := inf_le_right
    marked_nontrivial := hZne
    generates := s.generation_of_prime_three hG T hM hn c d π hp hs hthree
    local_sylow := s.local_sylow hM.1.2 hn c d π hs
    sylow_normal := (s.sylow_geometry_of_support_four_not_dvd hM.1.2 hn c d hfour).2.2.1
    residual_card := s.full_quotient_residual_card_of_prime_three hG T hM hn c d π hp hs hJ hthree
    seed_bound := (s.full_residual_bounds hM.1.2 hn c d hJ).2.2 }
  exact ⟨m,rfl,rfl,rfl,fun e hZ hr =>
    s.exchangedPlaneGeometry_of_support_four_not_dvd hM.1.2 hn c d π hp hs hJ hfour e hZ hr⟩

end CFSG.Quasithin.Chapter15.Section01.DecomposableMarker
