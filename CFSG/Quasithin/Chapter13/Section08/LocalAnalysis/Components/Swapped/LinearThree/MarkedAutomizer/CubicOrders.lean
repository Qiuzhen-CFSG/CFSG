module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.MarkedAutomizer.SourceMarking
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.ResidualDirections
public import Theory.Representation.HexacodeAction.CubicLocalModel.Orders.CentralCubicSymmetricFour
public import Theory.GroupTheory.CComponent.HexacodeTheta.ExponentThree

/-!
# Cubic orders for the two actual covered marks

The coordinate map makes each binary point stabilizer in the hexacode cover
an actual central cubic extension of S₄. The existing intrinsic commutator
calculation, together with the cover's absence of elements of order nine,
gives a cubic quotient for its derived subgroup. The proved source marking
and the two-group kernel of the literal quotient map transport this result
to L₁,₊. The center calculation gives the cubic quotient of L₀.

These are the two orders in Aschbacher–Smith, Notation 13.2.1, printed
p.877, used in the automizer calculation of 13.8.16(1), p.952 (PDF p.969).
No cubic order or quotient coordinates are assumed.
-/

@[expose] public section
open Subgroup Theory.SpecificGroups.SymmetricSix
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.MarkedAutomizer
namespace CubicOrders
open Representation.Hexacode.CubicLocalModel.Orders

private noncomputable def pointEquiv (x : BinaryPoint) :
    MulAction.stabilizer A6 x ≃* Equiv.Perm (Fin 4) := by
  have he : MulAction.stabilizer A6 x =
      MulAction.stabilizer A6 (duadPolarEquiv.symm x) := by
    ext g
    change g.val • x = x ↔ g.val • duadPolarEquiv.symm x = duadPolarEquiv.symm x
    rw [← duadPolarEquiv.injective.eq_iff, duadPolarEquiv_equivariant]
    simp
  let g := Classical.choose (a6_duad_transitive 0 (duadPolarEquiv.symm x))
  have hg := Classical.choose_spec (a6_duad_transitive 0 (duadPolarEquiv.symm x))
  exact (MulEquiv.subgroupCongr he).trans
    ((MulAction.stabilizerEquivStabilizer hg.symm).symm.trans
      ((MulEquiv.subgroupCongr a6_duad_stabilizer_zero).trans a6DuadModelEquiv.symm))

private theorem parabolic_quotient (x : BinaryPoint) :
    ∃ f : Model.parabolic x →* Equiv.Perm (Fin 4),
      Function.Surjective f ∧ f.ker ≤ center (Model.parabolic x) ∧ Nat.card f.ker = 3 := by
  let c : Model.parabolic x →* MulAction.stabilizer A6 x :=
    Atlas.Codes.hexEvenCoordinate.subgroupComap (MulAction.stabilizer A6 x)
  have hc : Function.Surjective c := by
    intro y
    obtain ⟨g, hg⟩ := Atlas.Codes.hexEvenCoordinate_surjective y.val
    exact ⟨⟨g, by change Atlas.Codes.hexEvenCoordinate g ∈ MulAction.stabilizer A6 x
                  rw [hg]; exact y.property⟩, Subtype.ext hg⟩
  let f := (pointEquiv x).toMonoidHom.comp c
  have hk : f.ker.map (Model.parabolic x).subtype = center Model.Cover := by
    rw [← Representation.Hexacode.even_kernel_eq_center]
    ext g
    constructor
    · rintro ⟨a, ha, rfl⟩
      have he : c a = 1 := (pointEquiv x).injective
        ((show pointEquiv x (c a) = 1 from ha).trans (map_one _).symm)
      exact congrArg Subtype.val he
    · intro hg
      have hm : g ∈ Model.parabolic x := by
        change Atlas.Codes.hexEvenCoordinate g ∈ MulAction.stabilizer A6 x
        rw [show Atlas.Codes.hexEvenCoordinate g = 1 from hg]
        exact one_mem _
      refine ⟨⟨g, hm⟩, ?_, rfl⟩
      change pointEquiv x (c ⟨g, hm⟩) = 1
      rw [show c ⟨g, hm⟩ = 1 from Subtype.ext hg, map_one]
  refine ⟨f, (pointEquiv x).surjective.comp hc, ?_, ?_⟩
  · intro a ha
    have hz : (a : Model.Cover) ∈ center Model.Cover := hk ▸ mem_map_of_mem _ ha
    rw [mem_center_iff]
    intro b
    exact Subtype.ext (mem_center_iff.mp hz b.val)
  · rw [← card_map_of_injective (Model.parabolic x).subtype_injective, hk,
      Representation.Hexacode.even_center_card]

/-- The intrinsic derived subgroup of the covered point stabilizer has cubic
quotient by its own two-core. -/
theorem derived_core_card (x : BinaryPoint) :
    Nat.card (commutator (Model.parabolic x) ⧸ pCore 2 (commutator (Model.parabolic x))) = 3 := by
  obtain ⟨f, hf, hk, hc⟩ := parabolic_quotient x
  let U : Sylow 2 (Model.parabolic x) := Classical.choice inferInstance
  have h := intrinsicCommutatorResidual_quotient_card_of_central_cubic_s4 f hf hc hk
    (fun g hg => Subtype.ext (Theory.GroupTheory.HexacodeTheta.cube_eq_one_of_ninth
      (congrArg Subtype.val hg))) U
  have he := ModelCommutator.central_symmetric_residual_commutator f hf hk U
  change Nat.card (intrinsicCommutatorResidual U ⧸ pCore 2 (intrinsicCommutatorResidual U)) = 3 at h
  change intrinsicCommutatorResidual U = commutator (Model.parabolic x) at he
  rwa [he] at h

variable {G : Type*} [Group G] [Finite G]
variable {L V : Subgroup G} {hLV : L ≤ normalizer (V : Set G)}

/-- Two-core quotients of the actual source subgroup and its cover image agree. -/
noncomputable def coreImageEquiv (d : CoverPointModel L V hLV)
    (A : Subgroup G) (hAL : A ≤ L) :
    (A ⧸ pCore 2 A) ≃* ((d.subgroupMap A hAL).range ⧸
      pCore 2 (d.subgroupMap A hAL).range) := by
  let f := (d.subgroupMap A hAL).rangeRestrict
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_rangeRestrict, d.subgroupMap_ker]
    exact pCore_isPGroup.comap_of_injective (inclusion hAL) (inclusion_injective hAL)
  let q := (QuotientGroup.mk' (pCore 2 (d.subgroupMap A hAL).range)).comp f
  have hker : q.ker = pCore 2 A := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact f.comap_pCore_of_ker_isPGroup (d.subgroupMap A hAL).rangeRestrict_surjective hk
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q
      ((QuotientGroup.mk'_surjective _).comp (d.subgroupMap A hAL).rangeRestrict_surjective))

open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement

/-- The scalar source quotient is cubic, from the actual cover center. -/
theorem zero_core_card (d : CoverPointModel L V hLV) :
    Nat.card (zero L ⧸ pCore 2 (zero L)) = 3 := by
  have he : (d.subgroupMap (zero L) (zero_le L)).range = center Model.Cover := by
    rw [d.subgroupMap_range, d.zero_image]
  let e := (coreImageEquiv d (zero L) (zero_le L)).trans
    (QuotientGroup.congr _ _ (MulEquiv.subgroupCongr he)
      (pCore_map_iso 2 (MulEquiv.subgroupCongr he)))
  have hp : pCore 2 (center Model.Cover) = ⊥ := by
    have h3 : IsPGroup 3 (center Model.Cover) := IsPGroup.of_card (n := 1)
      (by simpa using Representation.Hexacode.even_center_card)
    have hd := IsPGroup.disjoint_of_ne 2 3 (by decide)
      (pCore 2 (center Model.Cover)) (⊤ : Subgroup (center Model.Cover))
      pCore_isPGroup (h3.to_subgroup ⊤)
    simpa using hd.eq_bot
  rw [Nat.card_congr e.toEquiv, hp,
    Nat.card_congr (QuotientGroup.quotientBot (G := center Model.Cover)).toEquiv,
    Representation.Hexacode.even_center_card]

/-- The plus source quotient is cubic, using the proved model commutator mark. -/
theorem plus_core_card (d : CoverPointModel L V hLV)
    (T V₁ : Subgroup G) (hn : T ≤ normalizer (L : Set G))
    (S : Sylow 2 (L ⊔ T : Subgroup G))
    (hS : (S : Subgroup (L ⊔ T : Subgroup G)) = T.subgroupOf (L ⊔ T))
    (hTV : T ≤ normalizer (V₁ : Set G))
    (hV₁V : V₁ ≤ V) (hc : Nat.card V₁ = 2) :
    Nat.card (plus L T V₁ ⧸ pCore 2 (plus L T V₁)) = 3 := by
  obtain ⟨z, hz, _⟩ := (Nat.card_eq_two_iff' (1 : V₁)).mp hc
  let x := d.markedPoint V₁ hV₁V z hz
  obtain ⟨U, hU⟩ := d.exists_coverSylow T hn S hS
  have hUP : (U : Subgroup Model.Cover) ≤ Model.parabolic x := by
    rw [hU]
    exact d.sourceSylow_image_le_parabolic T V₁ hTV hV₁V hc z hz
  have he : (d.subgroupMap (plus L T V₁) (LocalAction.plus_le_L L T V₁ hn)).range =
      (commutator (Model.parabolic x)).map (Model.parabolic x).subtype := by
    rw [d.subgroupMap_range,
      d.plus_image T V₁ (CoverPointModel.source_isPGroup T S hS) hn hV₁V hc z hz, ← hU]
    exact Model.commutator_residual_eq_derived x U hUP
  let e := (MulEquiv.subgroupCongr he).trans
    ((commutator (Model.parabolic x)).equivMapOfInjective (Model.parabolic x).subtype
      (Model.parabolic x).subtype_injective).symm
  let q := (coreImageEquiv d (plus L T V₁) (LocalAction.plus_le_L L T V₁ hn)).trans
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))
  exact (Nat.card_congr q.toEquiv).trans (derived_core_card x)

end CubicOrders
end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.MarkedAutomizer
end
