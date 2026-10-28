module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Thompson
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Assembly

/-!
# Transporting the marked orthogonal section to the Thompson comparison

The natural moved section is defined on the ambient subgroup W_K. The
Thompson argument uses the same subgroup inside K T_v. The canonical
subgroup equivalence identifies these binary modules and intertwines their
conjugation actions through the original plus map and chosen S₈ marking.

Pulling back the actual moved subspace and its fixed subspace gives the
literal quotient U_K/C_{U_K}(K), with its existing natural coordinates.
Thus no complement, split extension or new actor is selected. Given the
image of the actual X T_v, this constructs Thompson.Marking and proves
J(O₂(X T_v)) = J(O₂(K T_v)). The source-configuration consumer also
constructs every field of EarlierData from the same source selection and
its intrinsic K/O₂(K) ≃ SL₄(2) identification.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, concluding
paragraph after 13.6.23, printed p.933.
-/

public section
open scoped IsMulCommutative MatrixGroups
open Subgroup Stellmacher Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Thompson
open ComponentSelection LocalAction.OrthogonalModule
open Theory.SpecificGroups.SymmetricEight
variable {G : Type*} [Group G] [Finite G]
    {K L T : Subgroup G} {z v : G}
    (d : EarlierData K L T z v)
    [IsElementaryAbelian 2 (WK K L T z v)]
    (m : NaturalMovedSection K L T z v d.normalizeL d.fixSeed)

private noncomputable def internalEquiv : Additive d.internalW ≃ₗ[ZMod 2] Additive (WK K L T z v) := by
  let e : d.internalW ≃* WK K L T z v := subgroupOfEquivOfLe d.WK_le_actor
  exact LinearEquiv.ofBijective (e.toMonoidHom.toAdditive.toZModLinearMap 2) e.bijective

private theorem internalEquiv_apply (w : Additive d.internalW) :
    ((internalEquiv d w).toMul : G) = ((w.toMul : plusActor K L T v) : G) := by rfl

private theorem internalEquiv_equivariant (g : Equiv.Perm (Fin 8)) (w : Additive d.internalW) :
    internalEquiv d (d.modelRepresentation m.actor g w) =
      representation K L T z v d.normalizeL d.fixSeed (m.actor.symm g) (internalEquiv d w) := by
  obtain ⟨a, rfl⟩ := d.modelMap_surjective m.actor g
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [internalEquiv_apply]
  have he := congrArg (fun x : plusActor K L T v => (x : G))
    (Representation.NormalElementaryQuotient.representation_apply d.internalW
      (d.modelMap m.actor) (d.modelMap_surjective m.actor) (d.modelMap_ker m.actor) a w)
  change _ = ((plusAction K L T z v d.normalizeL d.fixSeed
    (m.actor.symm (m.actor (plusMk K L T z v d.normalizeL d.fixSeed a)))
    (internalEquiv d w).toMul : WK K L T z v) : G)
  rw [m.actor.symm_apply_apply, plusAction_mk_apply]
  simpa only [internalEquiv_apply, Subgroup.coe_mul, Subgroup.coe_inv,
    EarlierData.modelRepresentation] using he

private noncomputable def transportedUpper : Subrepresentation (d.modelRepresentation m.actor) where
  toSubmodule := m.upper.toSubmodule.comap (internalEquiv d).toLinearMap
  apply_mem_toSubmodule g := by
    intro w hw
    change internalEquiv d (d.modelRepresentation m.actor g w) ∈ m.upper.toSubmodule
    rw [internalEquiv_equivariant]
    exact m.upper.apply_mem_toSubmodule _ hw

private noncomputable def transportedLower : Subrepresentation (d.modelRepresentation m.actor) where
  toSubmodule := (m.central.toSubmodule.map m.upper.toSubmodule.subtype).comap
    (internalEquiv d).toLinearMap
  apply_mem_toSubmodule g := by
    rintro w ⟨u, hu, he⟩
    refine ⟨m.upper.toRepresentation (m.actor.symm g) u,
      m.central.apply_mem_toSubmodule _ hu, ?_⟩
    change representation K L T z v d.normalizeL d.fixSeed (m.actor.symm g) u.val =
      internalEquiv d (d.modelRepresentation m.actor g w)
    rw [internalEquiv_equivariant]
    exact congrArg _ he

private noncomputable def upperEquiv :
    (transportedUpper d m).toSubmodule ≃ₗ[ZMod 2] m.upper.toSubmodule :=
  (internalEquiv d).ofSubmodule' m.upper.toSubmodule

private theorem lower_map :
    (sectionLower (d.modelRepresentation m.actor) (transportedLower d m)
      (transportedUpper d m)).toSubmodule.map (upperEquiv d m).toLinearMap =
        m.central.toSubmodule := by
  ext u
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨a, ha, he⟩ := hw
    have hh : a = upperEquiv d m w := Subtype.ext he
    exact hh ▸ ha
  · intro hu
    obtain ⟨w, rfl⟩ := (upperEquiv d m).surjective u
    exact ⟨w, ⟨upperEquiv d m w, hu, rfl⟩, rfl⟩

private noncomputable def sectionEquiv :
    ((transportedUpper d m).toSubmodule ⧸
      (sectionLower (d.modelRepresentation m.actor) (transportedLower d m)
        (transportedUpper d m)).toSubmodule) ≃ₗ[ZMod 2]
      BinaryPermutation.natural (Fin 8) :=
  (Submodule.Quotient.equiv _ _ (upperEquiv d m) (lower_map d m)).trans m.coordinates

private theorem sectionEquiv_equivariant (g : Equiv.Perm (Fin 8))
    (w : (transportedUpper d m).toSubmodule ⧸
      (sectionLower (d.modelRepresentation m.actor) (transportedLower d m)
        (transportedUpper d m)).toSubmodule) :
    sectionEquiv d m (sectionRepresentation (d.modelRepresentation m.actor)
      (transportedLower d m) (transportedUpper d m) g w) =
    BinaryPermutation.naturalRepresentation (Fin 8) g (sectionEquiv d m w) := by
  induction w using Submodule.Quotient.induction_on with
  | _ w =>
    change m.coordinates (m.central.toSubmodule.mkQ
      (upperEquiv d m ((transportedUpper d m).toRepresentation g w))) = _
    have he : upperEquiv d m ((transportedUpper d m).toRepresentation g w) =
        m.upper.toRepresentation (m.actor.symm g) (upperEquiv d m w) := by
      apply Subtype.ext
      exact internalEquiv_equivariant d m g w
    rw [he, ← Subrepresentation.quotientRepresentation_mk, m.equivariant,
      m.actor.apply_symm_apply]
    rfl

/-- The canonical transport preserves the actor and both literal subgroups. -/
noncomputable def markingOfMovedSection
    (hlocal : ((Source.orthogonalResidual K z ⊔ Tv T v).subgroupOf
      (plusActor K L T v)).map (d.modelMap m.actor) = A6ShadowTwoLocals.fourStabilizer) :
    Marking d where
  model := m.actor
  upper := transportedUpper d m
  lower := transportedLower d m
  upper_mem w := by
    change internalEquiv d w ∈ m.upper.toSubmodule ↔ _
    simpa only [internalEquiv_apply] using m.upper_mem (internalEquiv d w)
  lower_mem w := by
    rw [← internalEquiv_apply d w]
    change (∃ u : m.upper.toSubmodule, u ∈ m.central.toSubmodule ∧
      u.val = internalEquiv d w) ↔ _
    constructor
    · rintro ⟨u, hu, he⟩
      exact ⟨(m.upper_mem _).mp (he ▸ u.property),
        (show ((internalEquiv d w).toMul : G) ∈ centralizer (K : Set G) from
          he ▸ (m.central_mem u).mp hu)⟩
    · rintro ⟨hu,hc⟩
      let u : m.upper.toSubmodule := ⟨internalEquiv d w,(m.upper_mem _).mpr hu⟩
      exact ⟨u,(m.central_mem u).mpr hc,rfl⟩
  sectionEquiv := sectionEquiv d m
  equivariant := sectionEquiv_equivariant d m
  local_image := hlocal

/-- The original moved-section coordinates feed the proved Thompson comparison. -/
theorem thompson_eq_of_movedSection
    (hlocal : ((Source.orthogonalResidual K z ⊔ Tv T v).subgroupOf
      (plusActor K L T v)).map (d.modelMap m.actor) = A6ShadowTwoLocals.fourStabilizer) :
    elementaryAbelianMaxJ ((Source.orthogonalResidual K z ⊔ Tv T v).pCoreIn 2) =
      elementaryAbelianMaxJ ((K ⊔ Tv T v).pCoreIn 2) :=
  d.thompson_eq (markingOfMovedSection d m hlocal)

section Source
universe u
variable {H : Type u} [Group H] [Finite H]
    {𝒦 : GroupClass.{u}} {B M V : Subgroup H} {S : Sylow 2 H} {a b : H}
    (c : Recognition.SourceAction.Configuration 𝒦 B M V S a b)
    (eB : B ⧸ pCore 2 B ≃* SL(4, ZMod 2))

/-- The same source configuration and intrinsic quotient mark every earlier input. -/
@[expose] noncomputable def sourceEarlierData : EarlierData B M (S : Subgroup H) a b where
  component := c.selected
  tvSylow := c.sylow
  normalizeL := c.lv_invariant
  fixSeed := c.seed_fixed
  normalizeK := c.invariant
  lv_le := c.lv_le
  seedOmega := c.seed_omega
  characteristicTwo := c.characteristic_two
  coreModel := eB
  plusModel := c.linear_four

include eB in
/-- The actual source selection gives the local Thompson equality once its
marked residual-plus-Sylow image has been identified. -/
theorem source_thompson_eq_of_movedSection :
    letI := c.elementary
    ∀ (m : NaturalMovedSection B M (S : Subgroup H) a b c.lv_invariant c.seed_fixed),
      (plusImage B M (S : Subgroup H) a b c.lv_invariant c.seed_fixed
        (Source.orthogonalResidual B a ⊔ Tv (S : Subgroup H) b)).map m.actor.toMonoidHom =
          A6ShadowTwoLocals.fourStabilizer →
      elementaryAbelianMaxJ ((Source.orthogonalResidual B a ⊔ Tv (S : Subgroup H) b).pCoreIn 2) =
        elementaryAbelianMaxJ ((B ⊔ Tv (S : Subgroup H) b).pCoreIn 2) := by
  let := c.elementary
  intro m hlocal
  apply thompson_eq_of_movedSection (sourceEarlierData c eB) m
  change ((Source.orthogonalResidual B a ⊔ Tv (S : Subgroup H) b).subgroupOf
    (plusActor B M (S : Subgroup H) b)).map
    (m.actor.toMonoidHom.comp (plusMk B M (S : Subgroup H) a b c.lv_invariant c.seed_fixed)) = _
  rw [← Subgroup.map_map]
  exact hlocal
end Source

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Thompson
