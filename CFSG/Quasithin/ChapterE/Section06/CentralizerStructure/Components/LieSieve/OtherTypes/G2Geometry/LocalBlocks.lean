module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.Setup
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.RelativeBlocks
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.RelativeBlocks.FirstActor
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.RelativeBlocks.SecondActor
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockRigidity.Commutation.ShortTransport
public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.GeneralizedFitting.ComponentLocalClosure.Extension
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.Geometry.EvenOvergroups.Pullback
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.ShortCore

/-!
# Characteristic two and absence of blocks for the G₂ local joins

When Q normalizes L, each invariant parabolic pullback is normal in its join
with Q, with two-group quotient. Its map to the actual derived-model parabolic
is surjective with two-group kernel, so it maps its two-core onto the model
two-core. A short relatively subnormal subgroup acts with square-one
commutators on this core. The two existing model actor calculations force its
image to vanish; two-perfection then excludes the remaining two-group kernel.
This proves absence of every chi-zero block, with relative subnormality intact.

Characteristic two lifts through the same kernel and the upper two-group
quotient. Both arguments retain the binary derived group and arbitrary central
two-covers. Component normalization remains a separate ambient obligation.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8,
printed pp.247–248 (PDF pp.258–259); the reusable core-action argument is
formalized in the Chapter 2 G₂ relative-block leaves for 2.3.9(7), p.526.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.G2Geometry

open Chapter2.ComponentRefinement.LieType.G2.RelativeBlocks
variable {G P : Type*} [Group G] [Group P] [Finite G] [Finite P]

/-- A single normal coordinate suffices when the two-group preserves the local factor. -/
theorem noChiZeroBlocks_of_pKernel (A Q : Subgroup G)
    (hN : Q ≤ normalizer (A : Set G)) (hQ : IsPGroup 2 Q)
    (f : A →* P) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (hrigid : ∀ X : Subgroup P, X.IsSubnormal → IsPPerfect 2 X →
      (∀ q ∈ pCore 2 P, ∀ x ∈ X, (⁅q,x⁆ : P)^2 = 1) → X = ⊥) :
    NoChiZeroBlocks (A ⊔ Q) := by
  let D := A ⊔ Q
  let N := A.subgroupOf D
  let e : N ≃* A := subgroupOfEquivOfLe le_sup_left
  let g : N →* P := f.comp e.toMonoidHom
  have hg : Function.Surjective g := hf.comp e.surjective
  have hgk : IsPGroup 2 g.ker := by
    change IsPGroup 2 (f.ker.comap e.toMonoidHom)
    exact hk.comap_of_injective e.toMonoidHom e.injective
  have hn : N.Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (sup_le A.le_normalizer hN)
  let := hn
  have hgen : N ⊔ Q.subgroupOf D = ⊤ := by
    apply Subgroup.map_injective D.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left,
      map_subgroupOf_eq_of_le le_sup_right, ← MonoidHom.range_eq_map, range_subtype]
  let d : CoreSection D P := {
    base := N
    normal := hn
    quotient_two := isPGroup_quotient_of_sup_eq_top N (Q.subgroupOf D) hQ.comap_subtype hgen
    count := 1
    projection := fun _ => g
    surjective := fun _ => hg
    core_image := fun _ => by
      rw [← g.comap_pCore_of_ker_isPGroup hg hgk, map_comap_eq_self]
      rw [MonoidHom.range_eq_top.mpr hg]
      exact le_top
    kernel_two := by
      change IsPGroup 2 (⨅ _ : Fin 1, g.ker : Subgroup N)
      have he : (⨅ _ : Fin 1, g.ker : Subgroup N) = g.ker :=
        le_antisymm (iInf_le _ 0) (le_iInf fun _ => le_rfl)
      rw [he]
      exact hgk }
  intro B hBD hs hb
  exact not_short_of_coreSection d hrigid (B.subgroupOf D) hs
    (hb.chi.short.of_mulEquiv (subgroupOfEquivOfLe hBD).symm)

open Chapter2.ComponentRefinement.LieType.G2
variable {L Q : Subgroup G}

/-- Restriction to the actual derived-model parabolic, with all central kernels retained. -/
def parabolicProjection (d : ParabolicCoordinates L Q)
    (P : Subgroup (Atlas.G2.Model d.field)) :
    (P.comap d.modelMap) →* P.subgroupOf (commutator (Atlas.G2.Model d.field)) where
  toFun x := ⟨⟨d.modelMap x, d.model_range ▸ (show d.modelMap x ∈ d.modelMap.range from ⟨x, rfl⟩)⟩, x.property⟩
  map_one' := Subtype.ext (Subtype.ext (map_one _))
  map_mul' x y := Subtype.ext (Subtype.ext (map_mul d.modelMap (x : L) (y : L)))

omit [Finite G] in
theorem parabolicProjection_surjective (d : ParabolicCoordinates L Q)
    (P : Subgroup (Atlas.G2.Model d.field)) :
    Function.Surjective (parabolicProjection d P) := by
  intro y
  obtain ⟨x, hx⟩ := (show y.val.val ∈ d.modelMap.range from d.model_range.symm ▸ y.val.property)
  exact ⟨⟨x, by change d.modelMap x ∈ P; rw [hx]; exact y.property⟩,
    Subtype.ext (Subtype.ext hx)⟩

omit [Finite G] in
theorem parabolicProjection_kernel_two (d : ParabolicCoordinates L Q)
    (P : Subgroup (Atlas.G2.Model d.field)) :
    IsPGroup 2 (parabolicProjection d P).ker := by
  have he : (parabolicProjection d P).ker =
      d.modelMap.ker.subgroupOf (P.comap d.modelMap) := by
    ext x
    change (parabolicProjection d P x = 1) ↔ d.modelMap x = 1
    exact ⟨fun h => congrArg (fun y => y.val.val) h,
      fun h => Subtype.ext (Subtype.ext h)⟩
  rw [he]
  exact d.model_kernel_isPGroup.comap_subtype

/-- The model actor calculation excludes relative blocks in the genuine lifted join. -/
theorem noChiZeroBlocks_pullback (d : ParabolicCoordinates L Q)
    (P : Subgroup (Atlas.G2.Model d.field))
    (hN : Q ≤ normalizer ((P.comap d.modelMap).map L.subtype : Set G))
    (hQ : IsPGroup 2 Q)
    (hrigid : ∀ X : Subgroup (P.subgroupOf (commutator (Atlas.G2.Model d.field))),
      X.IsSubnormal → IsPPerfect 2 X →
      (∀ q ∈ pCore 2 (P.subgroupOf (commutator (Atlas.G2.Model d.field))),
        ∀ x ∈ X, (⁅q,x⁆ : P.subgroupOf (commutator (Atlas.G2.Model d.field)))^2 = 1) → X = ⊥) :
    NoChiZeroBlocks ((P.comap d.modelMap).map L.subtype ⊔ Q) := by
  let e := (P.comap d.modelMap).equivMapOfInjective L.subtype L.subtype_injective
  let f := (parabolicProjection d P).comp e.symm.toMonoidHom
  apply noChiZeroBlocks_of_pKernel _ Q hN hQ f
    ((parabolicProjection_surjective d P).comp e.symm.surjective) _ hrigid
  change IsPGroup 2 ((parabolicProjection d P).ker.comap e.symm.toMonoidHom)
  exact (parabolicProjection_kernel_two d P).comap_of_injective _ e.symm.injective

/-- Both standard parabolic pullbacks are block-free when Q preserves the component. -/
theorem noChiZeroBlocks_pair (d : ParabolicCoordinates L Q)
    (hN : Q ≤ normalizer (L : Set G)) (hQ : IsPGroup 2 Q) :
    NoChiZeroBlocks (d.first ⊔ Q) ∧ NoChiZeroBlocks (d.second ⊔ Q) := by
  constructor
  · exact noChiZeroBlocks_pullback d _
      (fun x hx => d.first_invariant ⟨hx, hN hx⟩) hQ
      (first_actor_eq_bot Atlas.G2.LieParabolicSetup.local₁_pCoreIn)
  · exact noChiZeroBlocks_pullback d _
      (fun x hx => d.second_invariant ⟨hx, hN hx⟩) hQ second_actor_eq_bot

omit [Finite G] in
/-- Adjoining a normalizing two-group preserves characteristic two. -/
theorem characteristicTwo_adjoin (A Q : Subgroup G)
    (hN : Q ≤ normalizer (A : Set G)) (hQ : IsPGroup 2 Q)
    (hc : HasCharacteristicTwo A) : HasCharacteristicTwo ↥(A ⊔ Q) := by
  let D := A ⊔ Q
  let N := A.subgroupOf D
  let : N.Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (sup_le A.le_normalizer hN)
  have hgen : N ⊔ Q.subgroupOf D = ⊤ := by
    apply Subgroup.map_injective D.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left,
      map_subgroupOf_eq_of_le le_sup_right, ← MonoidHom.range_eq_map, range_subtype]
  exact centralizer_pCore_le_of_normal_pGroup_quotient N
    ((Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe le_sup_left)).mpr hc)
    (isPGroup_quotient_of_sup_eq_top N (Q.subgroupOf D) hQ.comap_subtype hgen)

/-- The lifted pair has characteristic two, including the binary derived endpoint. -/
theorem characteristicTwo_pair (d : ParabolicCoordinates L Q)
    (hN : Q ≤ normalizer (L : Set G)) (hQ : IsPGroup 2 Q) :
    HasCharacteristicTwo ↥(d.first ⊔ Q) ∧ HasCharacteristicTwo ↥(d.second ⊔ Q) := by
  constructor
  · apply characteristicTwo_adjoin _ Q (fun x hx => d.first_invariant ⟨hx, hN hx⟩) hQ
    exact (Theory.Quasithin.centralizer_pCore_le_iff 2
      ((Atlas.G2.LieParabolicSetup.parabolic₁.comap d.modelMap).equivMapOfInjective
        L.subtype L.subtype_injective)).mp
      (d.first_pullback_centralizer_pCore (fun _ => Atlas.G2.EvenLocal.parabolic₁_centralizer_pCore))
  · apply characteristicTwo_adjoin _ Q (fun x hx => d.second_invariant ⟨hx, hN hx⟩) hQ
    exact (Theory.Quasithin.centralizer_pCore_le_iff 2
      ((Atlas.G2.LieParabolicSetup.parabolic₂.comap d.modelMap).equivMapOfInjective
        L.subtype L.subtype_injective)).mp d.second_pullback_centralizer_pCore

end CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.G2Geometry
