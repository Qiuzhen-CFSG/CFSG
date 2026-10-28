module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.RelativeBlocks.OrbitSections.ModelMaps
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.Setup
public import Theory.GroupTheory.GeneralizedFitting.ComponentLocalClosure.CentralCover
public import Theory.GroupTheory.PCoreSurjective.Coordinates

/-!
# Core-surjective G₂ parabolic orbit sections

For either marked parabolic K, take the base to be the subgroup generated
by the actual Sylow-conjugates of K, restricted to K ⊔ σ. It is normal
there, with two-group quotient. Stabilizer invariance identifies repeated
factors; distinct components of H commute. The central-cover orbit theorem
then descends the literal pullback model maps to a finite power of the
parabolic in the derived G₂ model, with two-group kernel.

Evaluation gives the required coordinates. Core lifting for the map to the
whole power, followed by the factor-core calculation, proves each core-image
equality. This does not require the individual coordinate kernels to be
two-groups. The construction retains arbitrary central two-covers at field
order four and the derived-model intersections at field order two.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, proof of 2.3.9(7), printed p.526. The inner action
input is retained in the paired source adapter; the orbit sections themselves
need only the component, Sylow and supplied parabolic coordinates. The
subsequent actor calculations and block obstruction are separate consumers.
-/

public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2.RelativeBlocks

private theorem coreSection_of_orbit_surjection
    {G P : Type*} [Group G] [Group P] [Finite G] [Finite P]
    (K A : Subgroup G) (hA : IsPGroup 2 A) (n : ℕ)
    (F : componentOrbit K A →* (Fin n → P))
    (hF : Function.Surjective F) (hk : IsPGroup 2 F.ker) :
    Nonempty (CoreSection (K ⊔ A : Subgroup G) P) := by
  let N := (componentOrbit K A).subgroupOf (K ⊔ A)
  let e : N ≃* componentOrbit K A := subgroupOfEquivOfLe (componentOrbit_le_sup K A)
  let f : N →* (Fin n → P) := F.comp e.toMonoidHom
  have hf : Function.Surjective f := hF.comp e.surjective
  have hfk : IsPGroup 2 f.ker := hk.comap_of_injective e.toMonoidHom e.injective
  let π : Fin n → N →* P := fun i => (Pi.evalMonoidHom (fun _ : Fin n => P) i).comp f
  have hπ : ∀ i, Function.Surjective (π i) := by
    intro i x
    obtain ⟨y, hy⟩ := hf (fun _ => x)
    exact ⟨y, congrFun hy i⟩
  have hker : (⨅ i, (π i).ker) = f.ker := by
    ext x
    rw [mem_iInf]
    change (∀ i, π i x = 1) ↔ f x = 1
    exact ⟨fun h => funext h, fun h i => congrFun h i⟩
  exact ⟨{
    base := N
    normal := componentOrbit_normal_subgroupOf_sup K A
    quotient_two := local_orbit_quotient_isPGroup K A hA
    count := n
    projection := π
    surjective := hπ
    core_image := fun i => f.pCore_map_coordinate hf hfk i
    kernel_two := hker.symm ▸ hfk }⟩

private theorem coreSection_of_relative_component
    {G P : Type*} [Group G] [Group P] [Finite G] [Finite P]
    {H L K A : Subgroup G}
    (hLH : L ≤ H) (hAH : A ≤ H)
    (hL : IsComponent H (L.subgroupOf H)) (hKL : K ≤ L)
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G))
    (hA : IsPGroup 2 A)
    (f : K →* P) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (hz : ∀ x : K, (⟨x.val, hKL x.property⟩ : L) ∈ center L → f x = 1) :
    Nonempty (CoreSection (K ⊔ A : Subgroup G) P) := by
  obtain ⟨n, F, hF, hkF⟩ := hL.local_orbit_surjection_power_in
    hLH hAH hKL hinv f hf hk hz
  exact coreSection_of_orbit_surjection K A hA n F hF hkF

variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The first actual parabolic overgroup has the required orbit core section. -/
theorem first_coreSection (h : LocalSetup H L M S z)
    (d : ParabolicCoordinates L ((S : Subgroup H).map H.subtype)) :
    Nonempty (CoreSection d.firstOvergroup (firstModel d.field)) := by
  let := h.finite
  exact coreSection_of_relative_component h.component_le (map_subtype_le _) h.component
    (map_subtype_le _) d.first_invariant (S.isPGroup'.map H.subtype)
    (d.pullbackMap Atlas.G2.LieParabolicSetup.parabolic₁)
    (d.pullbackMap_surjective _) (d.pullbackMap_kernel_two _) (d.pullbackMap_kills_center _)

/-- The second actual parabolic overgroup has the required orbit core section. -/
theorem second_coreSection (h : LocalSetup H L M S z)
    (d : ParabolicCoordinates L ((S : Subgroup H).map H.subtype)) :
    Nonempty (CoreSection d.secondOvergroup (secondModel d.field)) := by
  let := h.finite
  exact coreSection_of_relative_component h.component_le (map_subtype_le _) h.component
    (map_subtype_le _) d.second_invariant (S.isPGroup'.map H.subtype)
    (d.pullbackMap Atlas.G2.LieParabolicSetup.parabolic₂)
    (d.pullbackMap_surjective _) (d.pullbackMap_kernel_two _) (d.pullbackMap_kills_center _)

/-- Both sections for the literal inner-action branch, with every structural
field constructed and no block or actor-rigidity hypothesis. -/
theorem coreSections (h : LocalSetup H L M S z)
    (_hinner : ∃ t : L, IsConjugationProjection L z t)
    (d : ParabolicCoordinates L ((S : Subgroup H).map H.subtype)) :
    Nonempty (CoreSection d.firstOvergroup (firstModel d.field)) ∧
      Nonempty (CoreSection d.secondOvergroup (secondModel d.field)) :=
  ⟨first_coreSection h d, second_coreSection h d⟩

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2.RelativeBlocks

end
