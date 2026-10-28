module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SuzukiPair.Cubic
public import Theory.SpecificGroups.Suzuki.BorelResidual
public import Theory.SpecificGroups.Suzuki.CubicBorel
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# Arbitrary cubic actions on the paired Suzuki central quotient

The full lifted Borel surjects onto the concrete product Borel, which is its
own two-residual. Surjective residual transport therefore lifts every Borel
element into the actual O²(B), without removing the full central kernel.

The commutator bound forces O²(B) to normalize Lᵥ and O₂(Lᵥ). Intersecting
the latter with K₀ and taking its literal marked image gives a two-subgroup
normalized by the whole product Borel. Sylow maximality puts this image in
the product root group. The intrinsic cubic detector now kills the actor;
no compatible field marking, factor preservation or Borel invariance is
assumed.

Source: Aschbacher--Smith, proof of 13.6.6, printed p.927 (PDF p.944).
The source assembly supplies the nontrivial cubic actor and the displayed
commutator bound; this module proves precisely that conditional endpoint.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SuzukiPair
open Subgroup BenderSuzuki.MatrixGroups
open scoped commutatorElement
variable {G : Type*} [Group G] [Finite G]
variable {T K L : Subgroup G} {v : G}

namespace Marking

/-- The literal quotient map, restricted to the lifted and concrete Borels. -/
def productBorelMap (d : Marking T K v) : d.borel →*
    (SuzukiBorelSubgroup d.parameter).prod (SuzukiBorelSubgroup d.parameter) :=
  (d.quotientMap.comp (inclusion d.borel_le_orbit)).codRestrict _ (by
    intro b
    obtain ⟨x, hx, he⟩ := b.property
    have he' : x = inclusion d.borel_le_orbit b := Subtype.ext he
    change d.quotientMap (inclusion d.borel_le_orbit b) ∈ _
    rw [← he']
    exact hx)

omit [Finite G] in
theorem productBorelMap_surjective (d : Marking T K v) :
    Function.Surjective d.productBorelMap := by
  intro b
  have hb : b.val ∈ d.borelInOrbit.map d.quotientMap := d.borel_image.symm ▸ b.property
  obtain ⟨x, hx, he⟩ := hb
  exact ⟨⟨x, ⟨x, hx, rfl⟩⟩, Subtype.ext he⟩

/-- Every element of the product Borel has a lift in the actual residual of
its full central preimage. No assumption on the central kernel is needed. -/
theorem exists_residual_borel_lift (d : Marking T K v)
    (z : SuzukiMatrixGroup d.parameter × SuzukiMatrixGroup d.parameter)
    (hz : z ∈ (SuzukiBorelSubgroup d.parameter).prod (SuzukiBorelSubgroup d.parameter)) :
    ∃ b : d.borel, b ∈ pResidual 2 d.borel ∧
      d.quotientMap (inclusion d.borel_le_orbit b) = z := by
  have hmap := map_pResidual_of_surjective 2 d.productBorelMap d.productBorelMap_surjective
  rw [suzukiBorel_prod_pResidual_eq_top d.parameter d.positive] at hmap
  have hz' : (⟨z, hz⟩ : (SuzukiBorelSubgroup d.parameter).prod _)
      ∈ (pResidual 2 d.borel).map d.productBorelMap := hmap.symm ▸ mem_top _
  obtain ⟨b, hb, he⟩ := hz'
  exact ⟨b, hb, congrArg Subtype.val he⟩

/-- Residual transport through the exact central quotient, in both factors. -/
theorem residual_borel_image (d : Marking T K v) :
    ((pResidual 2 d.borel).map (inclusion d.borel_le_orbit)).map d.quotientMap =
      (SuzukiBorelSubgroup d.parameter).prod (SuzukiBorelSubgroup d.parameter) := by
  apply le_antisymm
  · rintro z ⟨x, ⟨b, hb, rfl⟩, rfl⟩
    exact (d.productBorelMap b).property
  · intro z hz
    obtain ⟨b, hb, he⟩ := d.exists_residual_borel_lift z hz
    exact ⟨inclusion d.borel_le_orbit b, mem_map_of_mem _ hb, he⟩

end Marking

/-- The image of the actual two-core intersection is contained in the
product root group. Normalization follows from the source commutator bound. -/
theorem twoCore_intersection_image_le_root (d : Marking T K v)
    (hcomm : ⁅Lv L v, (pResidual 2 d.borel).map d.borel.subtype⁆ ≤
      (pCore 2 (Lv L v)).map (Lv L v).subtype) :
    (((pCore 2 (Lv L v)).map (Lv L v).subtype).subgroupOf (orbit T K v)).map
        d.quotientMap ≤
      (SuzukiRootSubgroup d.parameter).prod (SuzukiRootSubgroup d.parameter) := by
  let Q := (pCore 2 (Lv L v)).map (Lv L v).subtype
  let R := (pResidual 2 d.borel).map d.borel.subtype
  let R₀ := (pResidual 2 d.borel).map (inclusion d.borel_le_orbit)
  have hRL : R ≤ normalizer (Lv L v : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr (hcomm.trans (map_subtype_le _))
  have hRQ : R ≤ normalizer (Q : Set G) :=
    hRL.trans (normalizer_le_normalizer_characteristic_image (Lv L v) (pCore 2 (Lv L v)))
  have hR₀Q : R₀ ≤ normalizer (Q.subgroupOf (orbit T K v) : Set (orbit T K v)) := by
    apply le_trans _ (Q.le_normalizer_comap (orbit T K v).subtype)
    rintro x ⟨b, hb, rfl⟩
    exact hRQ (mem_map_of_mem _ hb)
  apply suzuki_pair_twoSubgroup_le_root_of_borel_normalizes d.parameter d.positive
  · exact ((pCore_isPGroup.map (Lv L v).subtype).comap_subtype).map d.quotientMap
  · rw [← d.residual_borel_image]
    exact (map_mono hR₀Q).trans ((Q.subgroupOf (orbit T K v)).le_normalizer_map d.quotientMap)

/-- Any compatible actual cubic automorphism is trivial under the source
commutator bound, in every central-quotient marking. -/
theorem cubic_trivial_of_commutator_bound (d : Marking T K v)
    (c : G) (hc : c ∈ Lv L v) (hcN : c ∈ normalizer (orbit T K v : Set G))
    (α : MulAut (SuzukiMatrixGroup d.parameter × SuzukiMatrixGroup d.parameter))
    (hα : α ^ 3 = 1)
    (haction : ∀ x : orbit T K v,
      d.quotientMap ((orbit T K v).normalizerMonoidHom ⟨c, hcN⟩ x) = α (d.quotientMap x))
    (hcomm : ⁅Lv L v, (pResidual 2 d.borel).map d.borel.subtype⁆ ≤
      (pCore 2 (Lv L v)).map (Lv L v).subtype) : α = 1 := by
  apply suzuki_pair_cubic_eq_one_of_borel_displacement d.parameter d.positive α hα
  intro z hz
  obtain ⟨b, hb, he⟩ := d.exists_residual_borel_lift z hz
  let x : orbit T K v := inclusion d.borel_le_orbit b
  let a := (orbit T K v).normalizerMonoidHom ⟨c, hcN⟩
  have hw : ⁅c, (b : G)⁆ ∈ (pCore 2 (Lv L v)).map (Lv L v).subtype :=
    hcomm (commutator_mem_commutator hc (mem_map_of_mem _ hb))
  have hx : a x * x⁻¹ ∈
      ((pCore 2 (Lv L v)).map (Lv L v).subtype).subgroupOf (orbit T K v) := hw
  have hi := twoCore_intersection_image_le_root d hcomm (mem_map_of_mem d.quotientMap hx)
  have hxq : d.quotientMap x = z := he
  have hax : d.quotientMap (a x) = α z := (haction x).trans (congrArg α hxq)
  simpa only [map_mul, map_inv, hax, hxq] using hi

/-- The terminal paired Suzuki contradiction for an arbitrary actual cubic
actor. The central cover and both literal quotient coordinates are retained. -/
theorem cubic_contradiction (d : Marking T K v)
    (c : G) (hc : c ∈ Lv L v) (hcN : c ∈ normalizer (orbit T K v : Set G))
    (α : MulAut (SuzukiMatrixGroup d.parameter × SuzukiMatrixGroup d.parameter))
    (hα : α ^ 3 = 1) (hαne : α ≠ 1)
    (haction : ∀ x : orbit T K v,
      d.quotientMap ((orbit T K v).normalizerMonoidHom ⟨c, hcN⟩ x) = α (d.quotientMap x))
    (hcomm : ⁅Lv L v, (pResidual 2 d.borel).map d.borel.subtype⁆ ≤
      (pCore 2 (Lv L v)).map (Lv L v).subtype) : False :=
  hαne (cubic_trivial_of_commutator_bound d c hc hcN α hα haction hcomm)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SuzukiPair
