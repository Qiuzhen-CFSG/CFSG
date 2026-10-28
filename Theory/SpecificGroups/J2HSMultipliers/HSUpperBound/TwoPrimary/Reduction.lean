module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.BlockNormalizer.Concrete.CoreGeometry.Action
public import Theory.GroupTheory.PerfectCentralCoverLocalBound
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.CentralInvolutionCore.Data

/-!
# Restriction and an explicit fusion in the HS two-primary calculation

The characteristic elementary-eight normalizer has order 10752 and odd index
4125 in the literal HS carrier. Transfer puts an arbitrary central two-kernel
inside the derived subgroup of its full inverse image. Since the normalizer
itself is perfect, that inverse image is perfect, with exactly the original
covering kernel.

A thirteen-letter carrier word conjugates the core involution `e0` to `s0`,
which lies in the normalizer outside its two-core. Thus an involution lift of
`e0` supplies one for this specific noncore involution in the restricted cover.
The permutation identity is checked on all 100 letters by the Lean kernel.

These reductions are used in `HSUpperBound.TwoPrimary`. They do not assert
that `e0` lifts in arbitrary covers or bound arbitrary covers of the normalizer;
those are separate mathematical obligations. No order-two kernel premise is
used here.

Sources: Aschbacher–Smith I.1.1–I.1.3(1), printed p.407; GLS3 §6.1 and
Table 5.3m. The existing normalizer coordinates and action supply the actual
local subgroup, not just a group-family label. The untrusted fusion discovery
script is retained in `TwoPrimary/source/`.
-/

public section

namespace Theory.SpecificGroups.J2HSMultipliers.HS.TwoPrimary
open Subgroup PerfectCentralCovering
open Sporadic.LeechRelated.HS
open EvenLocalCandidates BlockNormalizer
set_option Elab.async false

/-- The marked involution of the normalizer outside its two-core. -/
def normalizerInvolution : baseNormalizer :=
  ⟨s0, baseSylow_le_normalizer (subset_closure ⟨0, rfl⟩)⟩

set_option maxRecDepth 20000 in
theorem normalizerInvolution_sq : normalizerInvolution ^ 2 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  apply SylowCatalogueData.allFin
  decide +kernel

set_option maxRecDepth 20000 in
theorem normalizerInvolution_not_mem_core : normalizerInvolution ∉ pCore 2 baseNormalizer := by
  intro h
  have hk := (show pCore 2 baseNormalizer = baseElementary.normalizerMonoidHom.ker from
    model_core_eq_action_ker) ▸ h
  have hh := congrArg (fun φ : MulAut baseElementary =>
    (φ ⟨e1, subset_closure ⟨1, Fin.le_last 1, rfl⟩⟩).val.val 1)
    (MonoidHom.mem_ker.mp hk)
  revert hh
  decide +kernel

private def fusionA : Carrier := ⟨CentralInvolutionCore.ab0, by
  rw [CentralInvolutionCore.ab0_eq]; exact generatorAElement.property⟩
private def fusionB : Carrier := ⟨CentralInvolutionCore.ab1, by
  rw [CentralInvolutionCore.ab1_eq]; exact generatorBElement.property⟩

private def fusionConjugator : Carrier :=
  let a := fusionA
  let b := fusionB
  b * a * b⁻¹ * a * b ^ 2 * a * b * a * b * a * b * a

set_option maxRecDepth 20000 in
private theorem conjugates_e0 : fusionConjugator * e0 * fusionConjugator⁻¹ = s0 := by
  apply Subtype.ext
  apply Equiv.ext
  apply SylowCatalogueData.allFin
  decide +kernel

theorem exists_involution_lift_of_e0_lift
    {E : Type*} [Group E] (f : E →* Carrier) (hf : Function.Surjective f)
    (hlift : ∃ x : E, f x = e0 ∧ x ^ 2 = 1) :
    ∃ x : baseNormalizer.comap f,
      f.subgroupComap baseNormalizer x = normalizerInvolution ∧ x ^ 2 = 1 := by
  obtain ⟨x, hx, hx2⟩ := hlift
  obtain ⟨g, hg⟩ := hf fusionConjugator
  have hmap : f (g * x * g⁻¹) = s0 := by
    rw [map_mul, map_mul, map_inv, hg, hx, conjugates_e0]
  refine ⟨⟨g * x * g⁻¹, ?_⟩, Subtype.ext hmap, ?_⟩
  · change f (g * x * g⁻¹) ∈ baseNormalizer
    rw [hmap]
    exact normalizerInvolution.property
  · apply Subtype.ext
    change (g * x * g⁻¹) ^ 2 = 1
    calc
      _ = g * x ^ 2 * g⁻¹ := by simp only [pow_two]; group
      _ = 1 := by rw [hx2]; group

variable {E : Type*} [Group E]

/-- A section over the actual C₄³ core lifts its marked elementary involution.
The section need not be invariant under the full normalizer. -/
theorem exists_e0_lift_of_core_section (f : E →* Carrier)
    (s : pCore 2 baseNormalizer →* baseNormalizer.comap f)
    (hs : (f.subgroupComap baseNormalizer).comp s = (pCore 2 baseNormalizer).subtype) :
    ∃ x : E, f x = e0 ∧ x ^ 2 = 1 := by
  have he0 : e0 ∈ baseElementary := subset_closure ⟨0, Fin.le_last 0, rfl⟩
  obtain ⟨q, hq, hqe⟩ := CoreGeometry.elementary_le_core_image he0
  change (q : Carrier) = e0 at hqe
  let q' : pCore 2 baseNormalizer := ⟨q, hq⟩
  have hq2 : q' ^ 2 = 1 := (CoreGeometry.core_involution_iff q').mpr (by
    change (q : Carrier) ∈ baseElementary
    rwa [hqe])
  refine ⟨(s q' : E), ?_, ?_⟩
  · have h := congrArg (fun h : pCore 2 baseNormalizer →* baseNormalizer =>
      (h q' : Carrier)) hs
    exact h.trans hqe
  · exact congrArg Subtype.val (show s q' ^ 2 = 1 by rw [← map_pow, hq2, map_one])

def restrictionKernelEquiv (f : E →* Carrier) :
    (f.subgroupComap baseNormalizer).ker ≃* f.ker where
  toFun x := ⟨x.val.val, congrArg Subtype.val x.property⟩
  invFun x := ⟨⟨x.val, f.ker_le_comap baseNormalizer x.property⟩,
    Subtype.ext x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem restriction_ker_le_center (f : E →* Carrier) (hk : f.ker ≤ center E) :
    (f.subgroupComap baseNormalizer).ker ≤ center (baseNormalizer.comap f) := by
  intro x hx
  have hh : x.val ∈ f.ker := congrArg Subtype.val hx
  exact mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp (hk hh) y)

theorem restriction_isPerfect [Finite E] [Group.IsPerfect E]
    (f : E →* Carrier) (hf : Function.Surjective f)
    (hk : f.ker ≤ center E) (hp : IsPGroup 2 f.ker) :
    Group.IsPerfect (baseNormalizer.comap f) := by
  let M := baseNormalizer.comap f
  let g := f.subgroupComap baseNormalizer
  have hi : ¬ 2 ∣ M.index := by
    rw [index_comap_of_surjective _ hf, CoreGeometry.normalizer_index]
    decide
  have htransfer : f.ker ≤ ⁅M, M⁆ := central_pSubgroup_le_commutator M f.ker
    (f.ker_le_comap baseNormalizer) hk hp hi
  have hker : g.ker ≤ _root_.commutator M := by
    intro x hx
    have hxk : x.val ∈ f.ker := congrArg Subtype.val hx
    have hxd := htransfer hxk
    rw [← map_subtype_commutator] at hxd
    obtain ⟨y, hy, he⟩ := hxd
    exact (Subtype.ext he : y = x) ▸ hy
  refine ⟨?_⟩
  have h := CentralExtension.ker_sup_commutator_eq_top_of_surjective g
    (f.subgroupComap_surjective_of_surjective baseNormalizer hf)
  rwa [sup_eq_right.mpr hker] at h

end Theory.SpecificGroups.J2HSMultipliers.HS.TwoPrimary
