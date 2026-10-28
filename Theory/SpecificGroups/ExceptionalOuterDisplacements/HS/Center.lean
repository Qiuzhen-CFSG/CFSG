module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.SylowCatalogue.Enumeration
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.CarrierOrder
public import Theory.GroupTheory.DoubleCoverCentralizer.DisplacementTransport

/-!
# Two-central HS elements have a fixed point

The existing enumeration of the actual 512-element two-subgroup gives its
order, and the checked HS order makes it Sylow. Testing commutation with
its three generators on points 1 and 4 leaves only rows fixing point 0.
Consequently every central element of this Sylow subgroup fixes point 0.
Sylow conjugacy transports this to a fixed point for every two-central
carrier element. A fixed-point-free displacement therefore has the
non-two-central mark, without any full-centralizer certificate.

Source: Aschbacher–Smith I.2.2, observation (iii), printed p.411 / PDF p.422.
The actual ATLAS HSG1-p100B0 Sylow enumeration and its attribution are reused
from `HS/EvenLocalCandidates/SylowCatalogue/Enumeration.lean`.
-/

public section
namespace Theory.SpecificGroups.ExceptionalOuterDisplacements.HS
open Subgroup Theory.GroupTheory.DoubleCoverCentralizer
open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.EvenLocalCandidates
open Sporadic.LeechRelated.HS.EvenLocalCandidates.SylowCatalogueData
open scoped Pointwise
set_option maxRecDepth 10000

private def sylow : Sylow 2 Carrier :=
  (IsPGroup.of_card subgroup_card).toSylow (by
    have h := subgroup.card_mul_index
    rw [subgroup_card, NormalizerIndex.card_carrier] at h
    have hi : subgroup.index = 86625 := by norm_num at h; omega
    rw [hi]
    decide)

private theorem center_fixed_check : ∀ i : Fin 512,
    (∀ s : Fin 3, ∀ p : Fin 2,
      point i (inclusion (sylowGenerator s) (![1, 4] p)) =
        inclusion (sylowGenerator s) (point i (![1, 4] p))) → point i 0 = 0 := by
  apply allFin
  decide +kernel

private theorem central_fixed (x : Carrier) (hx : x ∈ subgroup)
    (hc : ∀ y ∈ subgroup, y * x = x * y) : inclusion x 0 = 0 := by
  obtain ⟨i, rfl⟩ := element_surjective hx
  change (element i : Equiv.Perm (Fin 100)) 0 = 0
  rw [element_point]
  apply center_fixed_check i
  intro s p
  have he := congrArg (fun y : Carrier => inclusion y (![1, 4] p))
    (hc (sylowGenerator s) (subset_closure ⟨s, rfl⟩))
  change (sylowGenerator s : Equiv.Perm (Fin 100)) ((element i : Equiv.Perm (Fin 100)) (![1, 4] p)) =
    (element i : Equiv.Perm (Fin 100)) ((sylowGenerator s : Equiv.Perm (Fin 100)) (![1, 4] p)) at he
  change point i ((sylowGenerator s : Equiv.Perm (Fin 100)) (![1, 4] p)) =
    (sylowGenerator s : Equiv.Perm (Fin 100)) (point i (![1, 4] p))
  simpa only [element_point] using he.symm

/-- Every element central in a Sylow two-subgroup fixes a point of the defining action. -/
theorem twoCentral_has_fixed_point (x : Carrier) (hx : TwoCentral x) :
    ∃ p : Fin 100, inclusion x p = p := by
  obtain ⟨P, hxP, hc⟩ := hx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Carrier P sylow
  let e := MulAut.conj g
  have hP : (sylow : Subgroup Carrier) = (P : Subgroup Carrier).map e.toMonoidHom := by
    rw [← hg]
    rfl
  have hex : e x ∈ subgroup := by
    change e x ∈ (sylow : Subgroup Carrier)
    rw [hP]
    exact ⟨x, hxP, rfl⟩
  have hec : ∀ y ∈ subgroup, y * e x = e x * y := by
    intro y hy
    change y ∈ (sylow : Subgroup Carrier) at hy
    rw [hP] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    change e z * e x = e x * e z
    rw [← e.map_mul, ← e.map_mul]
    exact congrArg e (congrArg Subtype.val (mem_center_iff.mp hc ⟨z, hz⟩))
  have hf := central_fixed (e x) hex hec
  refine ⟨(inclusion g)⁻¹ 0, ?_⟩
  have hf' : inclusion g (inclusion x ((inclusion g)⁻¹ 0)) = 0 := hf
  exact (inclusion g).injective (hf'.trans ((inclusion g).apply_symm_apply 0).symm)

end Theory.SpecificGroups.ExceptionalOuterDisplacements.HS
