module
public import Theory.Representation.G2BinaryPointResidualMovement

/-!
# Generation of the binary point seed by its residual

The native cubic moves the first two nonfixed basis vectors. Its conjugate
by the C--D root pair adds the fixed point to a displacement. These three
displacements span the literal three-space. This supplies seed generation
in Aschbacher--Smith 13.3.14(g), printed pp.892--893, using the derived second
parabolic. The split-octonion action and its ATLAS attribution are inherited.
-/

public section
open Subgroup
namespace Atlas.G2.Natural.BinaryPointFlag
open Atlas.G2.BinaryParabolicPair Atlas.G2.BinaryCore
/-- Displacements of the actual point two-residual span the whole seed. -/
theorem seed_le_of_residual_displacements (S : Submodule F W)
    (hS : ∀ a : derivedSecond, a ∈ pResidual 2 derivedSecond → ∀ v ∈ seed,
      Atlas.G2.Restricted.NaturalCoordinates.action F a.val.val v - v ∈ S) :
    seed ≤ S := by
  let a : derivedSecond := ⟨⟨movingActor,movingActor_mem_derived⟩,movingActor_mem_derivedSecond⟩
  let c : derivedSecond := ⟨⟨Atlas.G2.rootC 1 * Atlas.G2.rootD 1,point_actor_membership.2.2.2⟩,
    point_actor_membership.2.2.1⟩
  have ha : a ∈ pResidual 2 derivedSecond := movingActor_derived_residual
  have hb : c*a*c⁻¹ ∈ pResidual 2 derivedSecond :=
    (inferInstance : (pResidual 2 derivedSecond).Normal).conj_mem a ha c
  have hi (i : Fin 6) (h : i < 3) : (Pi.single i 1 : W) ∈ seed := by
    simp only [mem_seed]
    have h3 : (3 : Fin 6) ≠ i := by omega
    have h4 : (4 : Fin 6) ≠ i := by omega
    have h5 : (5 : Fin 6) ≠ i := by omega
    simp [h3,h4,h5]
  have h2 : (Pi.single 2 1 : W) ∈ S := by
    have hh := hS a ha _ (hi 1 (by decide))
    convert hh using 1
    ext i
    fin_cases i <;> simp [a,movingActor,map_mul,Module.End.mul_apply]
  have h12 : (Pi.single 1 1 + Pi.single 2 1 : W) ∈ S := by
    have hh := hS a ha _ (hi 2 (by decide))
    convert hh using 1
    ext i
    fin_cases i <;> simp [a,movingActor,map_mul,Module.End.mul_apply]
  have h1 : (Pi.single 1 1 : W) ∈ S := by
    simpa only [add_sub_cancel_right] using S.sub_mem h12 h2
  have hc : (Atlas.G2.rootC (1 : F) * Atlas.G2.rootD 1)⁻¹ =
      Atlas.G2.rootD 1 * Atlas.G2.rootC 1 := by
    rw [mul_inv_rev]
    have hd : (Atlas.G2.rootD (1:F))⁻¹ = Atlas.G2.rootD 1 := by
      apply inv_eq_of_mul_eq_one_right
      rw [Atlas.G2.rootD_add,show (1:F)+1=0 by decide,Atlas.G2.rootD_zero]
    have hc : (Atlas.G2.rootC (1:F))⁻¹ = Atlas.G2.rootC 1 := by
      apply inv_eq_of_mul_eq_one_right
      rw [Atlas.G2.rootC_add,show (1:F)+1=0 by decide,Atlas.G2.rootC_zero]
    rw [hd,hc]
  have h02 : (Pi.single 0 1 + Pi.single 2 1 : W) ∈ S := by
    have hh := hS _ hb _ (hi 1 (by decide))
    change Atlas.G2.Restricted.NaturalCoordinates.action F
      ((Atlas.G2.rootC 1 * Atlas.G2.rootD 1) * movingActor *
        (Atlas.G2.rootC 1 * Atlas.G2.rootD 1)⁻¹) (Pi.single 1 1) - Pi.single 1 1 ∈ S at hh
    convert hh using 1
    ext i
    fin_cases i <;> simp [hc,movingActor,map_mul,Module.End.mul_apply]
  have h0 : (Pi.single 0 1 : W) ∈ S := by
    simpa only [add_sub_cancel_right] using S.sub_mem h02 h2
  intro v hv
  obtain ⟨h3,h4,h5⟩ := mem_seed v |>.mp hv
  have he : v = v 0 • Pi.single 0 1 + v 1 • Pi.single 1 1 + v 2 • Pi.single 2 1 := by
    ext i
    fin_cases i <;> simp [h3,h4,h5]
  rw [he]
  exact S.add_mem (S.add_mem (S.smul_mem _ h0) (S.smul_mem _ h1)) (S.smul_mem _ h2)

end Atlas.G2.Natural.BinaryPointFlag
