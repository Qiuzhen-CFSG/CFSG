module

public import Theory.Mathieu.M12.SylowOvergroups.Representatives
public import Theory.Mathieu.M12.SmallParabolicPair.SylowGeometry

/-!
# A computable invariant of the marked Sylow cosets in M₁₂

The Sylow subgroup centralizes the distinguished involution and normalizes the
marked four-group. Therefore the image of that involution, together with the
sum of the permutation codes of the conjugate four-group, is constant on right
multiplication by the Sylow subgroup. Distinct values certify distinct cosets.
No global injectivity of this numerical invariant is required.
-/

@[expose] public section
namespace Sporadic.Mathieu.M12SmallPair.SylowOvergroups
open SylowEnumeration


def permutationCode (g : Equiv.Perm (Fin 12)) : ℕ :=
  ∑ i : Fin 12, (g i).val * 12 ^ i.val

noncomputable def conjugatePlane (g : M12) : Finset (Equiv.Perm (Fin 12)) :=
  planePerms.image (fun x => g.val * x * g.val⁻¹)

noncomputable def cosetKey (g : M12) : ℕ :=
  permutationCode (g.val * zPerm * g.val⁻¹) * (4 * 12 ^ 12) +
    ∑ x ∈ conjugatePlane g, permutationCode x

theorem cosetKey_mul (g : M12) (s : sylowCandidate) :
    cosetKey (g * s) = cosetKey g := by
  have hn := (mem_secondParabolic_iff s.val).mp s.property.2
  have hz := (mem_firstParabolic_iff s.val).mp s.property.1
  change s.val.val * zPerm = zPerm * s.val.val at hz
  have hz' : s.val.val * zPerm * s.val.val⁻¹ = zPerm := by
    rw [hz, mul_assoc, mul_inv_cancel, mul_one]
  have hp : conjugatePlane (g * s) = conjugatePlane g := by
    unfold conjugatePlane
    calc
      _ = (planePerms.image (fun x => s.val.val * x * s.val.val⁻¹)).image
          (fun x => g.val * x * g.val⁻¹) := by
        rw [Finset.image_image]
        congr 1
      _ = _ := by rw [hn]
  have hzg : (g * s).val * zPerm * (g * s).val⁻¹ = g.val * zPerm * g.val⁻¹ := by
    change (g.val * s.val.val) * zPerm * (g.val * s.val.val)⁻¹ = _
    calc
      _ = g.val * (s.val.val * zPerm * s.val.val⁻¹) * g.val⁻¹ := by group
      _ = _ := by rw [hz']
  unfold cosetKey
  rw [hp, hzg]

theorem key_eq_of_coset_eq {g h : M12}
    (he : (QuotientGroup.mk g : M12 ⧸ sylowCandidate) = QuotientGroup.mk h) :
    cosetKey g = cosetKey h := by
  have hm : g⁻¹ * h ∈ sylowCandidate := QuotientGroup.leftRel_apply.mp (Quotient.exact he)
  have := cosetKey_mul g ⟨g⁻¹ * h, hm⟩
  simpa using this.symm

end Sporadic.Mathieu.M12SmallPair.SylowOvergroups
