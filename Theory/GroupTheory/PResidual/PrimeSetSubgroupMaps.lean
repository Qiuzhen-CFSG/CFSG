module

public import Theory.GroupTheory.PResidual.PrimeSet

/-!
# Prime-set residuals of subgroup images

If a homomorphism sends M into N, it sends the intrinsic π-residual of M
into that of N. Restrict the homomorphism to these actual subgroups and
apply residual functoriality, retaining both subtype embeddings.

This is the residual transport used to deduce GLS II 5.17 and 5.19 from
two-star-core balance and the odd-residual identification in 5.16.
-/

public section
namespace Subgroup
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

/-- Residual functoriality for a map carrying one specified subgroup into another.
Neither subgroup needs to be normal in its ambient group. -/
theorem map_embedded_piResidual_le (π : Set Nat.Primes)
    (M : Subgroup G) (N : Subgroup H) (f : G →* H) (h : M.map f ≤ N) :
    ((piResidual π M).map M.subtype).map f ≤ (piResidual π N).map N.subtype := by
  let g : M →* N := (f.comp M.subtype).codRestrict N
    (fun x => h (mem_map_of_mem f x.property))
  calc
    _ = ((piResidual π M).map g).map N.subtype := by
      rw [map_map, map_map]
      rfl
    _ ≤ _ := map_mono (map_piResidual_le π g)

end Subgroup
