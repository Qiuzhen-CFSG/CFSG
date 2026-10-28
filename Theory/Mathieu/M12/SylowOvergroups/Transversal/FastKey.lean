module

public import Theory.Mathieu.M12.SylowOvergroups.Transversal.Data

/-!
# Explicit evaluation of the Sylow coset key

Replacing the sum over a finite image by the four explicit conjugates avoids
expensive repeated permutation comparisons. This is the same coset invariant,
with its finite sum expanded using injectivity of conjugation.
-/

@[expose] public section
namespace Sporadic.Mathieu.M12SmallPair.SylowOvergroups
open SylowEnumeration


def explicitKey (g : Equiv.Perm (Fin 12)) : ℕ :=
  permutationCode (g * zPerm * g⁻¹) * (4 * 12 ^ 12) +
    (permutationCode 1 + permutationCode (g * zPerm * g⁻¹) +
      permutationCode (g * vPerm * g⁻¹) + permutationCode (g * (zPerm * vPerm) * g⁻¹))

theorem sum_conjugatePlane (g : Equiv.Perm (Fin 12)) :
    (∑ x ∈ planePerms.image (fun x => g * x * g⁻¹), permutationCode x) =
    permutationCode 1 + permutationCode (g * zPerm * g⁻¹) +
      permutationCode (g * vPerm * g⁻¹) + permutationCode (g * (zPerm * vPerm) * g⁻¹) := by
  rw [Finset.sum_image (fun x _ y _ h => mul_left_cancel (mul_right_cancel h))]
  have h1 : (1 : Equiv.Perm (Fin 12)) ∉ ({zPerm, vPerm, zPerm * vPerm} : Finset _) := by decide +kernel
  have h2 : zPerm ∉ ({vPerm, zPerm * vPerm} : Finset _) := by decide +kernel
  have h3 : vPerm ∉ ({zPerm * vPerm} : Finset _) := by decide +kernel
  simp only [planePerms, Finset.sum_insert h1, Finset.sum_insert h2,
    Finset.sum_insert h3, Finset.sum_singleton, mul_one, mul_inv_cancel]
  omega

theorem transversalKey_explicit (j : Fin 1485) :
    transversalKey j = explicitKey (transversalPerm j) := by
  unfold transversalKey explicitKey
  rw [sum_conjugatePlane]


/-- Five independent blocks keep kernel reduction of the 1,485 entries bounded. -/
def blockIndex (a : Fin 5) (b : Fin 297) : Fin 1485 :=
  ⟨a.val * 297 + b.val, by omega⟩

end Sporadic.Mathieu.M12SmallPair.SylowOvergroups
