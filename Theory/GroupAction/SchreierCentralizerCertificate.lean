module

public import Theory.GroupAction.SchreierActionCertificate

/-!
# Centralizer bounds from separating Schreier representatives

Forward Schreier edges in `H` give a decomposition `g = r * h` for every
generated element, including inverse words. If `H` centralizes `t`, then so
does `r` whenever `g` centralizes `t`. Separating the identity representative
from all other representatives by their commutators with `t` therefore bounds
the centralizer by `H`. No identification of the permutation action with a
conjugation action, or group-order computation, is required.

Application: the concrete Fi23 centralizer in GLS3 Table 5.3u, using the exact
ATLAS permutations and eight published witness permutations.
-/

public section
namespace Theory.GroupAction.SchreierActionCertificate
variable {G X : Type*} [Group G]

/-- Generator edges extend to all elements of their closure. -/
theorem schreier_mem_of_mem_closure (ρ : G →* Equiv.Perm X) (S : Set G)
    (H : Subgroup G) (rep : X → G)
    (hedge : ∀ s ∈ S, ∀ x, (rep (ρ s x))⁻¹ * s * rep x ∈ H)
    {g : G} (hg : g ∈ Subgroup.closure S) (x : X) :
    (rep (ρ g x))⁻¹ * g * rep x ∈ H := by
  let K : Subgroup G :=
    { carrier := {g | ∀ x, (rep (ρ g x))⁻¹ * g * rep x ∈ H}
      one_mem' := by simp
      mul_mem' := by
        intro g k hg hk x
        have hm := H.mul_mem (hg (ρ k x)) (hk x)
        simpa only [map_mul, Equiv.Perm.mul_apply, mul_assoc,
          mul_inv_cancel_left] using hm
      inv_mem' := by
        intro g hg x
        have hm := H.inv_mem (hg (ρ g⁻¹ x))
        simpa only [map_inv, Equiv.Perm.inv_def, Equiv.apply_symm_apply,
          mul_inv_rev, inv_inv, mul_assoc] using hm }
  exact ((Subgroup.closure_le K).mpr hedge hg) x

/-- Separate only the representatives commuting with `t`; pairwise conjugate
separation and a faithful action are unnecessary. -/
theorem mem_of_centralizing_of_schreier (ρ : G →* Equiv.Perm X) (S : Set G)
    (H : Subgroup G) (rep : X → G) (base : X) (t : G)
    (hbase : rep base = 1)
    (hedge : ∀ s ∈ S, ∀ x, (rep (ρ s x))⁻¹ * s * rep x ∈ H)
    (hcentral : H ≤ Subgroup.centralizer {t})
    (hsep : ∀ x, rep x ∈ Subgroup.centralizer {t} → rep x = 1)
    {g : G} (hg : g ∈ Subgroup.closure S)
    (hgt : g ∈ Subgroup.centralizer {t}) : g ∈ H := by
  have hk : (rep (ρ g base))⁻¹ * g ∈ H := by
    simpa only [hbase, mul_one] using
      schreier_mem_of_mem_closure ρ S H rep hedge hg base
  have hr : rep (ρ g base) ∈ Subgroup.centralizer {t} := by
    have hm := (Subgroup.centralizer {t}).mul_mem hgt
      ((Subgroup.centralizer {t}).inv_mem (hcentral hk))
    simpa only [mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul] using hm
  simpa only [hsep _ hr, inv_one, one_mul] using hk

end Theory.GroupAction.SchreierActionCertificate
