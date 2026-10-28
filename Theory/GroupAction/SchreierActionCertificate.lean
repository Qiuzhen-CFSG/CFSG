module

public import Theory.GroupAction.CentralizerFixedPoints

/-!
# Schreier certificates for permutation actions and centralizers

For representatives `r x` with `r base = 1`, certify that each forward edge
`(r (s • x))⁻¹ * s * r x` belongs to a subgroup H. Closure under products
and inverses then proves this for every group element. Evaluating at the
base point puts its stabilizer in H. The proof works for arbitrary index
types and derives the inverse edges from the forward ones.

A conjugation-equivariant labeling identifies the distinguished stabilizer
with an element centralizer. Equivariance also extends from generators.
These lemmas implement Schreier rewriting directly in the left-action
convention, without choosing a quotient transversal.

Application: `Fischer/AtlasCarriers/Fi22TransvectionComparison/Setup.lean`
reduces centralizer generation for GLS3 Table 5.3t to finite certificates
for the two actual ATLAS permutations.
-/

@[expose] public section

namespace Theory.GroupAction.SchreierActionCertificate
variable {G X : Type*} [Group G]

/-- Forward Schreier edges in `H` force the stabilizer of the base point into `H`. -/
theorem stabilizer_le_of_edges (ρ : G →* Equiv.Perm X) (S : Set G)
    (hS : Subgroup.closure S = ⊤) (H : Subgroup G)
    (rep : X → G) (base : X) (hbase : rep base = 1)
    (hedge : ∀ s ∈ S, ∀ x, (rep (ρ s x))⁻¹ * s * rep x ∈ H)
    (g : G) (hg : ρ g base = base) : g ∈ H := by
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
        simpa only [map_inv, Equiv.Perm.inv_def, Equiv.apply_symm_apply, mul_inv_rev, inv_inv,
          mul_assoc] using hm }
  have hle : Subgroup.closure S ≤ K := (Subgroup.closure_le K).mpr hedge
  have hgK : g ∈ K := hle (hS ▸ Subgroup.mem_top g)
  have hx := hgK base
  simpa only [hg, hbase, inv_one, one_mul, mul_one] using hx

/-- Conjugation equivariance only needs checking on a generating set. -/
theorem conjugation_equivariant_of_generators (ρ : G →* Equiv.Perm X) (S : Set G)
    (hS : Subgroup.closure S = ⊤) (root : X → G)
    (hroot : ∀ s ∈ S, ∀ x, root (ρ s x) = s * root x * s⁻¹)
    (g : G) (x : X) : root (ρ g x) = g * root x * g⁻¹ := by
  let K : Subgroup G :=
    { carrier := {g | ∀ x, root (ρ g x) = g * root x * g⁻¹}
      one_mem' := by simp
      mul_mem' := by
        intro g k hg hk x
        simp only [map_mul, Equiv.Perm.mul_apply, hg _, hk _, mul_inv_rev, mul_assoc]
      inv_mem' := by
        intro g hg x
        have hx := hg (ρ g⁻¹ x)
        simp only [map_inv, Equiv.Perm.inv_def, Equiv.apply_symm_apply] at hx
        simp only [map_inv, Equiv.Perm.inv_def, inv_inv]
        rw [hx]
        simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] }
  have hle : Subgroup.closure S ≤ K := (Subgroup.closure_le K).mpr hroot
  exact hle (hS ▸ Subgroup.mem_top g) x

/-- An equivariant conjugate labeling turns the stabilizer criterion into a
centralizer criterion. Only the fiber of the distinguished element is needed. -/
theorem centralizer_le_of_edges (ρ : G →* Equiv.Perm X) (S : Set G)
    (hS : Subgroup.closure S = ⊤) (H : Subgroup G)
    (rep root : X → G) (base : X) (t : G)
    (hbase : rep base = 1) (hrootBase : root base = t)
    (hrootFiber : ∀ x, root x = t → x = base)
    (hroot : ∀ s ∈ S, ∀ x, root (ρ s x) = s * root x * s⁻¹)
    (hedge : ∀ s ∈ S, ∀ x, (rep (ρ s x))⁻¹ * s * rep x ∈ H) :
    Subgroup.centralizer {t} ≤ H := by
  intro g hg
  apply stabilizer_le_of_edges ρ S hS H rep base hbase hedge g
  apply hrootFiber
  rw [conjugation_equivariant_of_generators ρ S hS root hroot, hrootBase]
  rw [Subgroup.mem_centralizer_singleton_iff.mp hg, mul_inv_cancel_right]

end Theory.GroupAction.SchreierActionCertificate

