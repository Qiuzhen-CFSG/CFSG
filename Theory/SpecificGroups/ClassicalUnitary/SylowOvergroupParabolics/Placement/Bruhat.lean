module

public import Mathlib.GroupTheory.Sylow

/-!
# Passing from a unipotent overgroup to a Borel overgroup

Suppose `G = U N U`, `H` normalizes `U`, and `N` normalizes `H`.
For any subgroup `Q` containing `U`, Bruhat factorization gives
`Q = U (N ∩ Q) U`. Consequently the sets `Q H` and `H Q` coincide,
and their product is the subgroup `Q ⊔ H`.

If the conjugates of `U` generate `G`, this enlargement is proper whenever
`Q` is proper: otherwise every conjugate of `U` lies in `Q`, because
`G = Q H` and `H` normalizes `U`.

This is the portion of GLS3, Theorem 2.6.7 needed for proper-overgroup
placement. Unlike a full Levi decomposition, it does not require computing
the residual of `Q`. Concrete groups must supply the Bruhat factorization,
the two normalization statements, and normal generation.
-/

public section

open Subgroup
open scoped Pointwise

namespace Theory.GroupTheory

variable {G : Type*} [Group G]

/-- Structural data for a Borel containing an actual Sylow two-subgroup.
None of the fields asserts overgroup placement. -/
structure SylowBruhatData (B : Subgroup G) where
  sylow : Sylow 2 G
  cartan : Subgroup G
  monomial : Subgroup G
  borel_eq : B = (sylow : Subgroup G) ⊔ cartan
  cartan_normalizes : cartan ≤ normalizer (sylow : Set G)
  monomial_normalizes : monomial ≤ normalizer (cartan : Set G)
  factorization : ∀ g : G, ∃ u ∈ (sylow : Subgroup G),
    ∃ n ∈ monomial, ∃ v ∈ (sylow : Subgroup G), g = u * n * v
  normal_generates : normalClosure (sylow : Set G) = ⊤

namespace SylowBruhatData

variable {B : Subgroup G} (D : SylowBruhatData B)

/-- An overgroup inherits the Bruhat factorization, with its middle factor
in the intersection with the monomial subgroup. -/
theorem overgroup_factorization (Q : Subgroup G)
    (hUQ : (D.sylow : Subgroup G) ≤ Q) :
    (Q : Set G) = (D.sylow : Set G) * (D.monomial ⊓ Q : Subgroup G) *
      (D.sylow : Set G) := by
  ext g
  constructor
  · intro hg
    obtain ⟨u, hu, n, hn, v, hv, rfl⟩ := D.factorization g
    have hnQ : n ∈ Q := by
      have := Q.mul_mem (Q.mul_mem (Q.inv_mem (hUQ hu)) hg)
        (Q.inv_mem (hUQ hv))
      simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one] using this
    exact ⟨u * n, ⟨u, hu, n, ⟨hn, hnQ⟩, rfl⟩, v, hv, rfl⟩
  · rintro ⟨_, ⟨u, hu, n, hn, rfl⟩, v, hv, rfl⟩
    exact Q.mul_mem (Q.mul_mem (hUQ hu) hn.2) (hUQ hv)

/-- The Cartan and a unipotent overgroup permute as sets. This alone
does not assert that the Cartan normalizes the overgroup. -/
theorem cartan_mul_overgroup (Q : Subgroup G)
    (hUQ : (D.sylow : Subgroup G) ≤ Q) :
    (D.cartan : Set G) * Q = (Q : Set G) * D.cartan := by
  have hHU := set_mul_normalizer_comm (D.cartan : Set G)
    (D.sylow : Subgroup G) D.cartan_normalizes
  change (D.cartan : Set G) * (D.sylow : Set G) =
    (D.sylow : Set G) * (D.cartan : Set G) at hHU
  have hNH := set_mul_normalizer_comm
    (D.monomial ⊓ Q : Subgroup G) D.cartan
    (show D.monomial ⊓ Q ≤ normalizer (D.cartan : Set G) from
      inf_le_left.trans D.monomial_normalizes)
  rw [D.overgroup_factorization Q hUQ]
  calc
    (D.cartan : Set G) * ((D.sylow : Set G) * (D.monomial ⊓ Q : Subgroup G) *
        (D.sylow : Set G)) =
      (D.sylow : Set G) * ((D.cartan : Set G) * (D.monomial ⊓ Q : Subgroup G)) *
        (D.sylow : Set G) := by
          rw [← mul_assoc, ← mul_assoc, hHU]
          simp only [mul_assoc]
    _ = (D.sylow : Set G) * ((D.monomial ⊓ Q : Subgroup G) *
        (D.cartan : Set G)) * (D.sylow : Set G) := by rw [hNH]
    _ = ((D.sylow : Set G) * (D.monomial ⊓ Q : Subgroup G) *
        (D.sylow : Set G)) * (D.cartan : Set G) := by
      simp only [mul_assoc]
      rw [hHU]

private theorem coe_sup_of_permute (Q H : Subgroup G)
    (hperm : (H : Set G) * Q = (Q : Set G) * H) :
    ((Q ⊔ H : Subgroup G) : Set G) = (Q : Set G) * H := by
  let P : Subgroup G :=
    { carrier := (Q : Set G) * H
      one_mem' := ⟨1, Q.one_mem, 1, H.one_mem, mul_one _⟩
      mul_mem' := by
        rintro _ _ ⟨q, hq, h, hh, rfl⟩ ⟨r, hr, k, hk, rfl⟩
        have hhr : h * r ∈ (Q : Set G) * H :=
          hperm ▸ (show h * r ∈ (H : Set G) * Q from ⟨h, hh, r, hr, rfl⟩)
        obtain ⟨r', hr', h', hh', he⟩ := hhr
        change r' * h' = h * r at he
        refine ⟨q * r', Q.mul_mem hq hr', h' * k, H.mul_mem hh' hk, ?_⟩
        calc
          q * r' * (h' * k) = q * (r' * h') * k := by simp only [mul_assoc]
          _ = q * (h * r) * k := by rw [he]
          _ = (q * h) * (r * k) := by simp only [mul_assoc]
      inv_mem' := by
        rintro _ ⟨q, hq, h, hh, rfl⟩
        rw [mul_inv_rev]
        exact hperm ▸ (show h⁻¹ * q⁻¹ ∈ (H : Set G) * Q from
          ⟨h⁻¹, H.inv_mem hh, q⁻¹, Q.inv_mem hq, rfl⟩) }
  have hQP : Q ≤ P := fun q hq => ⟨q, hq, 1, H.one_mem, mul_one _⟩
  have hHP : H ≤ P := fun h hh => ⟨1, Q.one_mem, h, hh, one_mul _⟩
  apply Set.Subset.antisymm (show (Q ⊔ H : Subgroup G) ≤ P from sup_le hQP hHP)
  rintro _ ⟨q, hq, h, hh, rfl⟩
  exact (Q ⊔ H).mul_mem ((show Q ≤ Q ⊔ H from le_sup_left) hq)
    ((show H ≤ Q ⊔ H from le_sup_right) hh)

/-- The subgroup generated with the Cartan is the literal product. -/
theorem coe_sup_cartan (Q : Subgroup G)
    (hUQ : (D.sylow : Subgroup G) ≤ Q) :
    ((Q ⊔ D.cartan : Subgroup G) : Set G) = (Q : Set G) * D.cartan :=
  coe_sup_of_permute Q D.cartan (D.cartan_mul_overgroup Q hUQ)

/-- Normal generation is precisely what excludes the whole-group product. -/
theorem sup_cartan_ne_top (Q : Subgroup G)
    (hUQ : (D.sylow : Subgroup G) ≤ Q) (hQ : Q ≠ ⊤) :
    Q ⊔ D.cartan ≠ ⊤ := by
  intro htop
  have hgen : normalClosure (D.sylow : Set G) ≤ Q := by
    rw [normalClosure, closure_le]
    intro x hx
    obtain ⟨u, hu, hux⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨g, rfl⟩ := isConj_iff.mp hux
    have hg : g ∈ ((Q ⊔ D.cartan : Subgroup G) : Set G) := by rw [htop]; trivial
    rw [D.coe_sup_cartan Q hUQ] at hg
    obtain ⟨q, hq, h, hh, rfl⟩ := hg
    have hconj := (mem_normalizer_iff.mp (D.cartan_normalizes hh) u).mp hu
    have hm := Q.mul_mem (Q.mul_mem hq (hUQ hconj)) (Q.inv_mem hq)
    change (q * h) * u * (q * h)⁻¹ ∈ Q
    simpa only [mul_inv_rev, mul_assoc] using hm
  exact hQ (top_le_iff.mp (D.normal_generates ▸ hgen))

/-- A proper Sylow overgroup is contained in a proper Borel overgroup.
The Borel is `U ⊔ H`; the intermediate group is the proved product `Q H`. -/
theorem exists_proper_borel_overgroup (Q : Subgroup G)
    (hUQ : (D.sylow : Subgroup G) ≤ Q) (hQ : Q ≠ ⊤) :
    ∃ P : Subgroup G, B ≤ P ∧ Q ≤ P ∧ P ≠ ⊤ := by
  refine ⟨Q ⊔ D.cartan, ?_, le_sup_left, D.sup_cartan_ne_top Q hUQ hQ⟩
  exact D.borel_eq.le.trans (sup_le_sup_right hUQ _)

end SylowBruhatData
end Theory.GroupTheory
