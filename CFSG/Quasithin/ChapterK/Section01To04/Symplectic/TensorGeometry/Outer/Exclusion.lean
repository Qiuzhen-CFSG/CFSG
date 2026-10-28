module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorReduction

/-!
# Arithmetic assembly of outer-actor exclusion

Singleton outer actors have codimension 6s. A larger actor has codimension at
least 8s, while its rank is at most 3s+1. Equality in the resulting bound can
only survive at s=1 and maximal rank; the source's strict codimension bound
eliminates this case. All representation estimates are explicit premises here.
This conditional reduction does not itself prove the outer branch of K.3.4.2.

Source: Aschbacher–Smith, K.3.4.2, printed p.457.
-/

public section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Outer
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V) (L : Subgroup G)

theorem elementary_le_of_outer_estimates {s : ℕ} (hs : 0 < s)
    (hdim : Module.finrank (ZMod 2) V = 16 * s)
    (hrank : ∀ (A : Subgroup G), IsElementaryTwo A →
      ∀ t ∈ A, t ∉ L → rank A ≤ 3 * s + 1)
    (hsingle : ∀ t : G, orderOf t = 2 → t ∉ L →
      Module.finrank (ZMod 2) (fixedSpace ρ (zpowers t)) = 10 * s)
    (hproper : ∀ (A : Subgroup G), IsElementaryTwo A →
      ∀ t : G, orderOf t = 2 → t ∉ L → zpowers t < A →
      8 * s ≤ fixedCodim ρ A ∧ (rank A = 3 * s + 1 → 8 * s < fixedCodim ρ A))
    (A : Subgroup G) (hA : IsElementaryTwo A) (hr : fixedCodim ρ A ≤ 2 * rank A) :
    A ≤ L := by
  intro t htA
  by_contra hout
  let : IsElementaryAbelian 2 A := hA.2
  have ht : orderOf t = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian t htA) (fun he => hout (he ▸ L.one_mem))
  have hle : zpowers t ≤ A := (zpowers_le).mpr htA
  by_cases he : zpowers t = A
  · have hfix := hsingle t ht hout
    have hsum := fixedCodim_add_finrank ρ (zpowers t)
    have hsize : rank (zpowers t) = 1 := by norm_num [BinaryOffender.rank, Nat.card_zpowers, ht]
    rw [← he] at hr
    omega
  · obtain ⟨hlower, hstrict⟩ := hproper A hA t ht hout (lt_of_le_of_ne hle he)
    have hupper := hrank A hA t htA hout
    by_cases heq : rank A = 3 * s + 1
    · have hh := hstrict heq
      omega
    · omega

end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Outer
