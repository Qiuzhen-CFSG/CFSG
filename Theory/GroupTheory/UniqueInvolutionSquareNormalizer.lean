module
public import Theory.GroupTheory.NormalFourCentralizerSeparation

/-!
# Sylow centralizer control from a unique involution square

If the elements of order four in a subgroup all square to z, and at least
one exists, its normalizer centralizes z. Thus local Sylow control in the
common centralizer of j and z promotes to Sylow control in C_G(j).
This avoids identifying the entire Sylow-centralizer isomorphism type.
Source application: Aschbacher–Smith 14.2.17(1), printed p.987.
-/

open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

public theorem normalizer_le_centralizer_of_unique_involution_square
    (P : Subgroup G) (z : G)
    (hroot : ∃ x ∈ P, orderOf x = 4)
    (hsquare : ∀ x ∈ P, orderOf x = 4 → x ^ 2 = z) :
    normalizer (P : Set G) ≤ centralizer ({z} : Set G) := by
  obtain ⟨x,hx,hx4⟩ := hroot
  intro g hg
  have hxg : g*x*g⁻¹ ∈ P := (mem_normalizer_iff.mp hg x).mp hx
  have hg4 : orderOf (g*x*g⁻¹) = 4 := ((MulAut.conj g).orderOf_eq x).trans hx4
  have h1 := hsquare _ hxg hg4
  have h2 := hsquare x hx hx4
  have he : g*z*g⁻¹=z := by
    simpa only [h2,MulAut.conj_apply] using (map_pow (MulAut.conj g) x 2).trans h1
  exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he)

/-- A locally Sylow centralizer with a unique involution square is globally
Sylow, expressed by its literal relative index. -/
public theorem not_two_dvd_centralizer_relIndex_of_unique_square [Finite G]
    (P : Subgroup G) (j z : G) (hp : IsPGroup 2 P)
    (hPj : P ≤ centralizer ({j} : Set G))
    (hlocal : ¬ 2 ∣ P.relIndex
      (centralizer ({z} : Set G) ⊓ centralizer ({j} : Set G)))
    (hroot : ∃ x ∈ P, orderOf x = 4)
    (hsquare : ∀ x ∈ P, orderOf x = 4 → x ^ 2 = z) :
    ¬ 2 ∣ P.relIndex (centralizer ({j} : Set G)) := by
  apply not_dvd_relIndex_of_normalizer_inf_le P _ _ hp hPj hlocal
  exact le_inf (inf_le_left.trans
    (normalizer_le_centralizer_of_unique_involution_square P z hroot hsquare)) inf_le_right
end Subgroup
