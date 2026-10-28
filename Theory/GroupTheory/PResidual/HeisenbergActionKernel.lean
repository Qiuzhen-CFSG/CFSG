module
public import Theory.GroupTheory.PResidual.CubicKernelResidual
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms
public import Theory.GroupTheory.PGroup.OrderTwentySeven

/-!
# Derived residuals in a Heisenberg two-core quotient

If A/O₂(A) has order 27 and gcd(27, |B|) = 3, every homomorphism A → B
kills O²(A′). Indeed ker(f)O₂(A) has index one or three, hence contains A′;
two-perfectness removes the two-core from the containment. If A/O₂(A) is
extraspecial of order a power of three, O²(A′) is nontrivial, since its
image contains the cubic derived subgroup of that quotient.

Source application: the escaping Heisenberg lift in Aschbacher–Smith,
14.7.9 and 14.7.27, printed pp.1045,1054–1055, refs/quasithin.pdf.
The actual ambient application is LocalReduction.SolvableHeisenbergResidual.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative

namespace MonoidHom

/-- The derived two-residual is killed by an action with only a cubic odd image. -/
theorem derived_twoResidual_le_kernel
    {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (f : A →* B) (h27 : Nat.card (A ⧸ pCore 2 A) = 27)
    (hB : Nat.gcd 27 (Nat.card B) = 3) :
    (pResidual 2 (_root_.commutator A)).map (_root_.commutator A).subtype ≤ f.ker := by
  let N := f.ker ⊔ pCore 2 A
  have hN27 : N.index ∣ 27 := by
    rw [← h27, ← index_eq_card]
    exact index_dvd_of_le (show pCore 2 A ≤ N from le_sup_right)
  have hNB : N.index ∣ Nat.card B := by
    have hh : N.index ∣ f.ker.index := index_dvd_of_le le_sup_left
    rw [index_ker] at hh
    exact hh.trans (card_subgroup_dvd_card f.range)
  have hN3 : N.index ∣ 3 := hB ▸ Nat.dvd_gcd hN27 hNB
  have hderived : _root_.commutator A ≤ N := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hN3 with h1 | h3
    · rw [index_eq_one.mp h1]
      exact le_top
    · let : IsCyclic (A ⧸ N) := isCyclic_of_prime_card (by simpa [index_eq_card] using h3)
      rw [←QuotientGroup.ker_mk' N,←Subgroup.map_eq_bot_iff,
        _root_.map_commutator_eq,MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N)]
      exact commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer ⊤)
  exact le_normal_of_isPPerfect_of_le_sup_pGroup _ f.ker (pCore 2 A)
    (isPPerfect_embedded_pResidual 2 _) pCore_isPGroup ((map_subtype_le _).trans hderived)

end MonoidHom

namespace Subgroup

/-- An extraspecial three-group core quotient has a nontrivial derived two-residual. -/
theorem extraspecial_derived_twoResidual_ne_bot
    {A : Type*} [Group A] [Finite A]
    [IsExtraspecial 3 (A ⧸ pCore 2 A)] :
    (pResidual 2 (_root_.commutator A)).map (_root_.commutator A).subtype ≠ ⊥ := by
  let Q := A ⧸ pCore 2 A
  let q := QuotientGroup.mk' (pCore 2 A)
  have hmap : (_root_.commutator A).map q = _root_.commutator Q := by
    rw [_root_.map_commutator_eq,MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
    rfl
  have hc : Nat.card (_root_.commutator Q) = 3 := by
    rw [IsExtraspecial.commutator_eq_center (p := 3),IsExtraspecial.center_order_p 3 Q]
  have hp : IsPPerfect 2 (_root_.commutator Q) := by
    apply (pResidual_eq_top_iff 2 _).mp
    apply top_unique
    intro x _
    exact mem_pResidual_of_orderOf_coprime
      ((by decide : Nat.Coprime 2 3).of_dvd_right (hc ▸ _root_.orderOf_dvd_natCard x))
  intro hz
  have hm := congrArg (fun C : Subgroup A => C.map q) hz
  rw [map_embedded_pResidual,hmap,(pResidual_eq_top_iff 2 _).mpr hp,
    ←MonoidHom.range_eq_map,range_subtype,Subgroup.map_bot] at hm
  rw [hm,card_bot] at hc
  omega

end Subgroup
