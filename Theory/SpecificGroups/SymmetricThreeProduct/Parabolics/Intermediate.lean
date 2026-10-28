module
public import Theory.SpecificGroups.SymmetricThreeProduct.Parabolics.Structure
public import Mathlib.GroupTheory.Subgroup.Simple
/-!
# Strict overgroups of Sylow subgroups in S₃ × S₃

Every proper subgroup strictly containing a Sylow two-subgroup is one of
the two coordinate parabolics after conjugation. Its order is twelve and
its two-core has order two. The coatom classification and divisibility
of subgroup orders give the result without enumerating additional groups.

Source: Aschbacher--Smith15.2.5, printed p.1107.
-/
public section
open Subgroup
namespace SymmetricThreeProduct
private theorem eq_of_between_four_twelve (A B C : Subgroup G)
    (hAB : A ≤ B) (hBC : B ≤ C) (hA : Nat.card A = 4)
    (hC : Nat.card C = 12) (hne : A ≠ B) : B = C := by
  have h4 : 4 ∣ Nat.card B := hA ▸ card_dvd_of_le hAB
  have h12 : Nat.card B ∣ 12 := hC ▸ card_dvd_of_le hBC
  have hm := Nat.mem_divisors.mpr ⟨h12,(by decide : 12 ≠ 0)⟩
  rw [show Nat.divisors 12 = {1,2,3,4,6,12} by decide] at hm
  simp only [Finset.mem_insert,Finset.mem_singleton] at hm
  have hc : Nat.card B = 4 ∨ Nat.card B = 12 := by omega
  rcases hc with hc | hc
  · exact (hne (eq_of_le_of_card_ge hAB (by rw [hA,hc]))).elim
  · exact eq_of_le_of_card_ge hBC (by rw [hC,hc])

theorem strict_intermediate_over_borel (A : Subgroup G)
    (hBA : borel < A) (hA : A ≠ ⊤) : A = leftParabolic ∨ A = rightParabolic := by
  obtain ⟨B,hB,hAB⟩ := (eq_top_or_exists_le_coatom A).resolve_left hA
  rcases coatom_over_borel B hB (hBA.le.trans hAB) with rfl | rfl
  · exact Or.inl (eq_of_between_four_twelve borel A leftParabolic hBA.le hAB
      card_borel card_leftParabolic hBA.ne)
  · exact Or.inr (eq_of_between_four_twelve borel A rightParabolic hBA.le hAB
      card_borel card_rightParabolic hBA.ne)
end SymmetricThreeProduct

namespace SymmetricThreeProduct

theorem strict_intermediate_over_sylow (S : Sylow 2 G) (A : Subgroup G)
    (hSA : (S : Subgroup G) < A) (hA : A ≠ ⊤) :
    Nonempty (A ≃* leftParabolic) ∨ Nonempty (A ≃* rightParabolic) := by
  obtain ⟨g,hg,_⟩ := coatom_over_sylow S
  let e := (MulAut.conj g).mapSubgroup
  have hBA : borel < e.symm A := by
    have hh := e.symm.strictMono hSA
    rw [←hg,e.symm_apply_apply] at hh
    exact hh
  have hn : e.symm A ≠ ⊤ := by
    intro he
    apply hA
    have hh := congrArg e he
    simpa only [e.apply_symm_apply,e.map_top] using hh
  let j : A ≃* e.symm A := (MulAut.conj g).symm.subgroupMap A
  rcases strict_intermediate_over_borel (e.symm A) hBA hn with he | he
  · exact Or.inl ⟨j.trans (MulEquiv.subgroupCongr he)⟩
  · exact Or.inr ⟨j.trans (MulEquiv.subgroupCongr he)⟩

end SymmetricThreeProduct

namespace SymmetricThreeProduct
variable {D : Type*} [Group D] [Finite D]

/-- Every strict proper overgroup of a Sylow in an actual product action
has order twelve and two-core of order two. -/
theorem intermediate_card_and_core (e : D ≃* G) (S : Sylow 2 D) (A : Subgroup D)
    (hSA : (S : Subgroup D) < A) (hA : A ≠ ⊤) :
    Nat.card A = 12 ∧ Nat.card (pCore 2 A) = 2 := by
  let P := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let B := e.mapSubgroup A
  have hPB : (P : Subgroup G) < B := e.mapSubgroup.strictMono hSA
  have hB : B ≠ ⊤ := by
    intro he
    apply hA
    exact e.mapSubgroup.injective (he.trans e.mapSubgroup.map_top.symm)
  let j : A ≃* B := e.subgroupMap A
  rcases strict_intermediate_over_sylow P B hPB hB with hk | hk
  · obtain ⟨k⟩ := hk
    let a := j.trans k
    refine ⟨(Nat.card_congr a.toEquiv).trans card_leftParabolic,?_⟩
    have hc := card_left_twoCore
    rw [←pCore_map_iso 2 a,card_map_of_injective a.injective] at hc
    exact hc
  · obtain ⟨k⟩ := hk
    let a := j.trans k
    refine ⟨(Nat.card_congr a.toEquiv).trans card_rightParabolic,?_⟩
    have hc := card_right_twoCore
    rw [←pCore_map_iso 2 a,card_map_of_injective a.injective] at hc
    exact hc
end SymmetricThreeProduct


