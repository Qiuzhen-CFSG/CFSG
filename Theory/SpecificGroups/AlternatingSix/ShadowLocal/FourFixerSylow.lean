module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.SylowGeometry

/-!
# Full automorphism four-group fixers lie in the chosen Sylow subgroup

The two inner four-groups in the marked Sylow model both contain the
central involution. Its centralizer in Aut(A₆) is itself a Sylow subgroup,
so it is precisely the chosen one. A pointwise fixer of either four-group
centralizes that involution. This proves the A₆ containment in
Aschbacher--Smith 2.5.8(5), printed p.556, without falsely claiming that
every pointwise fixer is inner.
-/

public section
open Subgroup
namespace AlternatingSix.ShadowLocal
open Identification

/-- Every inner four-group in a full automorphism Sylow subgroup contains
its central involution. -/
theorem four_contains_sylow_center_generator (P : Sylow 2 AutA6)
    (E : Subgroup P) [IsKleinFour E] (hE : E ≤ sylowInner P) :
    sylowEquiv P (Holomorph.rotation ^ 4) ∈ E := by
  rcases SylowGeometry.kleinFour_subgroups_inner P E hE with rfl | rfl
  · exact mem_map_of_mem _ (by
      rw [Holomorph.kleinZero_eq_closure]
      exact subset_closure (by simp))
  · exact mem_map_of_mem _ (by
      rw [Holomorph.kleinOne_eq_closure]
      exact subset_closure (by simp))

/-- Centralizers of inner four-groups lie in every full automorphism Sylow
subgroup containing them. -/
theorem four_centralizer_le_sylow (P : Sylow 2 AutA6) (F : Subgroup A6)
    [IsKleinFour F] (hFP : F.map (MulAut.conj : A6 →* AutA6) ≤ P) :
    centralizer (F.map (MulAut.conj : A6 →* AutA6) : Set AutA6) ≤ P := by
  let J := F.map (MulAut.conj : A6 →* AutA6)
  let E := J.subgroupOf (P : Subgroup AutA6)
  let eJ := F.equivMapOfInjective (MulAut.conj : A6 →* AutA6) inner_injective
  let : IsKleinFour J := {
    card_four := (Nat.card_congr eJ.toEquiv).symm.trans IsKleinFour.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eJ).symm.trans IsKleinFour.exponent_two }
  let eE := subgroupOfEquivOfLe hFP
  let : IsKleinFour E := {
    card_four := (Nat.card_congr eE.toEquiv).trans IsKleinFour.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eE).trans IsKleinFour.exponent_two }
  have hEi : E ≤ sylowInner P := by
    rintro a ⟨f, _, hf⟩
    exact ⟨f, hf⟩
  let z : P := sylowEquiv P (Holomorph.rotation ^ 4)
  have hzJ : (z : AutA6) ∈ J := four_contains_sylow_center_generator P E hEi
  have hzZ : z ∈ center P := by
    rw [SylowGeometry.center_eq]
    exact mem_zpowers _
  have hzorder : orderOf (z : AutA6) = 2 := by
    rw [Subgroup.orderOf_coe]
    change orderOf (sylowEquiv P (Holomorph.rotation ^ 4)) = 2
    rw [(sylowEquiv P).orderOf_eq]
    apply orderOf_eq_prime
    · decide +kernel
    · decide +kernel
  have hzinner : z ∈ sylowInner P := hEi hzJ
  obtain ⟨Q, hQ⟩ := inner_involution_centralizer_sylow z hzorder hzinner
  have hPQ : (P : Subgroup AutA6) ≤ Q := by
    rw [hQ]
    intro x hx
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (mem_center_iff.mp hzZ (⟨x, hx⟩ : P))
  have heq : (P : Subgroup AutA6) = Q := (P.is_maximal' Q.isPGroup' hPQ).symm
  intro x hx
  rw [heq, hQ, mem_centralizer_singleton_iff]
  exact (hx z hzJ).symm

/-- Literal pointwise-fixer form, including outer automorphisms. -/
theorem four_fixed_mem_sylow (P : Sylow 2 AutA6) (F : Subgroup A6)
    [IsKleinFour F] (hFP : F.map (MulAut.conj : A6 →* AutA6) ≤ P)
    (a : AutA6) (ha : ∀ x ∈ F, a x = x) : a ∈ P := by
  apply four_centralizer_le_sylow P F hFP
  rintro _ ⟨x, hx, rfl⟩
  have he := aut_conj_inner a x
  rw [ha x hx, mul_inv_eq_iff_eq_mul] at he
  exact he.symm

end AlternatingSix.ShadowLocal
