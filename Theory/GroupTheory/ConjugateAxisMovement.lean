module
public import Theory.GroupTheory.SubgroupConjugation

/-!
# Movement detected by two conjugate axes

Suppose two conjugates of E span a finite subgroup U. An element x preserving
J and a commutator axis A cannot move U while sending E into its centralizer,
provided the local centralizer-and-commutator test forces that conjugate into U.
The commutator of x and the spanning mover acts trivially on E, so both
conjugate axes would remain in U and finiteness would force x to normalize U.

Source application: Aschbacher–Smith 2.4.29, printed pp.545–546.
-/
public section
namespace Subgroup
open scoped commutatorElement

private theorem conjugate_axes_commute {G : Type*} [Group G]
    (E J : Subgroup G) (hJE : J ≤ normalizer (E : Set G))
    (x s : G) (hc : ⁅x⁻¹,s⁻¹⁆ ∈ J) :
    (E.conjBy s).conjBy x = (E.conjBy x).conjBy s := by
  have he : x*s = (s*x)*⁅x⁻¹,s⁻¹⁆ := by
    simp only [commutatorElement_def, inv_inv, mul_assoc, mul_inv_cancel_left]
  have hn : E.conjBy ⁅x⁻¹,s⁻¹⁆ = E :=
    mem_normalizer_iff_map_conj_eq.mp (hJE hc)
  rw [←conjBy_mul, ←conjBy_mul, he, conjBy_mul, hn]

theorem not_conjBy_le_centralizer_of_span {G : Type*} [Group G] [Finite G]
    (E J U A : Subgroup G) (x s : G)
    (hEJ : E ≤ J) (hJx : x ∈ normalizer (J : Set G))
    (hAx : A.conjBy x = A) (hcomm : ⁅E,J⁆ ≤ A)
    (hcriterion : ∀ B : Subgroup G, B ≤ J → ⁅B,J⁆ ≤ A →
      B ≤ centralizer (E : Set G) → B ≤ U)
    (hspan : U = E ⊔ E.conjBy s)
    (hsU : s ∈ normalizer (U : Set G))
    (hJE : J ≤ normalizer (E : Set G))
    (hc : ⁅x⁻¹,s⁻¹⁆ ∈ J)
    (hxU : x ∉ normalizer (U : Set G)) :
    ¬ E.conjBy x ≤ centralizer (E : Set G) := by
  intro hcentral
  have hJfix : J.conjBy x = J := mem_normalizer_iff_map_conj_eq.mp hJx
  have hB : E.conjBy x ≤ J := (map_mono hEJ).trans_eq hJfix
  have hBA : ⁅E.conjBy x,J⁆ ≤ A := by
    have hh := map_mono (f := (MulAut.conj x).toMonoidHom) hcomm
    rw [map_commutator] at hh
    change ⁅E.conjBy x,J.conjBy x⁆ ≤ A.conjBy x at hh
    rwa [hJfix,hAx] at hh
  have hBU : E.conjBy x ≤ U := hcriterion _ hB hBA hcentral
  have hUx : U.conjBy x ≤ U := by
    rw [congrArg (fun B : Subgroup G => B.conjBy x) hspan,
      show (E ⊔ E.conjBy s).conjBy x =
      E.conjBy x ⊔ (E.conjBy s).conjBy x from map_sup _ _ _]
    apply sup_le hBU
    rw [conjugate_axes_commute E J hJE x s hc]
    exact (map_mono hBU).trans_eq (mem_normalizer_iff_map_conj_eq.mp hsU)
  apply hxU
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge hUx
  change Nat.card U ≤ Nat.card (U.map (MulAut.conj x).toMonoidHom)
  rw [card_map_of_injective (MulAut.conj x).injective]


end Subgroup
