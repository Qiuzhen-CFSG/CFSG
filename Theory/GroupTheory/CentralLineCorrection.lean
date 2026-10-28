module
public import Theory.GroupTheory.CentralLineCentralizer
public import Mathlib.Tactic.Group

/-!
# Correcting a lift by a central binary commutator

The nonzero commutator row into a central order-two group is surjective.
It corrects any lift fixing a vector modulo that group to an element of
the actual centralizer, without changing the lift modulo the correcting
subgroup. Source application: Aschbacher–Smith 13.8.27, printed p.963.
-/

public section

open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Correct the central error of a lift using the original commutator row. -/
theorem exists_centralizer_correction_of_binary_commutator
    (Q Z : Subgroup G) (hZ : Nat.card Z = 2)
    (hcen : Z ≤ centralizer (Q : Set G)) (t : G)
    (hcom : ∀ q ∈ Q, ⁅t,q⁆ ∈ Z)
    (hne : ∃ q ∈ Q, ⁅t,q⁆ ≠ 1) (a : G) (ha : ⁅a,t⁆ ∈ Z) :
    ∃ q ∈ Q, q*a ∈ centralizer ({t} : Set G) := by
  let f : Q →* Z := {
    toFun q := ⟨⁅t,(q:G)⁆,hcom q q.property⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' x y := by
      apply Subtype.ext
      change ⁅t,(x:G)*(y:G)⁆ = ⁅t,(x:G)⁆ * ⁅t,(y:G)⁆
      rw [commutatorElement_mul_right_eq_mul_conj]
      have hc := mem_centralizer_iff.mp (hcen (hcom y y.property)) x x.property
      calc
        _ = ⁅t,(x:G)⁆ * ((x:G)*⁅t,(y:G)⁆) * (x:G)⁻¹ := by group
        _ = _ := by rw [hc]; group }
  have hr : f.range = ⊤ := by
    have hd : Nat.card f.range ∣ 2 := hZ ▸ card_subgroup_dvd_card f.range
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
    · have hb : f.range = ⊥ := card_eq_one.mp h1
      obtain ⟨q,hq,hq1⟩ := hne
      have hm : f ⟨q,hq⟩ ∈ f.range := ⟨⟨q,hq⟩,rfl⟩
      rw [hb,mem_bot] at hm
      exact False.elim (hq1 (congrArg Subtype.val hm))
    · exact eq_top_of_card_eq f.range (h2.trans hZ.symm)
  obtain ⟨q,hq⟩ := (MonoidHom.range_eq_top.mp hr) ⟨⁅a,t⁆,ha⟩
  have hqt : ⁅t,(q:G)⁆ = ⁅a,t⁆ := congrArg Subtype.val hq
  have htq : ⁅(q:G),t⁆ = ⁅a,t⁆⁻¹ := by rw [← hqt, commutatorElement_inv]
  refine ⟨q,q.property,mem_centralizer_singleton_iff.mpr ?_⟩
  apply commutatorElement_eq_one_iff_mul_comm.mp
  rw [commutatorElement_mul_left_eq_conj_mul, htq]
  have hc := mem_centralizer_iff.mp (hcen ha) q q.property
  rw [hc]
  group

end Subgroup
