module

public import Theory.GroupTheory.SylowCentralizerTrivialIntersection

/-!
# Transporting root centralizer containment to Sylow subgroups

A centralizer bound in one Sylow subgroup transports by Sylow conjugacy.
The centralizer argument then makes every nontrivial Sylow intersection
determine its Sylow subgroup. This packages the actual root calculations
for the binary linear and Suzuki cases of Aschbacher--Smith 2.5.3(3), p.552.
-/

public section
namespace Sylow
open Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem centralizer_le_of_one_sylow (R P : Sylow p G)
    (hc : ∀ x ∈ (R : Subgroup G), x ≠ 1 → centralizer ({x} : Set G) ≤ R)
    {x : G} (hx : x ∈ P) (hne : x ≠ 1) :
    centralizer ({x} : Set G) ≤ P := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G R P
  obtain ⟨z, hz, rfl⟩ := hx
  let e := MulAut.conj g
  have hz1 : z ≠ 1 := by intro h; exact hne (by simp [h])
  intro y hy
  have hcomm : Commute y (e z) := mem_centralizer_singleton_iff.mp hy
  have hcz : Commute (e.symm y) z := by
    simpa only [e.symm_apply_apply] using hcomm.map e.symm
  exact ⟨e.symm y, hc z hz hz1 (mem_centralizer_singleton_iff.mpr hcz.eq),
    e.apply_symm_apply y⟩

theorem eq_of_inf_ne_bot_of_one_sylow (R P Q : Sylow p G)
    (hc : ∀ x ∈ (R : Subgroup G), x ≠ 1 → centralizer ({x} : Set G) ≤ R)
    (hi : (P : Subgroup G) ⊓ (Q : Subgroup G) ≠ ⊥) : P = Q :=
  (P.eq_of_inf_ne_bot_of_centralizer_le Q
    (fun _ hx hn => centralizer_le_of_one_sylow R P hc hx hn) hi).symm

end Sylow
