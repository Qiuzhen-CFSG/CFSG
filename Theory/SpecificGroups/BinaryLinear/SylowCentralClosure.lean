module
public import Theory.SpecificGroups.BinaryLinear.SylowPointwiseInner
public import Theory.Representation.BinaryNaturalDual.ModelOrbits.AutomorphismModel.Structure
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Proper normal closures of Sylow-central binary linear automorphisms

Intersect an automorphism-group Sylow subgroup with the inner subgroup and
pull it back to the original linear group. A centralizing automorphism fixes
that Sylow pointwise, so pointwise Sylow rigidity makes it inner. The graph
automorphism lies outside the inner subgroup in dimensions four and five;
therefore the centralizing element cannot generate the full automorphism
group by normal closure.

Source application: Aschbacher--Smith, original 15.2.27(2), printed p.1119,
excluding rank-one chief displacement via the original G.6.4(4).
-/

public section
open Subgroup
namespace BinaryLinear.OuterCyclic
open BinaryNaturalDual.ModelOrbits.AutomorphismModel

/-- Every automorphism centralizing a full Sylow of Aut(Lₙ(2)) is inner. -/
theorem central_sylow_automorphism_inner {n : ℕ} (hn : n = 4 ∨ n = 5)
    (S : Sylow 2 (MulAut (LinearGroup n))) (a : MulAut (LinearGroup n))
    (hc : ∀ s ∈ S, Commute a s) : a ∈ MulAut.innerSubgroup (LinearGroup n) := by
  let : Finite (LinearGroup n) :=
    Finite.of_injective (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective
  let I := MulAut.innerSubgroup (LinearGroup n)
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal I
  let e := innerEquiv (show 0 < n by omega)
  let Q := P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  obtain ⟨x,_,he⟩ := sylow_fixing_inner hn Q a (by
    rintro y ⟨z,hz,rfl⟩
    have hzS : (z : MulAut (LinearGroup n)) ∈ S := by
      rw [hP] at hz
      exact hz
    have h := hc z hzS
    apply MulAut.conj_injective_of_center_eq_bot (linear_center_eq_bot (by omega : 0 < n))
    have hz' : MulAut.conj (e.symm z) = z := congrArg Subtype.val (e.apply_symm_apply z)
    have he : MulAut.conj (a (e.symm z)) = a * MulAut.conj (e.symm z) * a⁻¹ := by
      ext x
      simp [MulAut.conj_apply]
    change MulAut.conj (a (e.symm z)) = MulAut.conj (e.symm z)
    rw [he,hz']
    exact mul_inv_eq_iff_eq_mul.mpr h.eq)
  rw [he]
  exact ⟨x,rfl⟩

/-- A Sylow-central automorphism has proper normal closure in degrees four and five. -/
theorem central_sylow_normalClosure_ne_top {n : ℕ} (hn : n = 4 ∨ n = 5)
    (S : Sylow 2 (MulAut (LinearGroup n))) (a : MulAut (LinearGroup n))
    (hc : ∀ s ∈ S, Commute a s) : normalClosure ({a} : Set _) ≠ ⊤ := by
  have hle : normalClosure ({a} : Set _) ≤ MulAut.innerSubgroup (LinearGroup n) :=
    normalClosure_le_normal (Set.singleton_subset_iff.mpr
      (central_sylow_automorphism_inner hn S a hc))
  intro he
  exact graph_not_inner hn (hle (he ▸ mem_top _))
end BinaryLinear.OuterCyclic
