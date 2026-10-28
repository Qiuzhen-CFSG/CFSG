module

public import Theory.SpecificGroups.PSL3Two.Automorphisms
public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups
public import Theory.GroupAction.ExtendingSubgroupAutomorphisms
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Sylow stabilizers for the external binary linear-three action

The upper triangular Sylow subgroup of PSL₃(2) is self-normalizing.
The Bruhat decomposition reduces this to six permutation matrices, tested
on two explicit upper triangular generators. Conjugacy gives the result
for every Sylow two-subgroup. Its stabilizer in the full automorphism
group is a two-group: the inner kernel is the Sylow subgroup itself,
and the outer quotient has order two.

These are the concrete model facts used for the dichotomy in
Aschbacher–Smith 13.8.21(1), combined manuscript of 1 March 2004,
printed p.956. The model is the actual matrix PSL₃(2).
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ExternalComponentAction.OrdinaryCentralization
open Matrix.PSL3Two

private theorem upper_test : ∀ j : Fin 6,
    let g := Bruhat.perm j;
    (g * Bruhat.upper 1 * g⁻¹).val 1 0 = 0 →
    (g * Bruhat.upper 1 * g⁻¹).val 2 0 = 0 →
    (g * Bruhat.upper 1 * g⁻¹).val 2 1 = 0 →
    (g * Bruhat.upper 4 * g⁻¹).val 1 0 = 0 →
    (g * Bruhat.upper 4 * g⁻¹).val 2 0 = 0 →
    (g * Bruhat.upper 4 * g⁻¹).val 2 1 = 0 →
    g.val 1 0 = 0 ∧ g.val 2 0 = 0 ∧ g.val 2 1 = 0 := by
  decide +kernel

/-- The literal upper triangular Sylow subgroup is self-normalizing. -/
theorem normalizer_borel : normalizer (borel : Set PSL) = borel := by
  apply le_antisymm _ borel.le_normalizer
  intro x hx
  obtain ⟨g, rfl⟩ := project_surjective x
  obtain ⟨i, j, k, he⟩ := Bruhat.decomposition g
  have hu (i : Fin 8) : project (Bruhat.upper i) ∈ normalizer (borel : Set PSL) :=
    borel.le_normalizer (mem_map_of_mem project (Bruhat.upper_mem i))
  have hj : project (Bruhat.perm j) ∈ normalizer (borel : Set PSL) := by
    rw [he, map_mul, map_mul] at hx
    exact ((normalizer (borel : Set PSL)).mul_mem_cancel_left (hu i)).mp
      (((normalizer (borel : Set PSL)).mul_mem_cancel_right (hu k)).mp hx)
  have hh (i : Fin 8) : project (Bruhat.perm j * Bruhat.upper i * (Bruhat.perm j)⁻¹) ∈ borel := by
    simpa only [map_mul, map_inv] using
      (mem_normalizer_iff.mp hj _).mp (mem_map_of_mem project (Bruhat.upper_mem i))
  have h1 := (mem_borel_project _).mp (hh 1)
  have h4 := (mem_borel_project _).mp (hh 4)
  have hjB : project (Bruhat.perm j) ∈ borel := (mem_borel_project _).mpr
    (upper_test j h1.1 h1.2.1 h1.2.2 h4.1 h4.2.1 h4.2.2)
  rw [he, map_mul, map_mul]
  exact borel.mul_mem (borel.mul_mem (mem_map_of_mem project (Bruhat.upper_mem i)) hjB)
    (mem_map_of_mem project (Bruhat.upper_mem k))

open scoped Pointwise

/-- Every Sylow two-subgroup of the matrix model is self-normalizing. -/
theorem normalizer_sylow (S : Sylow 2 PSL) :
    normalizer (S : Set PSL) = (S : Subgroup PSL) := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq PSL borelSylow S
  change normalizer (((borel.map (MulAut.conj g).toMonoidHom)) : Set PSL) = _
  rw [← map_normalizer_eq_of_bijective borel (MulAut.conj g).bijective, normalizer_borel]
  rfl

private noncomputable def innerEquiv : PSL ≃* MulAut.innerSubgroup PSL :=
  MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot Automorphisms.center_psl_eq_bot)

/-- The actual outer automorphism quotient is a two-group. -/
theorem outer_two : IsPGroup 2 (MulAut.Outer PSL) := by
  have hi : Nat.card (MulAut.innerSubgroup PSL) = 168 :=
    (Nat.card_congr innerEquiv.toEquiv).symm.trans card_PSL
  have hc := (MulAut.innerSubgroup PSL).card_mul_index
  rw [hi, Automorphisms.card_aut] at hc
  apply IsPGroup.of_card (n := 1)
  change (MulAut.innerSubgroup PSL).index = 2
  omega

/-- Automorphisms preserving a Sylow two-subgroup form a two-group. -/
theorem sylow_stabilizer_two (S : Sylow 2 PSL) :
    IsPGroup 2 (MulAction.stabilizer (MulAut PSL) (S : Subgroup PSL)) := by
  let P := MulAction.stabilizer (MulAut PSL) (S : Subgroup PSL)
  let q := (QuotientGroup.mk' (MulAut.innerSubgroup PSL)).comp P.subtype
  have hconj (s : S) : MulAut.conj s.val ∈ P := by
    change (S : Subgroup PSL).map (MulAut.conj s.val).toMonoidHom = S
    exact mem_normalizer_iff_map_conj_eq.mp ((S : Subgroup PSL).le_normalizer s.property)
  let f : S →* q.ker :=
    ((MulAut.conj.comp (S : Subgroup PSL).subtype).codRestrict P hconj).codRestrict q.ker
      (fun s => by
        change QuotientGroup.mk' (MulAut.innerSubgroup PSL) (MulAut.conj s.val) = 1
        exact (QuotientGroup.eq_one_iff _).mpr ⟨s.val, rfl⟩)
  have hf : Function.Surjective f := by
    intro a
    have ha : a.val.val ∈ MulAut.innerSubgroup PSL :=
      (QuotientGroup.eq_one_iff _).mp a.property
    obtain ⟨g, hg⟩ := ha
    have hgs : g ∈ (S : Subgroup PSL) := by
      rw [← normalizer_sylow S]
      apply mem_normalizer_iff_map_conj_eq.mpr
      change MulAut.conj g • (S : Subgroup PSL) = _
      rw [hg]
      exact a.val.property
    refine ⟨⟨g, hgs⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hg
  have hker : IsPGroup 2 q.ker := S.isPGroup'.of_surjective f hf
  have ht := (outer_two.to_subgroup ⊤).comap_of_ker_isPGroup q hker
  rw [comap_top] at ht
  exact ht.of_equiv topEquiv
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ExternalComponentAction.OrdinaryCentralization
