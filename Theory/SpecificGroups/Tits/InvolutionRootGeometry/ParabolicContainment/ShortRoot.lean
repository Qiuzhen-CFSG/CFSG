module

public import Theory.SpecificGroups.Tits.InvolutionRootGeometry.ParabolicContainment.ShortOrbit
public import Theory.SpecificGroups.Tits.InvolutionRootGeometry.ParabolicContainment.ShortCertificate
public import Theory.SpecificGroups.Tits.R1AmbientCosetCover
public import Theory.SpecificGroups.Tits.OuterOddSubgroups.OverlapCentralizers.FirstCover

/-!
# The short-root centralizer lies in the linear Tits parabolic

The certified R₁ cover and the five-coset first-parabolic normal form write
an arbitrary element as s v, with s in the Sylow subgroup. If s v centralizes
s₄, then v s₄ = (s⁻¹ s₄ s) v. The structural four-element Sylow orbit and
the complete two-point certificate force v to use only second-parabolic
generators. Hence both factors lie in the second parabolic.

All words and maps use the literal certified Atlas marking. Source:
Parrott (1972), pp.672,683--684; Aschbacher--Smith 16.1.4(1), p.1171.
-/

public section

open Subgroup Theory.GroupTheory.CosetEnumeration
namespace Tits.InvolutionRootGeometry.ParabolicContainment
open Atlas1600ParrottData ExceptionalParabolics OuterOddSubgroups.OverlapCentralizers

private theorem short_val_mul (a b : Atlas1600Group) : (a*b).val = a.val*b.val := rfl
private theorem short_val_inv (a : Atlas1600Group) : (a⁻¹).val = a.val⁻¹ := rfl

private theorem orbitPerm_eq (k : Fin 4) : Certificate.orbitPerm k = (shortOrbit k).val := by
  fin_cases k <;>
    simp [Certificate.orbitPerm, shortOrbit, orbitConjugator,
      short_val_mul, short_val_inv, atlas1600ParrottAssignment_val, permutation]

private theorem mapped_eval (w : Word ParrottGenerator) :
    parrottFiniteImageEquiv (eval parrottGenerator w) =
      eval atlas1600ParrottAssignment w := by
  simp only [eval, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  rintro ⟨a,b⟩ _
  cases b <;> simp [letterValue]

private theorem eval_val (w : Word ParrottGenerator) :
    (eval atlas1600ParrottAssignment w).val = eval permutation w := by
  change atlas1600Subgroup.subtype (eval atlas1600ParrottAssignment w) = _
  simp only [eval, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  rintro ⟨a,b⟩ _
  cases b
  · change (atlas1600ParrottAssignment a).val⁻¹ = _
    rw [atlas1600ParrottAssignment_val]
    rfl
  · exact atlas1600ParrottAssignment_val a

set_option maxRecDepth 30000 in
private theorem concrete_covers (x : ParrottGroup) :
    ∃ h : parrottR1Subgroup, ∃ i : Fin 1755,
      x = h.val * representative parrottGenerator R1Certificate.input (R1Certificate.index i) := by
  let C : ParrottR1CosetCover := {
    rep := fun i => representative parrottGenerator R1Certificate.input (R1Certificate.index i)
    initial := R1Certificate.initial
    initial_eq := by simp [representative, R1Certificate.initial_index, R1Certificate.model.zero]
    step := fun a => tablePermutation R1Certificate.table R1Certificate.inverse_table (a, true)
    transition := fun i a => by
      simpa only [Fact.Valid, Related, eval_singleton, letterValue, ↓reduceIte,
        tablePermutation, Equiv.coe_fn_mk] using R1Certificate.edges i a }
  exact C.covers x

private theorem sylow_coset_cover (x : Atlas1600Group) :
    ∃ (n : Fin 2048) (j : Fin 5) (i : ℕ),
      x = atlas1600SylowTwoNormalForm n * (firstRotation ^ j.val *
        eval atlas1600ParrottAssignment (R1Certificate.input.reps.getD i [])) := by
  obtain ⟨h, i, he⟩ := concrete_covers (parrottFiniteImageEquiv.symm x)
  have hxform : x = parrottFiniteImageEquiv h.val * parrottFiniteImageEquiv
      (representative parrottGenerator R1Certificate.input (R1Certificate.index i)) := by
    rw [← map_mul, ← he, MulEquiv.apply_symm_apply]
  have hh : parrottFiniteImageEquiv h.val ∈ first := by
    rw [← ReeLocalBlockOrders.first_map]
    exact mem_map_of_mem _ h.property
  obtain ⟨⟨n,j⟩, hnj⟩ := firstNormalForm_surjective ⟨parrottFiniteImageEquiv h.val, hh⟩
  have hnf := congrArg Subtype.val hnj
  change atlas1600SylowTwoNormalForm n * firstRotation ^ j.val =
    parrottFiniteImageEquiv h.val at hnf
  refine ⟨n, j, R1Certificate.index i, ?_⟩
  rw [hxform, ← hnf, representative, mapped_eval, mul_assoc]

private theorem generator_mem_second (a : ParrottGenerator) (ha : a ≠ .r1) :
    atlas1600ParrottAssignment a ∈ second := by
  by_cases h8 : a = .r8
  · subst a
    exact reflection_mem_second
  · apply sylow_le_second
    rw [S, atlas1600SylowTwoSubgroup_eq]
    apply subset_closure
    cases a <;> simp_all

private theorem inSecond_sound (w : Word ParrottGenerator) (j : Fin 5)
    (h : Certificate.inSecond w j = true) :
    firstRotation ^ j.val * eval atlas1600ParrottAssignment w ∈ second := by
  simp only [Certificate.inSecond, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, hw⟩
  simp only [Fin.val_zero, pow_zero, one_mul]
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨⟨a,b⟩, ha, rfl⟩ := List.mem_map.mp hx
  have ha1 : a ≠ .r1 := by simpa using List.all_eq_true.mp hw (a,b) ha
  have hm := generator_mem_second a ha1
  cases b <;> simp only [letterValue, Bool.false_eq_true, ↓reduceIte]
  · exact second.inv_mem hm
  · exact hm

theorem short_centralizer_le_second :
    centralizer {atlas1600ParrottAssignment .s4} ≤ second := by
  intro x hx
  obtain ⟨n, j, i, he⟩ := sylow_coset_cover x
  let s := atlas1600SylowTwoNormalForm n
  let v := firstRotation ^ j.val *
    eval atlas1600ParrottAssignment (R1Certificate.input.reps.getD i [])
  have hs : s ∈ S := atlas1600SylowTwoNormalForm_mem n
  obtain ⟨k, hk⟩ := sylow_conjugate_short s⁻¹ (S.inv_mem hs)
  have hc : v * atlas1600ParrottAssignment .s4 = shortOrbit k * v := by
    have hcomm := mem_centralizer_singleton_iff.mp hx
    rw [he] at hcomm
    change (s*v) * atlas1600ParrottAssignment .s4 =
      atlas1600ParrottAssignment .s4 * (s*v) at hcomm
    have h := congrArg (fun y => s⁻¹*y) hcomm
    rw [← hk]
    simpa only [inv_inv, mul_assoc, inv_mul_cancel_left] using h
  have hval := congrArg Subtype.val hc
  have hv : v.val = (s1Perm*r1Perm)^j.val *
      eval permutation (R1Certificate.input.reps.getD i []) := by
    change firstRotation.val ^ j.val * _ = _
    rw [eval_val]
    simp only [firstRotation, short_val_mul, atlas1600ParrottAssignment_val, permutation]
  have hp : Certificate.separates (R1Certificate.input.reps.getD i []) j k = false := by
    change v.val * (atlas1600ParrottAssignment .s4).val = (shortOrbit k).val * v.val at hval
    rw [atlas1600ParrottAssignment_val, ← orbitPerm_eq, hv] at hval
    have h0 := congrArg (fun p : Equiv.Perm (Fin 1600) => p 0) hval
    have h1 := congrArg (fun p : Equiv.Perm (Fin 1600) => p 1) hval
    simp only [permutation, Equiv.Perm.mul_apply] at h0 h1
    simp only [Certificate.separates_eq, Equiv.Perm.mul_apply, h0, h1, bne_self_eq_false, Bool.or_self]
  have ht := Certificate.representative_test i j
  simp only [Bool.or_eq_true] at ht
  rcases ht with hin | hout
  · rw [he]
    exact second.mul_mem (sylow_le_second hs) (inSecond_sound _ _ hin)
  · have hf := List.all_eq_true.mp hout k (List.mem_finRange k)
    rw [hp] at hf
    contradiction
end Tits.InvolutionRootGeometry.ParabolicContainment
