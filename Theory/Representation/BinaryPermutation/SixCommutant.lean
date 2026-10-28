module
public import Theory.Representation.BinaryPermutationNaturalStructure
public import Theory.Representation.BinaryPermutation.Faithful

/-!
# The linear centralizer of the binary six-letter augmentation core

Two three-cycles fixing a pair constrain its image to be constant on the
complementary four letters. The three-term relation on the pairs in a
triangle makes that constant zero. An invertible commuting operator
therefore fixes the pair. The alternating-invariant subspace theorem then
makes it fix the entire core.

This is the rigidity input for centralizing the original moved module in
Aschbacher--Smith, combined manuscript (1 March 2004), the paragraph before
12.6.6, printed p.824; the invariant-subspace calculation is B.3.1.
-/

public section

open Representation BinaryPermutation Equiv
namespace BinaryPermutation.SixCommutant
private abbrev Ω := Fin 6
private def a : Perm Ω := swap 2 3 * swap 3 4
private def b : Perm Ω := swap 3 4 * swap 4 5
private def c : Perm Ω := swap 0 1 * swap 1 2
private def p : core Ω := ⟨![1,1,0,0,0,0], by rw [mem_core]; decide⟩
private theorem even : a ∈ alternatingGroup Ω ∧ b ∈ alternatingGroup Ω ∧
    c ∈ alternatingGroup Ω := by
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide
private theorem pair_ne : p ≠ 0 := by
  intro h
  have hh := congrArg (fun w : core Ω => w.val 0) h
  exact one_ne_zero hh
private theorem pair_fixed : coreRepresentation Ω a p = p ∧
    coreRepresentation Ω b p = p := by
  constructor <;> apply Subtype.ext <;> decide
private theorem pair_relation :
    p + coreRepresentation Ω c p + coreRepresentation Ω (c*c) p = 0 := by
  apply Subtype.ext
  decide
private theorem fixed_relation (w : core Ω)
    (ha : coreRepresentation Ω a w = w)
    (hb : coreRepresentation Ω b w = w)
    (hc : w + coreRepresentation Ω c w + coreRepresentation Ω (c*c) w = 0) :
    w = 0 ∨ w = p := by
  have h23 := congrArg (fun w : core Ω => w.val 3) ha
  have h34 := congrArg (fun w : core Ω => w.val 4) ha
  have h45 := congrArg (fun w : core Ω => w.val 5) hb
  change w.val 2 = w.val 3 at h23
  change w.val 3 = w.val 4 at h34
  change w.val 4 = w.val 5 at h45
  have h3 := congrArg (fun w : core Ω => w.val 3) hc
  change w.val 3 + w.val 3 + w.val 3 = 0 at h3
  have h3z : w.val 3 = 0 := by simpa only [CharTwo.add_self_eq_zero, zero_add] using h3
  have h2z := h23.trans h3z
  have h4z := h34.symm.trans h3z
  have h5z := h45.symm.trans h4z
  have hsum := w.property
  change ∑ i : Fin 6, w.val i = 0 at hsum
  simp only [Fin.sum_univ_succ] at hsum
  change w.val 0 + (w.val 1 + (w.val 2 + (w.val 3 + (w.val 4 + (w.val 5 + 0))))) = 0 at hsum
  rw [h2z,h3z,h4z,h5z] at hsum
  have h01 : w.val 0 = w.val 1 := by
    simpa only [add_zero, CharTwo.add_eq_zero] using hsum
  have hcases : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  rcases hcases (w.val 0) with hz | ho
  · left; apply Subtype.ext; funext i; fin_cases i <;> simp_all
  · right; apply Subtype.ext; funext i; fin_cases i <;> simp_all [p]

/-- Every invertible operator commuting with the A₆ augmentation action is the identity. -/
theorem commuting_eq_refl (f : core (Fin 6) ≃ₗ[ZMod 2] core (Fin 6))
    (hf : ∀ g : alternatingGroup (Fin 6), ∀ x,
      f (coreRepresentation (Fin 6) g.val x) =
        coreRepresentation (Fin 6) g.val (f x)) : f = LinearEquiv.refl _ _ := by
  have hp : f p = p := by
    apply (fixed_relation (f p) ?_ ?_ ?_).resolve_left
    · exact fun h => pair_ne (f.injective (h.trans f.map_zero.symm))
    · exact (hf ⟨a,even.1⟩ p).symm.trans (congrArg f pair_fixed.1)
    · exact (hf ⟨b,even.2.1⟩ p).symm.trans (congrArg f pair_fixed.2)
    · have h := congrArg f pair_relation
      rw [map_add,map_add,hf ⟨c,even.2.2⟩,hf ⟨c*c,mul_mem even.2.2 even.2.2⟩,map_zero] at h
      exact h
  let P : Submodule (ZMod 2) (core Ω) := LinearMap.ker (f.toLinearMap - LinearMap.id)
  let W := P.map (core Ω).subtype
  have hW : ∀ g : alternatingGroup Ω, ∀ w ∈ W, representation Ω g.val w ∈ W := by
    rintro g _ ⟨w,hw,rfl⟩
    refine ⟨coreRepresentation Ω g.val w,?_,rfl⟩
    change f w - w = 0 at hw
    change f (coreRepresentation Ω g.val w) - coreRepresentation Ω g.val w = 0
    rw [hf,sub_eq_zero.mp hw,sub_self]
  have hPW : p.val ∈ W := ⟨p,sub_eq_zero.mpr hp,rfl⟩
  have hcore : core Ω ≤ W :=
    (invariant_le_constants_or_core_le (by decide : 5 ≤ Fintype.card Ω) W hW).resolve_left (by
      intro h
      obtain ⟨t,ht⟩ := Submodule.mem_span_singleton.mp (h hPW)
      exact one_ne_zero ((congrFun ht.symm 0).trans (congrFun ht 2)))
  apply LinearEquiv.ext
  intro w
  obtain ⟨x,hx,he⟩ := hcore w.property
  have hxe : x = w := Subtype.ext he
  subst x
  exact sub_eq_zero.mp hx
/-- The same six-letter augmentation action is faithful. -/
theorem action_injective : Function.Injective (alternatingCoreRepresentation (Fin 6)) := by
  intro a b hab
  apply Subtype.ext
  apply naturalRepresentation_injective (Fin 6) (by decide : 5 ≤ Fintype.card (Fin 6))
  apply LinearMap.ext
  intro w
  obtain ⟨x,rfl⟩ := coreToNatural_surjective w
  rw [← coreToNatural_equivariant, ← coreToNatural_equivariant]
  exact congrArg (coreToNatural (Fin 6)) (DFunLike.congr_fun hab x)
end BinaryPermutation.SixCommutant
