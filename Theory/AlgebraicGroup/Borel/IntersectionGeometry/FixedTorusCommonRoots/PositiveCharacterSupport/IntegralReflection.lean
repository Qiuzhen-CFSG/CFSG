module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas

/-!
# Sums in finite integral reflection systems

For a finite family of roots in a finite free integral lattice, integral
reflection functionals with diagonal value two suffice to construct a root
pairing on the span of those roots. Finiteness gives injectivity and reflection
compatibility of the restricted coroots; the evaluation pairing on this free
finite span is perfect. The construction follows the reflection-rigidity
argument in `Mathlib.LinearAlgebra.RootSystem.Basic`.

A root which is a sum of members of a root-addition-closed set belongs to that
set. Pair the sum with the target coroot and choose a summand with positive
pairing. Unless it is already the target, subtracting it leaves a root, so
induction on the number of summands applies. No reducedness or chosen base is
needed. This extends the sum argument of `RootData.RootAdditionClosure` to the
reflection data directly available from realized algebraic characters.

Source: Borel, *Linear Algebraic Groups*, IV, §14.7 (root systems and closed
sets of roots), especially the root-sum argument on printed p.188. The actual
character application is in the parent `PositiveCharacterSupport` module.
-/

open Set Submodule Module

namespace Theory.AlgebraicGroup.PositiveCharacterSupport

noncomputable section

variable {ι L : Type*} [AddCommGroup L]
  (r : ι ↪ L) (c : ι → Module.Dual ℤ L) (s : ι → ι → ι)
  (htwo : ∀ i, c i (r i) = 2)
  (href : ∀ i j, r (s i j) = r j - c i (r j) • r i)

private abbrev Span := Submodule.span ℤ (Set.range r)

private def spanRoot : ι ↪ Span r where
  toFun i := ⟨r i, Submodule.subset_span (Set.mem_range_self i)⟩
  inj' _ _ h := r.injective (congrArg Subtype.val h)

private def spanCoroot (i : ι) : Module.Dual ℤ (Span r) :=
  (c i).comp (Span r).subtype

include htwo in
private lemma span_two (i : ι) : spanCoroot r c i (spanRoot r i) = 2 := htwo i

include href in
private lemma span_ref (i j : ι) :
    spanRoot r (s i j) =
      spanRoot r j - spanCoroot r c i (spanRoot r j) • spanRoot r i := by
  apply Subtype.ext
  exact href i j

include href in
private lemma span_mapsTo (i : ι) :
    Set.MapsTo (Module.preReflection (spanRoot r i) (spanCoroot r c i))
      (Set.range (spanRoot r)) (Set.range (spanRoot r)) := by
  rintro _ ⟨j, rfl⟩
  exact ⟨s i j, span_ref r c s href i j⟩

private lemma span_spans : Submodule.span ℤ (Set.range (spanRoot r)) = ⊤ := by
  exact (Submodule.span_range_subtype_eq_top_iff (Span r)
    (fun i => Submodule.subset_span (Set.mem_range_self i))).mpr rfl

variable [Finite ι] [Module.Free ℤ L]

include htwo href in
private lemma spanCoroot_injective : Function.Injective (spanCoroot r c) := by
  let : IsAddTorsionFree (Span r) := .of_isTorsionFree ℤ (Span r)
  intro i j hij
  apply (spanRoot r).injective
  apply Module.eq_of_mapsTo_reflection_of_mem (Set.finite_range (spanRoot r))
    (span_two r c htwo i) (span_two r c htwo j)
  · rw [← hij]
    exact span_two r c htwo i
  · rw [hij]
    exact span_two r c htwo j
  · exact span_mapsTo r c s href i
  · exact span_mapsTo r c s href j
  · exact Set.mem_range_self j

include htwo href in
private lemma span_coref (i j : ι) :
    spanCoroot r c (s i j) = spanCoroot r c j -
      spanCoroot r c j (spanRoot r i) • spanCoroot r c i := by
  have hi := span_two r c htwo i
  have hj := span_two r c htwo j
  have href' := span_ref r c s href i j
  apply Module.Dual.eq_of_preReflection_mapsTo
    (Set.finite_range (spanRoot r)) (span_spans r)
    (span_two r c htwo (s i j)) (span_mapsTo r c s href (s i j))
  · rw [href']
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul,
      hi, hj, smul_eq_mul]
    ring
  · have hconj := Module.preReflection_preReflection (x := spanRoot r i)
      (y := spanRoot r j) (f := spanCoroot r c i) (spanCoroot r c j) hi
    change Module.preReflection
      (spanRoot r j - spanCoroot r c i (spanRoot r j) • spanRoot r i)
      (spanCoroot r c j - spanCoroot r c j (spanRoot r i) • spanCoroot r c i) = _
      at hconj
    rw [← href'] at hconj
    rw [hconj]
    exact (span_mapsTo r c s href i).comp
      ((span_mapsTo r c s href j).comp (span_mapsTo r c s href i))

variable [Module.Finite ℤ L]

private def pairing : RootPairing ι ℤ (Span r) (Module.Dual ℤ (Span r)) :=
  RootPairing.mk' (Module.Dual.eval ℤ (Span r))
    (spanRoot r) ⟨spanCoroot r c, spanCoroot_injective r c s htwo href⟩
    (span_two r c htwo) (span_mapsTo r c s href) (by
      rintro i _ ⟨j, rfl⟩
      exact ⟨s i j, span_coref r c s htwo href i j⟩)

end

private theorem mem_of_pairing_root_sum
    {ι M N : Type*} [Finite ι] [AddCommGroup M] [AddCommGroup N]
    (R : RootPairing ι ℤ M N) (S : Set ι)
    (hS : ∀ i ∈ S, ∀ j ∈ S, ∀ a, R.root a = R.root i + R.root j → a ∈ S)
    (roots : List ι) (a : ι) (hroots : ∀ i ∈ roots, i ∈ S)
    (hsum : R.root a = (roots.map R.root).sum) : a ∈ S := by
  classical
  let _ := Fintype.ofFinite ι
  induction hlen : roots.length using Nat.strong_induction_on generalizing roots a with
  | h n ih =>
      have hpairSum : (2 : ℤ) =
          (roots.map fun i => R.pairingIn ℤ i a).sum := by
        calc
          (2 : ℤ) = R.coroot' a (R.root a) := by simp
          _ = R.coroot' a ((roots.map R.root).sum) := congrArg (R.coroot' a) hsum
          _ = (roots.map fun i => R.pairingIn ℤ i a).sum := by
            rw [map_list_sum]
            simp [List.map_map, Function.comp_def, ← R.algebraMap_pairingIn ℤ]
      obtain ⟨i, hi, hpair⟩ : ∃ i ∈ roots, 0 < R.pairingIn ℤ i a := by
        by_contra! hall
        have hn : 0 ≤ (roots.map fun i => -R.pairingIn ℤ i a).sum :=
          List.sum_nonneg (by simpa using hall)
        have heq : (roots.map fun i => -R.pairingIn ℤ i a).sum =
            -(roots.map fun i => R.pairingIn ℤ i a).sum := by
          rw [List.sum_neg, List.map_map]
          rfl
        rw [heq, ← hpairSum] at hn
        omega
      by_cases hai : a = i
      · exact hai ▸ hroots i hi
      · have hpair' : 0 < R.pairingIn ℤ a i :=
          (R.zero_lt_pairingIn_iff (R.posRootForm ℤ) i a).mp hpair
        obtain ⟨b, hb⟩ := R.root_sub_root_mem_of_pairingIn_pos hpair' hai
        let shorter := roots.erase i
        have hshorterRoots : ∀ j ∈ shorter, j ∈ S := by
          intro j hj
          exact hroots j (List.mem_of_mem_erase hj)
        have herase : (roots.map R.root).sum =
            R.root i + (shorter.map R.root).sum := by
          simpa [shorter] using (List.perm_cons_erase hi |>.map R.root).sum_eq
        have hshorterSum : R.root b = (shorter.map R.root).sum := by
          rw [hb, hsum, herase]
          abel
        have hshorterLength : shorter.length < n := by
          rw [← hlen]
          simpa [shorter, List.length_erase_of_mem hi] using List.length_pos_of_mem hi
        have hbS : b ∈ S :=
          ih shorter.length hshorterLength shorter b hshorterRoots hshorterSum rfl
        exact hS b hbS i (hroots i hi) a (by rw [hb]; abel)

variable {ι L : Type*} [Finite ι] [AddCommGroup L]
  [Module.Free ℤ L] [Module.Finite ℤ L]

/-- Binary root-addition closure contains every root represented by a sum of
its members, for actual finite integral reflection data. -/
public theorem mem_of_root_sum
    (r : ι ↪ L) (c : ι → Module.Dual ℤ L) (s : ι → ι → ι)
    (htwo : ∀ i, c i (r i) = 2)
    (href : ∀ i j, r (s i j) = r j - c i (r j) • r i)
    (S : Set ι)
    (hS : ∀ i ∈ S, ∀ j ∈ S, ∀ a, r a = r i + r j → a ∈ S)
    (roots : List ι) (a : ι) (hroots : ∀ i ∈ roots, i ∈ S)
    (hsum : r a = (roots.map r).sum) : a ∈ S := by
  let R := pairing r c s htwo href
  refine mem_of_pairing_root_sum R S ?_ roots a hroots ?_
  · intro i hi j hj a ha
    apply hS i hi j hj a
    exact congrArg Subtype.val ha
  · apply Subtype.val_injective
    change (r a : L) = (Span r).subtype ((roots.map (spanRoot r)).sum)
    rw [map_list_sum, List.map_map]
    have heq : (Span r).subtype ∘ spanRoot r = r := by
      funext i
      rfl
    rw [heq]
    exact hsum

end Theory.AlgebraicGroup.PositiveCharacterSupport
