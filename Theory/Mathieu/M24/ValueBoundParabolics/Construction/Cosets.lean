module

public import Theory.Mathieu.M24.ValueBoundParabolics.Construction.Generators
public import Theory.Mathieu.M24.LocalGeometry.SylowNormalizer.Order

/-!
# Three-coset certificates for the native parabolics

For each extension, left multiplication by any of its five generators
permutes the three left cosets represented by 1, r, and r². Each transition
is checked as a permutation identity, with its Sylow factor given by a
positive word in the four marked generators. Positive closure induction
then bounds the order by 3·1024. Divisibility by 1024 and by 3 gives equality.

Source: Aschbacher–Smith, E.4.3(2), printed p.242 (PDF p.253).
-/

@[expose] public section
namespace Sporadic.Mathieu.M24ValueBoundParabolics.Construction
open M24LocalGeometry.SylowNormalizer
open M24LocalGeometry.SylowNormalizer.OrderEnumeration (evaluate evaluate_mem evaluate_apply)

set_option maxRecDepth 100000

private def cosetTarget : Fin 3 → Fin 5 → Fin 3 → Fin 3
  | 0 => ![![0,1,2],![0,2,1],![0,1,2],![0,2,1],![1,2,0]]
  | 1 => ![![0,2,1],![0,1,2],![0,2,1],![0,1,2],![1,2,0]]
  | 2 => ![![0,2,1],![0,1,2],![0,1,2],![0,1,2],![1,2,0]]

private def cosetWord : Fin 3 → Fin 5 → Fin 3 → List (Fin 4)
  | 0 => ![![[0],[0,3,0,3,0],[0,1,0,3,0,0]],![[1],[3,2,3,1,2],[2,3,1,2,3]],![[2],[2,1,2,1],[1,2,1]],![[3],[3],[3]],![[],[],[]]]
  | 1 => ![![[0],[2,0,3,2],[2,1,0,2]],![[1],[2,1,2],[2,1,2,1]],![[2],[2],[2]],![[3],[2,3,2],[3,2,3,2]],![[],[],[]]]
  | 2 => ![![[0],[2,0,2,0,0],[3,2,0,0,3,2,0]],![[1],[0,2,1,2,0,0,0],[1,0,2,1,2,0,0,0]],![[2],[3,1,2,3,1,0,0],[2,1,0,0,1,0,0]],![[3],[3,1],[0,2,0,0,3,2,0]],![[],[],[]]]

private def localPoint (i : Fin 3) : Fin 5 → Fin 24 → Fin 24 :=
  ![generatorPoint 0, generatorPoint 1, generatorPoint 2, generatorPoint 3, extraPoint i]

private theorem localGenerator_apply (i : Fin 3) (a : Fin 5) (x : Fin 24) :
    (localGenerator i a).val x = localPoint i a x := by
  fin_cases a
  · exact generatorPerm_apply 0 x
  · exact generatorPerm_apply 1 x
  · exact generatorPerm_apply 2 x
  · exact generatorPerm_apply 3 x
  · rfl

private theorem extra_pow_apply (i : Fin 3) (n : ℕ) (x : Fin 24) :
    ((extra i)^n).val x = (extraPoint i)^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ]
    change ((extra i)^n).val (extraPoint i x) = _
    rw [ih]
    rfl

private theorem coset_transition (i : Fin 3) (a : Fin 5) (j : Fin 3) :
    localGenerator i a * extra i ^ j.val =
      extra i ^ (cosetTarget i a j).val * evaluate (cosetWord i a j) := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change (localGenerator i a).val ((extra i ^ j.val).val x) =
    (extra i ^ (cosetTarget i a j).val).val ((evaluate (cosetWord i a j)).val x)
  rw [localGenerator_apply, extra_pow_apply, extra_pow_apply, evaluate_apply]
  exact (by decide +kernel : ∀ i a j x,
    localPoint i a ((extraPoint i)^[j.val] x) =
    (extraPoint i)^[(cosetTarget i a j).val] (evaluatePoint (cosetWord i a j) x)) i a j x

/-- Each native overgroup is covered by the three displayed Sylow cosets. -/
theorem parabolic_coset_cover (i : Fin 3) (g : parabolic i) :
    ∃ j : Fin 3, ∃ s : candidate, (g : M24) = extra i ^ j.val * s := by
  have hg : (g : M24) ∈ Submonoid.closure (Set.range (localGenerator i)) := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    exact g.property
  refine Submonoid.closure_induction_left
    (motive := fun y _ => ∃ j : Fin 3, ∃ s : candidate, y = extra i ^ j.val * s)
    ?_ ?_ hg
  · exact ⟨0, 1, by simp⟩
  · intro a ha y _ ih
    obtain ⟨a, rfl⟩ := ha
    obtain ⟨j, s, rfl⟩ := ih
    refine ⟨cosetTarget i a j,
      ⟨evaluate (cosetWord i a j), evaluate_mem _⟩ * s, ?_⟩
    change localGenerator i a * (extra i ^ j.val * (s : M24)) =
      extra i ^ (cosetTarget i a j).val * (evaluate (cosetWord i a j) * s)
    rw [← mul_assoc, coset_transition, mul_assoc]

private theorem parabolic_card_le (i : Fin 3) : Nat.card (parabolic i) ≤ 3072 := by
  let f : Fin 3 × candidate → parabolic i := fun js =>
    ⟨extra i ^ js.1.val * js.2,
      (parabolic i).mul_mem ((parabolic i).pow_mem (extra_mem_parabolic i) _)
        (candidate_le_parabolic i js.2.property)⟩
  have hf : Function.Surjective f := by
    intro g
    obtain ⟨j, s, h⟩ := parabolic_coset_cover i g
    exact ⟨(j,s), Subtype.ext h.symm⟩
  have h := Nat.card_le_card_of_surjective f hf
  simpa only [Nat.card_prod, Nat.card_fin, candidate_card] using h

theorem extra_order (i : Fin 3) : orderOf (extra i) = 3 := by
  apply orderOf_eq_prime
  · apply Subtype.ext
    apply Equiv.ext
    intro x
    change ((extra i)^3).val x = x
    rw [extra_pow_apply]
    exact (by decide +kernel : ∀ i x, (extraPoint i)^[3] x = x) i x
  · intro h
    have hp := congrArg (fun g : M24 => g.val) h
    have hn : ∀ i, extraPerm i ≠ 1 := by decide +kernel
    exact hn i hp

/-- Each of the three actual native overgroups has order 3072. -/
theorem parabolic_card (i : Fin 3) : Nat.card (parabolic i) = 3072 := by
  have h1024 : 1024 ∣ Nat.card (parabolic i) := by
    simpa only [candidate_card] using Subgroup.card_dvd_of_le (candidate_le_parabolic i)
  have h3 : 3 ∣ Nat.card (parabolic i) := by
    have h := orderOf_dvd_natCard (⟨extra i, extra_mem_parabolic i⟩ : parabolic i)
    simpa only [Subgroup.orderOf_mk, extra_order] using h
  have hd : 3072 ∣ Nat.card (parabolic i) :=
    (by decide +kernel : Nat.Coprime 3 1024).mul_dvd_of_dvd_of_dvd h3 h1024
  exact (parabolic_card_le i).antisymm (Nat.le_of_dvd Nat.card_pos hd)

end Sporadic.Mathieu.M24ValueBoundParabolics.Construction
