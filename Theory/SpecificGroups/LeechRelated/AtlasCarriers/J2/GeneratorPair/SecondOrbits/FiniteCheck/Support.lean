module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.SecondOrbits.PointChecks

/-!
# Pointwise computation for the J₂ finite certificate

The Boolean checker evaluates the three rejection words as point maps. In the
acceptance case it compares all 100 points with the indicated partner table.
Its soundness theorem recovers exactly `WitnessValid`, so the finite checks
can use small Boolean computations without changing the mathematical tests.

Source: the ATLAS `J2G1-p100B0` word tests, with the inverse/right-action
convention documented in `SecondOrbits/source/README.md`.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.GeneratorPair.SecondOrbitCertificate.FiniteCheck

/-- Forward action of a normal form, without constructing intermediate equivalences. -/
def pointMap (i : Index) (x : Fin 100) : Fin 100 :=
  rep0Map i.1 (rep1Map i.2.1 (rep2Map i.2.2.1 (rep3Map i.2.2.2 x)))

/-- Inverse action, with the four factors in reverse order. -/
def inversePointMap (i : Index) (x : Fin 100) : Fin 100 :=
  rep3InvMap i.2.2.2 (rep2InvMap i.2.2.1 (rep1InvMap i.2.1 (rep0InvMap i.1 x)))

/-- Evaluate a rejection point or compare every point with the claimed partner. -/
def fastValid (i : Index) (code : Nat) : Bool :=
  let f := pointMap i
  let x := witnessPoint code
  match code % 4 with
  | 0 => f (f (f x)) != x
  | 1 => (fun x => tableAValues (f x))^[7] x != x
  | 2 => (fun x => tableAValues (f (tableAValues (inversePointMap i x))))^[12] x != x
  | _ => checkFin (fun x => f x == partnerTable (witnessConjugator code) (witnessInverse code) x)

theorem checkFin_true {n : Nat} {f : Fin n → Bool}
    (h : checkFin f = true) (i : Fin n) : f i = true := by
  have hi := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  simpa only [dif_pos i.isLt] using hi

private theorem pointMap_eq (i : Index) : pointMap i = normalForm i := rfl
private theorem inversePointMap_eq (i : Index) : inversePointMap i = (normalForm i)⁻¹ := rfl
private theorem a_values_eq : tableAValues = tableA := rfl

/-- The optimized computation proves the original witness proposition. -/
theorem fastValid_sound (i : Index) (code : Nat) (h : fastValid i code = true) :
    WitnessValid (normalForm i) code := by
  unfold fastValid at h
  rw [pointMap_eq, inversePointMap_eq, a_values_eq] at h
  unfold WitnessValid
  split <;> rename_i heq
  · rw [heq] at h
    simpa only [bne_iff_ne, Equiv.Perm.coe_pow, Function.iterate_succ_apply,
      Function.iterate_zero_apply] using h
  · rw [heq] at h
    simpa only [bne_iff_ne, Equiv.Perm.coe_pow, Equiv.Perm.coe_mul,
      Function.comp_def] using h
  · rw [heq] at h
    simpa only [bne_iff_ne, Equiv.Perm.coe_pow, Equiv.Perm.coe_mul,
      Function.comp_def] using h
  · simp only at h
    apply Equiv.ext
    intro x
    have hx := checkFin_true h x
    simpa only [beq_iff_eq] using hx

end Sporadic.LeechRelated.J2.GeneratorPair.SecondOrbitCertificate.FiniteCheck
