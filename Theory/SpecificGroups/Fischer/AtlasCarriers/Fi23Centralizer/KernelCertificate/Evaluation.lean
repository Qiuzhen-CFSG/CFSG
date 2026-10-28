module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelCertificate.DecodedGenerators
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.FixedPointSetup
public import Theory.SpecificGroups.Fischer.AtlasCarriers.CycleNodup

/-!
# Checked evaluators for the Fi23 kernel certificate

Inverse cycle evaluation agrees with the actual ATLAS generators and candidate
word. This separates the mathematical interpretation of the decoded tables from
concrete fixed-letter computations. Those computations remain to be certified.
A second evaluator uses disjointness to look up the unique relevant cycle; its
soundness and application to the two actual generators are also proved here.

Source: ATLAS F23G1-p31671B0; the centralizer application is GLS3 Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.KernelCertificate

def cycleInv {α : Type*} [DecidableEq α] : List α → α → α
  | [], z => z
  | [_], z => z
  | a :: b :: l, z => cycleInv (b :: l) (if z = a then b else if z = b then a else z)

theorem cycleInv_eq {α : Type*} [DecidableEq α] (l : List α) (z : α) :
    cycleInv l z = l.formPerm⁻¹ z := by
  induction l generalizing z with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b l =>
      simp only [cycleInv, List.formPerm_cons_cons, mul_inv_rev,
        Equiv.Perm.mul_apply, Equiv.swap_inv, Equiv.swap_apply_def]
      exact ih _

def cyclesInv {α : Type*} [DecidableEq α] (ls : List (List α)) (z : α) : α :=
  ls.foldl (fun x l => cycleInv l x) z

theorem cyclesInv_eq {α : Type*} [DecidableEq α] (ls : List (List α)) (z : α) :
    cyclesInv ls z = (ls.map List.formPerm).prod⁻¹ z := by
  induction ls generalizing z with
  | nil => rfl
  | cons a l ih =>
    simpa only [cyclesInv, List.foldl_cons, List.map_cons, List.prod_cons,
      mul_inv_rev, Equiv.Perm.mul_apply, cycleInv_eq] using ih (cycleInv a z)

theorem cycleInv_of_notMem {α : Type*} [DecidableEq α]
    {l : List α} {x : α} (hx : x ∉ l) : cycleInv l x = x := by
  rw [cycleInv_eq]
  apply l.formPerm.injective
  simp [List.formPerm_apply_of_notMem hx]

theorem cyclesInv_of_notMem {α : Type*} [DecidableEq α]
    (ls : List (List α)) (x : α) (hx : x ∉ ls.flatten) : cyclesInv ls x = x := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    have h : x ∉ l ∧ x ∉ ls.flatten := by
      simpa only [List.flatten_cons, List.mem_append, not_or] using hx
    simpa only [cyclesInv, List.foldl_cons, cycleInv_of_notMem h.1] using ih h.2

def lookupInv {α : Type*} [DecidableEq α] : List (List α) → α → α
  | [], x => x
  | l :: ls, x => if x ∈ l then cycleInv l x else lookupInv ls x

theorem lookupInv_eq {α : Type*} [DecidableEq α]
    (ls : List (List α)) (hd : ls.flatten.Nodup) (x : α) :
    lookupInv ls x = cyclesInv ls x := by
  induction ls generalizing x with
  | nil => rfl
  | cons l ls ih =>
    obtain ⟨_, hls, hdisj⟩ := List.nodup_append'.mp (show (l ++ ls.flatten).Nodup from hd)
    by_cases hx : x ∈ l
    · have hy : cycleInv l x ∈ l := by
        rw [cycleInv_eq]
        apply List.mem_of_formPerm_apply_mem
        simpa using hx
      rw [lookupInv, if_pos hx]
      exact (cyclesInv_of_notMem ls (cycleInv l x)
        (fun h => List.disjoint_left.mp hdisj hy h)).symm
    · simpa only [lookupInv, if_neg hx, cyclesInv, List.foldl_cons,
        cycleInv_of_notMem hx] using ih hls x

def fastA (x : Fin 31671) := cyclesInv cyclesA x
def fastB (x : Fin 31671) := cyclesInv cyclesB x

theorem fastA_eq (x : Fin 31671) : fastA x = generatorA x := by
  rw [generatorA, AtlasCarriers.permutationFromCycleBlocks, cyclesA_spec]
  exact cyclesInv_eq _ _

theorem fastB_eq (x : Fin 31671) : fastB x = generatorB x := by
  rw [generatorB, AtlasCarriers.permutationFromCycleBlocks, cyclesB_spec]
  exact cyclesInv_eq _ _

def fastW (x : Fin 31671) :=
  fastA (fastB (fastB (fastA (fastB (fastB (fastA (fastB (fastA (fastB (fastA (fastB x)))))))))))

theorem fastW_eq (x : Fin 31671) : fastW x = inclusion word x := by
  simp only [fastW, fastA_eq, fastB_eq, word, map_mul, pow_succ,
    pow_zero, Equiv.Perm.mul_apply]
  rfl

def fastT (x : Fin 31671) := (fastW^[7]) x

theorem fastT_eq (x : Fin 31671) : fastT x = inclusion candidate x := by
  have h : fastW = inclusion word := funext fastW_eq
  simp only [fastT, h, candidate, map_pow, Equiv.Perm.coe_pow]

/-- With a disjointness certificate, lookup computes the literal first generator. -/
theorem generatorA_lookup (hd : cyclesA.flatten.Nodup) (x : Fin 31671) :
    lookupInv cyclesA x = generatorA x :=
  (lookupInv_eq _ hd x).trans (fastA_eq x)

/-- With a disjointness certificate, lookup computes the literal second generator. -/
theorem generatorB_lookup (hd : cyclesB.flatten.Nodup) (x : Fin 31671) :
    lookupInv cyclesB x = generatorB x :=
  (lookupInv_eq _ hd x).trans (fastB_eq x)

end Sporadic.Fischer.Fi23.CentralizerSection.KernelCertificate
