module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.CycleInvolutions
public import Theory.SpecificGroups.Fischer.AtlasCarriers.CycleNodup
/-!
# Certifying an inverse cycle product by its individual cycles

For disjoint cycles it suffices to check the candidate map on each cycle and
the fixed complement. A bit mask tests membership in the union of the cycles,
so the certificates avoid a quadratic scan of the full permutation product.
Used for the exact ATLAS F22G1-p3510B0 generators.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi22.KernelCertificate.CycleCheck
variable {n : Nat}

def mask : List (Fin n) → Nat
  | [] => 0
  | x :: xs => (2 ^ x.val) ||| mask xs

theorem mask_spec (xs : List (Fin n)) (x : Fin n) :
    (mask xs).testBit x.val = true ↔ x ∈ xs := by
  induction xs with
  | nil => simp [mask]
  | cons a xs ih =>
    simp only [mask, Nat.testBit_or, Bool.or_eq_true, List.mem_cons, ← ih]
    simp only [Nat.testBit_two_pow, decide_eq_true_eq]
    exact or_congr ⟨fun h => Fin.ext h.symm, fun h => congrArg Fin.val h.symm⟩ Iff.rfl

private theorem prod_fixed (cs : List (List (Fin n))) (x : Fin n)
    (hx : x ∉ cs.flatten) : (cs.map List.formPerm).prod x = x := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.flatten_cons, List.mem_append, not_or] at hx
    simp only [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply, ih hx.2,
      List.formPerm_apply_of_notMem hx.1]

private theorem prod_on_cycle (cs : List (List (Fin n)))
    (hd : cs.Pairwise List.Disjoint) (c : List (Fin n)) (hc : c ∈ cs)
    (x : Fin n) (hx : x ∈ c) : (cs.map List.formPerm).prod x = c.formPerm x := by
  induction cs with
  | nil => simp at hc
  | cons a cs ih =>
    obtain ⟨ha, hd⟩ := List.pairwise_cons.mp hd
    rcases List.mem_cons.mp hc with rfl | hc
    · rw [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply, prod_fixed]
      intro hm
      obtain ⟨c, hc, hx'⟩ := List.mem_flatten.mp hm
      exact ha c hc hx hx'
    · rw [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply, ih hd hc]
      apply List.formPerm_apply_of_notMem
      intro hm
      exact ha c hc hm (c.formPerm_apply_mem_of_mem hx)

/-- Certifying each cycle and the fixed complement determines the inverse product. -/
theorem inverse_prod_eq (cs : List (List (Fin n))) (f : Fin n → Fin n)
    (hd : cs.flatten.Nodup)
    (hcycle : ∀ c ∈ cs, ∀ x ∈ c, c.formPerm (f x) = x)
    (hfix : ∀ x, (mask cs.flatten).testBit x.val = false → f x = x)
    (x : Fin n) : (cs.map List.formPerm).prod⁻¹ x = f x := by
  apply (cs.map List.formPerm).prod.injective
  simp only [Equiv.Perm.inv_def, Equiv.apply_symm_apply]
  symm
  by_cases hx : x ∈ cs.flatten
  · obtain ⟨c, hc, hx⟩ := List.mem_flatten.mp hx
    have he := hcycle c hc x hx
    have hf : f x ∈ c := List.formPerm_mem_iff_mem.mp (he.symm ▸ hx)
    rw [prod_on_cycle cs (List.nodup_flatten.mp hd).2 c hc (f x) hf, he]
  · rw [hfix x (Bool.eq_false_iff.mpr (fun hh => hx ((mask_spec _ _).mp hh)))]
    exact prod_fixed cs x hx
end Sporadic.Fischer.Fi22.KernelCertificate.CycleCheck
