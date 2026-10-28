module

public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.Orders
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.Q0
import Mathlib.Tactic.FinCases

/-!
# Detecting the centralizer of the core

Finite permutation certificates for the fixed word-generated J₃ two-local
candidates. The retained ATLAS action is on 6156 letters. Packed maps are
checked against words in the preceding generators; all transition identities
are checked by the Lean kernel on every letter. The generating Python script
is discovery and code generation only, and contributes no proof premise.

Source: GLS, volume 3, Table 5.3h, printed p.269; ATLAS J3G1-p6156B0.
-/

namespace Sporadic.Janko3.TwoLocal.CentralizerCertificate
open Theory.GroupTheory OrderCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option Elab.async false

public abbrev CIndex := Fin 16 × Fin 5 × Fin 2 × Fin 3 × Fin 2 × Fin 2

@[expose] public def CRep (r : CIndex) : Equiv.Perm (Fin 6156) :=
  C0Rep r.1 * (C1Rep r.2.1 * (C2Rep r.2.2.1 *
    (C3Rep r.2.2.2.1 * (C4Rep r.2.2.2.2.1 * C5Rep r.2.2.2.2.2))))

public theorem CRep_complete (g : C0H) : ∃ r, (g : Equiv.Perm (Fin 6156)) = CRep r := by
  obtain ⟨r0, k1, h0⟩ := C0H_decompose g
  obtain ⟨r1, k2, h1⟩ := C1H_decompose k1
  obtain ⟨r2, k3, h2⟩ := C2H_decompose k2
  obtain ⟨r3, k4, h3⟩ := C3H_decompose k3
  obtain ⟨r4, k5, h4⟩ := C4H_decompose k4
  obtain ⟨r5, k6, h5⟩ := C5H_decompose k5
  have h6 : (k6 : Equiv.Perm (Fin 6156)) = 1 := by
    have h := k6.property
    simpa only [C6H, wordSubgroup_fin_zero_eq_bot, Subgroup.mem_bot] using h
  refine ⟨(r0, r1, r2, r3, r4, r5), ?_⟩
  rw [h0, h1, h2, h3, h4, h5, h6, mul_one]
  rfl

set_option synthInstance.maxSize 256 in
private theorem detection : ∀ r : CIndex,
    (∀ j : Fin 5, (CRep r * Q0Gen (j.castAdd 5)) 0 = (Q0Gen (j.castAdd 5) * CRep r) 0) →
    r = (0, 0, 0, 0, 0, 0) ∨ r = (0, 0, 1, 1, 0, 0) := by
  rintro ⟨r0, r1, r2, r3, r4, r5⟩
  revert r0 r1 r2 r3 r4 r5
  decide +kernel

private theorem last_rep_one : CRep (0, 0, 0, 0, 0, 0) = 1 := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem last_rep_involution : CRep (0, 0, 1, 1, 0, 0) = Q0G0 := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

/-- Centralizing the five generators forces membership in the order-two center. -/
public theorem core_centralizer_detection (g : C0H)
    (h : ∀ j : Fin 10, (g : Equiv.Perm (Fin 6156)) * Q0Gen j =
      Q0Gen j * (g : Equiv.Perm (Fin 6156))) :
    (g : Equiv.Perm (Fin 6156)) = 1 ∨ (g : Equiv.Perm (Fin 6156)) = Q0G0 := by
  obtain ⟨r, hr⟩ := CRep_complete g
  have hd := detection r (fun j => by
    have hh := congrArg (fun p : Equiv.Perm (Fin 6156) => p 0) (h (j.castAdd 5))
    simpa only [hr] using hh)
  rcases hd with rfl | rfl
  · exact Or.inl (hr.trans last_rep_one)
  · exact Or.inr (hr.trans last_rep_involution)

end Sporadic.Janko3.TwoLocal.CentralizerCertificate
