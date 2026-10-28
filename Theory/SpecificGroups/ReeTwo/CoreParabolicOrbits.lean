module

public import Theory.SpecificGroups.ReeTwo.CoreParabolicStructure
public import Theory.SpecificGroups.ReeTwo.CoreActionPacking

/-!
# Five-fixed points and involutions in the full Ree core

The order-five automorphism fixes precisely the four powers of the middle root.
Every involution outside the derived centralizer is conjugate to one of the
five images of root 3. The conjugators have zero binary character, so they
already belong to the characteristic index-two core.

The finite certificates enumerate the 1024 independent root coordinates.
For each of the 80 relevant involutions the two short tables supply a core
conjugator and a power of the specified five-action. Lean's kernel checks
all the multiplication identities, including the zero-character assertion.
The fixed-point certificate uses the verified packed action from
`CoreActionPacking`; no external computation is trusted.

Source: the verified root relations of Shinoda (1975), (2.3), pp.81–83;
compare Aschbacher (1982), Section 3, especially (3.2.7) and (3.2.11).
Ambient Ree/Tits identifications remain separate obligations.
-/

@[expose] public section
namespace ReeTwo.Core
open CensusPacked

private def involutionConjugator (n : Nat) : Nat :=
  match n with
  | 1 => 0
  | 16 => 0
  | 29 => 7
  | 33 => 6
  | 55 => 11
  | 59 => 10
  | 65 => 12
  | 80 => 7
  | 91 => 44
  | 97 => 10
  | 119 => 12
  | 125 => 1
  | 129 => 284
  | 144 => 6
  | 151 => 45
  | 155 => 11
  | 157 => 27
  | 161 => 26
  | 193 => 16
  | 208 => 1
  | 215 => 42
  | 225 => 278
  | 251 => 45
  | 253 => 32
  | 272 => 12
  | 279 => 22
  | 283 => 39
  | 317 => 45
  | 336 => 43
  | 343 => 17
  | 349 => 22
  | 379 => 26
  | 400 => 10
  | 439 => 16
  | 443 => 6
  | 445 => 44
  | 464 => 45
  | 475 => 0
  | 477 => 23
  | 503 => 23
  | 513 => 256
  | 528 => 32
  | 541 => 26
  | 545 => 262
  | 567 => 43
  | 571 => 17
  | 577 => 268
  | 592 => 39
  | 603 => 12
  | 609 => 266
  | 631 => 44
  | 637 => 33
  | 641 => 28
  | 656 => 38
  | 663 => 13
  | 667 => 16
  | 669 => 6
  | 673 => 282
  | 705 => 272
  | 720 => 33
  | 727 => 10
  | 737 => 22
  | 763 => 13
  | 765 => 0
  | 784 => 44
  | 791 => 1
  | 795 => 7
  | 829 => 13
  | 848 => 11
  | 855 => 6
  | 861 => 11
  | 891 => 1
  | 912 => 42
  | 951 => 7
  | 955 => 38
  | 957 => 12
  | 976 => 13
  | 987 => 27
  | 989 => 10
  | 1015 => 0
  | _ => 0

private def involutionPower (n : Nat) : Fin 5 :=
  match n with
  | 16 => 1
  | 29 => 2
  | 55 => 4
  | 59 => 3
  | 80 => 1
  | 91 => 3
  | 119 => 4
  | 125 => 2
  | 144 => 1
  | 151 => 4
  | 155 => 3
  | 157 => 2
  | 208 => 1
  | 215 => 4
  | 251 => 3
  | 253 => 2
  | 272 => 1
  | 279 => 4
  | 283 => 3
  | 317 => 2
  | 336 => 1
  | 343 => 4
  | 349 => 2
  | 379 => 3
  | 400 => 1
  | 439 => 4
  | 443 => 3
  | 445 => 2
  | 464 => 1
  | 475 => 3
  | 477 => 2
  | 503 => 4
  | 528 => 1
  | 541 => 2
  | 567 => 4
  | 571 => 3
  | 592 => 1
  | 603 => 3
  | 631 => 4
  | 637 => 2
  | 656 => 1
  | 663 => 4
  | 667 => 3
  | 669 => 2
  | 720 => 1
  | 727 => 4
  | 763 => 3
  | 765 => 2
  | 784 => 1
  | 791 => 4
  | 795 => 3
  | 829 => 2
  | 848 => 1
  | 855 => 4
  | 861 => 2
  | 891 => 3
  | 912 => 1
  | 951 => 4
  | 955 => 3
  | 957 => 2
  | 976 => 1
  | 987 => 3
  | 989 => 2
  | 1015 => 4
  | _ => 0

private def involutionOrbit (i : Fin 5) : Core :=
  decode (![1, 16, 765, 475, 1015] i)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem involutionOrbit_eq : ∀ i : Fin 5,
    involutionOrbit i = (c ^ i.val) (root 0) := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem involution_certificate : ∀ n : Fin 1024,
    decode n.val * decode n.val = 1 →
    ¬ ((decode n.val).b0 = 0 ∧ (decode n.val).b1 = 0 ∧
      (decode n.val).b3 = 0 ∧ (decode n.val).b4 = 0) →
    ((decode (involutionConjugator n.val)).b1 +
      (decode (involutionConjugator n.val)).b2 +
      (decode (involutionConjugator n.val)).b3 = 0) ∧
    decode (involutionConjugator n.val) * involutionOrbit (involutionPower n.val) *
      (decode (involutionConjugator n.val))⁻¹ = decode n.val := by
  decide +kernel

/-- Each involution outside the derived centralizer has an explicit conjugate root form. -/
theorem involution_eq_conjugate_five_root (x : Core) (hx : x ^ 2 = 1)
    (hf : x ∉ Subgroup.centralizer (commutator Core : Set Core)) :
    ∃ h : Core, ∃ k : Fin 5, h.b1 + h.b2 + h.b3 = 0 ∧
      h * (c ^ k.val) (root 0) * h⁻¹ = x := by
  have hs : decode (code x) * decode (code x) = 1 := by
    simpa only [decode_code, pow_two] using hx
  have hn : ¬ ((decode (code x)).b0 = 0 ∧ (decode (code x)).b1 = 0 ∧
      (decode (code x)).b3 = 0 ∧ (decode (code x)).b4 = 0) := by
    simpa only [decode_code, ← mem_centralizer_derived_iff] using hf
  have h := involution_certificate ⟨code x, code_lt x⟩ hs hn
  simp only [involutionOrbit_eq, decode_code] at h
  exact ⟨_, _, h⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem fixed_certificate : ∀ n : Fin 1024,
    cAct n.val = n.val → n.val = 0 ∨ n.val = 4 ∨ n.val = 512 ∨ n.val = 516 := by
  decide +kernel

/-- The fixed points of the specified cyclic-five action form the middle-root cyclic group. -/
theorem fixed_c_iff_mem_zpowers (x : Core) :
    c x = x ↔ x ∈ Subgroup.zpowers (root 2) := by
  constructor
  · intro hx
    have h : cAct (code x) = code x := by rw [cAct_code, hx]
    have hc := fixed_certificate ⟨code x, code_lt x⟩ h
    change code x = 0 ∨ code x = 4 ∨ code x = 512 ∨ code x = 516 at hc
    have hd := decode_code x
    rcases hc with hc | hc | hc | hc
    · rw [hc] at hd
      have he : decode 0 = 1 := by decide +kernel
      rw [← hd, he]
      exact Subgroup.one_mem _
    · rw [hc] at hd
      have he : decode 4 = root 2 := by decide +kernel
      rw [← hd, he]
      exact Subgroup.mem_zpowers _
    · rw [hc] at hd
      have he : decode 512 = root 2 ^ 2 := by decide +kernel
      rw [← hd, he]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
    · rw [hc] at hd
      have he : decode 516 = (root 2)⁻¹ := by decide +kernel
      rw [← hd, he]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
  · intro hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have h : c (root 2) = root 2 := by decide +kernel
    rw [map_zpow, h]


end ReeTwo.Core
