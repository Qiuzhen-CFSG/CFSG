module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoOne.FiniteConditions
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Arithmetic for the J₁ involution-orbit certificate

Four-bit digits encode the entries of a seven-by-seven matrix over `ZMod 11`.
Natural-number dot products, reduced modulo eleven at the end, certify equality
of two matrix products. The proof below identifies those computations with
ordinary matrix multiplication; the checker itself is evaluated in the kernel.

The arithmetic pattern follows
`Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Seven.MatrixCertificates.Checker`.
Its use here supports the `Out(J₁) = 1` entry of GLS3, Table 5.3f, for the actual
ATLAS matrices in `Theory.SpecificGroups.Janko1.Model.Basic`.
-/

namespace Janko1.OuterCertificate.InvolutionOrbit

@[expose] public def entry (a i j : ℕ) : ℕ := (a >>> (4 * (7 * i + j))) % 16

@[expose] public def decode (a : ℕ) : Mat := fun i j => (entry a i.val j.val : ℕ)

@[expose] public def dot (f g : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => dot f g n + f n * g n

@[expose] public def all (f : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n + 1 => all f n && f n

private theorem all_sound (f : ℕ → Bool) (n : ℕ) :
    all f n = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => simp [all]
  | succ n ih =>
    rw [all, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h, hn⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
      · exact h i hlt
      · exact hn
    · intro h
      exact ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h n (Nat.lt_succ_self n)⟩

private theorem dot_cast (f g : ℕ → ℕ) (n : ℕ) :
    (dot f g n : ZMod 11) = ∑ k : Fin n, (f k.val : ZMod 11) * (g k.val : ZMod 11) := by
  induction n with
  | zero => simp [dot]
  | succ n ih =>
    rw [dot, Nat.cast_add, Nat.cast_mul, ih, Fin.sum_univ_castSucc]
    rfl

/-- Compare every entry of the two products, using natural-number arithmetic. -/
@[expose] public def check (a b c d : ℕ) : Bool :=
  all (fun i => all (fun j =>
    dot (entry a i) (fun k => entry b k j) 7 % 11 ==
    dot (entry c i) (fun k => entry d k j) 7 % 11) 7) 7

/-- A successful check proves equality of the actual matrix products. -/
public theorem check_sound (a b c d : ℕ) (h : check a b c d = true) :
    decode a * decode b = decode c * decode d := by
  ext i j
  have hij := (all_sound _ _).mp ((all_sound _ _).mp h i.val i.isLt) j.val j.isLt
  have hc := congrArg (fun n : ℕ => (n : ZMod 11)) (beq_iff_eq.mp hij)
  simp only [ZMod.natCast_mod, dot_cast] at hc
  exact hc

/-- Blocks have 32 slots; the unused final slots wrap to the beginning. -/
@[expose] public def blockIndex (b : ℕ) (i : Fin 32) : Fin 1463 :=
  Fin.ofNat 1463 (32 * b + i.val)

/-- The block indexing covers every index of the published matrix family. -/
public theorem forall_of_blocks (P : Fin 1463 → Prop)
    (h : ∀ b : Fin 46, ∀ i : Fin 32, P (blockIndex b.val i)) : ∀ i, P i := by
  intro i
  let b : Fin 46 := ⟨i.val / 32, by have := i.isLt; omega⟩
  let r : Fin 32 := ⟨i.val % 32, Nat.mod_lt _ (by decide)⟩
  have hi : blockIndex b.val r = i := by
    apply Fin.ext
    change (32 * (i.val / 32) + i.val % 32) % 1463 = i.val
    have := i.isLt
    omega
  exact hi ▸ h b r

end Janko1.OuterCertificate.InvolutionOrbit
