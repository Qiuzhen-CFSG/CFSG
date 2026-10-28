module

public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.Representatives
public import Theory.SpecificGroups.Tits.Atlas1600OrderData
import Mathlib.Tactic.FinCases

/-!
# Executable words and point checks for the five-overgroup certificates

A bijective base-four encoding stores words in two candidate generators and
their inverses. Nodes encode a fixed double-coset label and a right subgroup
word; transitions encode a target node and a left subgroup word. The checker
compares the resulting permutations at points 0, 1, 2. Its soundness is proved
separately in `Base`, keeping the large order proof out of finite computations.
Source: primary ATLAS Tits max4/max8 programs and the shared representatives.
-/

namespace Tits.MinimumIndexFiveOvergroups.DoubleCosetCertificate
open Theory.GroupTheory Atlas1600OrderCertificate

@[expose] public def decode : Nat → List (Fin 4)
  | 0 => []
  | n + 1 => ⟨n % 4, Nat.mod_lt _ (by decide)⟩ :: decode (n / 4)
termination_by n => n

@[expose] public def gen (pair : Atlas1600Group × Atlas1600Group) : Fin 4 → Atlas1600Group :=
  ![pair.1, pair.2, pair.1⁻¹, pair.2⁻¹]

@[expose] public def value (pair : Atlas1600Group × Atlas1600Group) (n : Nat) : Atlas1600Group :=
  ((decode n).map (gen pair)).prod

public theorem value_mem (pair : Atlas1600Group × Atlas1600Group) (n : Nat) :
    value pair n ∈ Subgroup.closure ({pair.1, pair.2} : Set Atlas1600Group) := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  have h0 : pair.1 ∈ Subgroup.closure ({pair.1, pair.2} : Set Atlas1600Group) :=
    Subgroup.subset_closure (by simp)
  have h1 : pair.2 ∈ Subgroup.closure ({pair.1, pair.2} : Set Atlas1600Group) :=
    Subgroup.subset_closure (by simp)
  fin_cases i
  · exact h0
  · exact h1
  · exact Subgroup.inv_mem _ h0
  · exact Subgroup.inv_mem _ h1

@[expose] public def packedLetter : Fin 4 → Equiv.Perm (Fin 1600) :=
  ![L0G0, L0G1, L0G0⁻¹, L0G1⁻¹]

public theorem packedLetter_spec (i : Fin 4) : packedLetter i = (letter i).val := by
  fin_cases i <;> simp only [packedLetter, letter, L0G0_eq_atlas, L0G1_eq_atlas] <;> rfl

public theorem packedWord_spec (w : List (Fin 4)) :
    (w.map packedLetter).prod = ((w.map letter).prod).val := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change packedLetter i * (w.map packedLetter).prod =
      (letter i).val * ((w.map letter).prod).val
    rw [packedLetter_spec, ih]

@[expose] public def point (data : Nat) (p : Fin 1600) : Fin 1600 :=
  ⟨(data >>> (11 * p.val)) % 2048 % 1600, Nat.mod_lt _ (by decide)⟩

@[expose] public def fastValue (maps : Fin 4 → Fin 1600 → Fin 1600)
    (c : Nat) (p : Fin 1600) : Fin 1600 :=
  (decode c).foldr (fun i q => maps i q) p

public theorem fastValue_spec (pair : Atlas1600Group × Atlas1600Group)
    (maps : Fin 4 → Fin 1600 → Fin 1600)
    (h : ∀ i p, maps i p = (gen pair i).val p) (c : Nat) (p : Fin 1600) :
    fastValue maps c p = (value pair c).val p := by
  unfold fastValue value
  generalize decode c = w
  induction w generalizing p with
  | nil => rfl
  | cons i w ih =>
    change maps i (w.foldr (fun i q => maps i q) p) =
      (gen pair i).val (((w.map (gen pair)).prod).val p)
    rw [ih, h]

@[expose] public def label {n : Nat} [NeZero n] (c : Nat) : Fin n :=
  ⟨c % 32 % n, Nat.mod_lt _ (NeZero.pos n)⟩

@[expose] public def target {m : Nat} [NeZero m] (c : Nat) : Fin m :=
  ⟨c % 32768 % m, Nat.mod_lt _ (NeZero.pos m)⟩

@[expose] public def nodeValue {n : Nat} [NeZero n]
    (pair : Atlas1600Group × Atlas1600Group) (reps : Fin n → Atlas1600Group)
    (c : Nat) : Atlas1600Group := reps (label c) * value pair (c / 32)

@[expose] public def fastNode {n : Nat} [NeZero n]
    (maps : Fin 4 → Fin 1600 → Fin 1600) (reps : Fin n → Fin 1600 → Fin 1600)
    (c : Nat) (p : Fin 1600) : Fin 1600 := reps (label c) (fastValue maps (c / 32) p)

@[expose] public def fastLetter (g : Fin 2) : Fin 1600 → Fin 1600 :=
  ![L0G0Map, L0G1Map] g

public theorem fastLetter_spec (g : Fin 2) (p : Fin 1600) :
    fastLetter g p = (letter g.castSucc.castSucc).val p := by
  have h0 : L0G0Map p = atlas1600A p := congrArg (fun q : Equiv.Perm (Fin 1600) => q p) L0G0_eq_atlas
  have h1 : L0G1Map p = atlas1600B p := congrArg (fun q : Equiv.Perm (Fin 1600) => q p) L0G1_eq_atlas
  fin_cases g
  · exact h0
  · exact h1

@[expose] public def test {n m : Nat} [NeZero n] [NeZero m]
    (maps : Fin 4 → Fin 1600 → Fin 1600) (reps : Fin n → Fin 1600 → Fin 1600)
    (nodes : Fin m → Nat) (steps : Fin m → Fin 2 → Nat) (r : Fin m) (g : Fin 2) : Bool :=
  let c := steps r g
  let lhs := fun p => fastNode maps reps (nodes r) (fastLetter g p)
  let rhs := fun p => fastValue maps (c / 32768) (fastNode maps reps (nodes (target c)) p)
  lhs 0 == rhs 0 && lhs 1 == rhs 1 && lhs 2 == rhs 2

end Tits.MinimumIndexFiveOvergroups.DoubleCosetCertificate
