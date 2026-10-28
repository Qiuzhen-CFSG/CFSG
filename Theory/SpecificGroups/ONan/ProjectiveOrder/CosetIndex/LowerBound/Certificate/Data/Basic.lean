module

public import Theory.SpecificGroups.ONan.ProjectiveOrder.CosetIndex.LowerBound.Certificate.PackedData
/-!
# Checking the numerical orbit input

The untrusted producer is `LowerBound/source/GenerateOrbit.py`. Each leaf stores
its literal rows, change-of-basis coefficients, parent and generator. A Boolean
checker verifies canonical base-eight digits, the identity pivot minor, vanishing
before pivots, and decreasing parents. Its soundness is proved here. Balanced
interval lookup lets the kernel access any leaf in logarithmically many steps.
-/

@[expose] public section
namespace ONan.OrderCertificate.ReducedData
structure Pattern where
  pivot : Fin 8 → Fin 45
  increasing : StrictMono pivot
structure Node where
  row : Fin 8 → Nat
  coeff : Fin 8 → Nat
  pattern : Pattern
  parent : Nat
  letter : Bool

def digits : Nat → Nat → Bool
  | 0, a => a == 0
  | n+1, a => (a % 8 < 7) && digits n (a / 8)

theorem digits_sound (n a : Nat) (h : digits n a = true) : ValidOrbitRowCode n a := by
  induction n generalizing a with
  | zero =>
    simp only [digits, beq_iff_eq] at h
    subst a
    constructor
    · decide
    · intro j; exact Fin.elim0 j
  | succ n ih =>
    simp only [digits, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨ha, hd⟩ := ih (a / 8) h.2
    constructor
    · rw [Nat.div_lt_iff_lt_mul (by decide)] at ha
      simpa only [pow_succ] using ha
    · intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · simpa using h.1
      · simpa only [Nat.div_div_eq_div_mul, ← pow_succ', Fin.val_succ] using hd k

def all8 (f : Fin 8 → Bool) : Bool :=
  f 0 && f 1 && f 2 && f 3 && f 4 && f 5 && f 6 && f 7

theorem all8_sound {f : Fin 8 → Bool} (h : all8 f = true) (r : Fin 8) : f r = true := by
  simp only [all8, Bool.and_eq_true] at h
  fin_cases r <;> tauto

def check (i : Nat) (x : Node) : Bool :=
  (i == 0 || x.parent < i) && digits 45 (x.row 0) &&
  all8 (fun r => all8 (fun s =>
    (x.row r / 8 ^ (x.pattern.pivot s).val % 8 == if r == s then 1 else 0)) &&
    (x.row r % 8 ^ (x.pattern.pivot r).val == 0))

theorem check_parent {i : Nat} {x : Node} (h : check i x = true) (hi : i ≠ 0) :
    x.parent < i := by
  simp only [check, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact h.1.1.resolve_left hi

theorem check_valid {i : Nat} {x : Node} (h : check i x = true) :
    ValidOrbitRowCode 45 (x.row 0) := by
  simp only [check, Bool.and_eq_true] at h
  exact digits_sound _ _ h.1.2

theorem check_reduced {i : Nat} {x : Node} (h : check i x = true) :
    Matrix.IsReducedRowBasis (fun r => decodeOrbitRow (x.row r)) x.pattern.pivot := by
  simp only [check, Bool.and_eq_true] at h
  have hr := all8_sound h.2
  constructor
  · exact x.pattern.increasing
  · intro r s
    have hrr := hr r
    simp only [Bool.and_eq_true] at hrr
    have h := all8_sound hrr.1 s
    simp only [beq_iff_eq] at h
    change ((x.row r / 8 ^ (x.pattern.pivot s).val % 8 : Nat) : ZMod 7) = _
    rw [h]
    by_cases he : r = s <;> simp [he]
  · intro r j hj
    have hrr := hr r
    simp only [Bool.and_eq_true] at hrr
    have hz := hrr.2
    simp only [beq_iff_eq] at hz
    have hd : 8 ^ (j.val + 1) ∣ x.row r :=
      (Nat.pow_dvd_pow 8 (by exact hj)).trans (Nat.dvd_of_mod_eq_zero hz)
    have he : 8 ∣ x.row r / 8 ^ j.val := by
      apply Nat.dvd_div_of_mul_dvd
      simpa only [pow_succ] using hd
    simp only [decodeOrbitRow, Nat.mod_eq_zero_of_dvd he, Nat.cast_zero]

def branch {α : Type} (cut : Nat) (a b : Nat → α) (i : Nat) : α :=
  if i < cut then a i else b i

def Checked (lo hi : Nat) (f : Nat → Node) : Prop :=
  ∀ i, lo ≤ i → i < hi → check i (f i) = true

theorem checked_of_fin {lo n : Nat} {f : Nat → Node}
    (h : ∀ i : Fin n, check (lo + i.val) (f (lo + i.val)) = true) : Checked lo (lo+n) f := by
  intro i hlo hhi
  have he : lo + (i - lo) = i := by omega
  simpa only [he] using h ⟨i - lo, by omega⟩

theorem checked_branch {lo mid hi : Nat} {f g : Nat → Node}
    (hf : Checked lo mid f) (hg : Checked mid hi g) :
    Checked lo hi (branch mid f g) := by
  intro i hlo hhi
  unfold branch
  split_ifs with h
  · exact hf i hlo h
  · exact hg i (by omega) hhi
end ONan.OrderCertificate.ReducedData
