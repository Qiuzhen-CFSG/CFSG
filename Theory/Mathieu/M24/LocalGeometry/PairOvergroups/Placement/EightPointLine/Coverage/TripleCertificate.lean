module

public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Placement.EightPointLine.TripleData
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Fin

/-!
# Coordinate certificates for conjugation of pairs of triples

For each adjacent transposition and each listed pair, the image triples are
another listed pair, up to reordering and exchange. The witness tables are
reproduced by `source/generate_tables.py`; the kernel checks every coordinate.
Keeping this finite calculation separate avoids importing group theory into
its verification. `Adjacent.lean` turns the coordinate identities into
conjugacy of the generated subgroups.

Source application: Aschbacher–Smith, proof of 1.3.4, printed p.511 (PDF p.528);
GLS3, Table 5.3e.
-/

namespace Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement.EightPoint.Coverage

-- A Boolean loop keeps the predicate fixed as the bound decreases. Its
-- correctness proof permits kernel-checked finite certificates without the
-- quadratic predicate rebuilding of the default bounded quantifier.
private def boundedAll {n : ℕ} (f : Fin n → Bool) : (m : ℕ) → m ≤ n → Bool
  | 0, _ => true
  | m + 1, h => f ⟨m, Nat.lt_of_lt_of_le (Nat.lt_succ_self m) h⟩ &&
      boundedAll f m (Nat.le_trans (Nat.le_succ m) h)

private theorem boundedAll_correct {n : ℕ} (f : Fin n → Bool) (m : ℕ) (hm : m ≤ n) :
    boundedAll f m hm = true ↔ ∀ j : Fin n, j.val < m → f j = true := by
  induction m with
  | zero => simp [boundedAll]
  | succ m ih =>
    rw [boundedAll, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨htop, hbelow⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
      · exact hbelow j hlt
      · have h : j = ⟨m, Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hm⟩ := Fin.ext heq
        simpa only [h] using htop
    · intro h
      exact ⟨h _ (Nat.lt_succ_self m), fun j hj => h j (Nat.lt_succ_of_lt hj)⟩

private instance (priority := 2000) finiteForall {n : ℕ}
    (P : Fin n → Prop) [DecidablePred P] : Decidable (∀ i, P i) :=
  decidable_of_iff (boundedAll (fun i => decide (P i)) n (Nat.le_refl n) = true)
    ⟨fun h i => of_decide_eq_true ((boundedAll_correct _ _ _).mp h i i.isLt),
      fun h => (boundedAll_correct _ _ _).mpr (fun i _ => decide_eq_true (h i))⟩

@[expose] public def tripleOrder (q : Fin 6) : Fin 3 → Fin 3 :=
  ![![0,1,2], ![1,2,0], ![2,0,1], ![2,1,0], ![1,0,2], ![0,2,1]] q
@[expose] public def genTriple (i : Fin 280) (k : Fin 2) (n : Fin 3) : Fin 8 :=
  triplePair i ⟨3 * k.val + n.val, by omega⟩

private def fastTriple (i : Fin 280) : Fin 6 → Fin 8 :=
  if i.val < 140 then
    if i.val < 70 then
      if i.val < 35 then
        if i.val < 17 then
          if i.val < 8 then
            if i.val < 4 then
              if i.val < 2 then
                if i.val < 1 then
                  ![0, 1, 2, 3, 4, 5]
                else
                  ![0, 1, 2, 3, 4, 6]
              else
                if i.val < 3 then
                  ![0, 1, 2, 3, 4, 7]
                else
                  ![0, 1, 2, 3, 5, 6]
            else
              if i.val < 6 then
                if i.val < 5 then
                  ![0, 1, 2, 3, 5, 7]
                else
                  ![0, 1, 2, 3, 6, 7]
              else
                if i.val < 7 then
                  ![0, 1, 2, 4, 5, 6]
                else
                  ![0, 1, 2, 4, 5, 7]
          else
            if i.val < 12 then
              if i.val < 10 then
                if i.val < 9 then
                  ![0, 1, 2, 4, 6, 7]
                else
                  ![0, 1, 2, 5, 6, 7]
              else
                if i.val < 11 then
                  ![0, 1, 3, 2, 4, 5]
                else
                  ![0, 1, 3, 2, 4, 6]
            else
              if i.val < 14 then
                if i.val < 13 then
                  ![0, 1, 3, 2, 4, 7]
                else
                  ![0, 1, 3, 2, 5, 6]
              else
                if i.val < 15 then
                  ![0, 1, 3, 2, 5, 7]
                else
                  if i.val < 16 then
                    ![0, 1, 3, 2, 6, 7]
                  else
                    ![0, 1, 3, 4, 5, 6]
        else
          if i.val < 26 then
            if i.val < 21 then
              if i.val < 19 then
                if i.val < 18 then
                  ![0, 1, 3, 4, 5, 7]
                else
                  ![0, 1, 3, 4, 6, 7]
              else
                if i.val < 20 then
                  ![0, 1, 3, 5, 6, 7]
                else
                  ![0, 1, 4, 2, 3, 5]
            else
              if i.val < 23 then
                if i.val < 22 then
                  ![0, 1, 4, 2, 3, 6]
                else
                  ![0, 1, 4, 2, 3, 7]
              else
                if i.val < 24 then
                  ![0, 1, 4, 2, 5, 6]
                else
                  if i.val < 25 then
                    ![0, 1, 4, 2, 5, 7]
                  else
                    ![0, 1, 4, 2, 6, 7]
          else
            if i.val < 30 then
              if i.val < 28 then
                if i.val < 27 then
                  ![0, 1, 4, 3, 5, 6]
                else
                  ![0, 1, 4, 3, 5, 7]
              else
                if i.val < 29 then
                  ![0, 1, 4, 3, 6, 7]
                else
                  ![0, 1, 4, 5, 6, 7]
            else
              if i.val < 32 then
                if i.val < 31 then
                  ![0, 1, 5, 2, 3, 4]
                else
                  ![0, 1, 5, 2, 3, 6]
              else
                if i.val < 33 then
                  ![0, 1, 5, 2, 3, 7]
                else
                  if i.val < 34 then
                    ![0, 1, 5, 2, 4, 6]
                  else
                    ![0, 1, 5, 2, 4, 7]
      else
        if i.val < 52 then
          if i.val < 43 then
            if i.val < 39 then
              if i.val < 37 then
                if i.val < 36 then
                  ![0, 1, 5, 2, 6, 7]
                else
                  ![0, 1, 5, 3, 4, 6]
              else
                if i.val < 38 then
                  ![0, 1, 5, 3, 4, 7]
                else
                  ![0, 1, 5, 3, 6, 7]
            else
              if i.val < 41 then
                if i.val < 40 then
                  ![0, 1, 5, 4, 6, 7]
                else
                  ![0, 1, 6, 2, 3, 4]
              else
                if i.val < 42 then
                  ![0, 1, 6, 2, 3, 5]
                else
                  ![0, 1, 6, 2, 3, 7]
          else
            if i.val < 47 then
              if i.val < 45 then
                if i.val < 44 then
                  ![0, 1, 6, 2, 4, 5]
                else
                  ![0, 1, 6, 2, 4, 7]
              else
                if i.val < 46 then
                  ![0, 1, 6, 2, 5, 7]
                else
                  ![0, 1, 6, 3, 4, 5]
            else
              if i.val < 49 then
                if i.val < 48 then
                  ![0, 1, 6, 3, 4, 7]
                else
                  ![0, 1, 6, 3, 5, 7]
              else
                if i.val < 50 then
                  ![0, 1, 6, 4, 5, 7]
                else
                  if i.val < 51 then
                    ![0, 1, 7, 2, 3, 4]
                  else
                    ![0, 1, 7, 2, 3, 5]
        else
          if i.val < 61 then
            if i.val < 56 then
              if i.val < 54 then
                if i.val < 53 then
                  ![0, 1, 7, 2, 3, 6]
                else
                  ![0, 1, 7, 2, 4, 5]
              else
                if i.val < 55 then
                  ![0, 1, 7, 2, 4, 6]
                else
                  ![0, 1, 7, 2, 5, 6]
            else
              if i.val < 58 then
                if i.val < 57 then
                  ![0, 1, 7, 3, 4, 5]
                else
                  ![0, 1, 7, 3, 4, 6]
              else
                if i.val < 59 then
                  ![0, 1, 7, 3, 5, 6]
                else
                  if i.val < 60 then
                    ![0, 1, 7, 4, 5, 6]
                  else
                    ![0, 2, 3, 1, 4, 5]
          else
            if i.val < 65 then
              if i.val < 63 then
                if i.val < 62 then
                  ![0, 2, 3, 1, 4, 6]
                else
                  ![0, 2, 3, 1, 4, 7]
              else
                if i.val < 64 then
                  ![0, 2, 3, 1, 5, 6]
                else
                  ![0, 2, 3, 1, 5, 7]
            else
              if i.val < 67 then
                if i.val < 66 then
                  ![0, 2, 3, 1, 6, 7]
                else
                  ![0, 2, 3, 4, 5, 6]
              else
                if i.val < 68 then
                  ![0, 2, 3, 4, 5, 7]
                else
                  if i.val < 69 then
                    ![0, 2, 3, 4, 6, 7]
                  else
                    ![0, 2, 3, 5, 6, 7]
    else
      if i.val < 105 then
        if i.val < 87 then
          if i.val < 78 then
            if i.val < 74 then
              if i.val < 72 then
                if i.val < 71 then
                  ![0, 2, 4, 1, 3, 5]
                else
                  ![0, 2, 4, 1, 3, 6]
              else
                if i.val < 73 then
                  ![0, 2, 4, 1, 3, 7]
                else
                  ![0, 2, 4, 1, 5, 6]
            else
              if i.val < 76 then
                if i.val < 75 then
                  ![0, 2, 4, 1, 5, 7]
                else
                  ![0, 2, 4, 1, 6, 7]
              else
                if i.val < 77 then
                  ![0, 2, 4, 3, 5, 6]
                else
                  ![0, 2, 4, 3, 5, 7]
          else
            if i.val < 82 then
              if i.val < 80 then
                if i.val < 79 then
                  ![0, 2, 4, 3, 6, 7]
                else
                  ![0, 2, 4, 5, 6, 7]
              else
                if i.val < 81 then
                  ![0, 2, 5, 1, 3, 4]
                else
                  ![0, 2, 5, 1, 3, 6]
            else
              if i.val < 84 then
                if i.val < 83 then
                  ![0, 2, 5, 1, 3, 7]
                else
                  ![0, 2, 5, 1, 4, 6]
              else
                if i.val < 85 then
                  ![0, 2, 5, 1, 4, 7]
                else
                  if i.val < 86 then
                    ![0, 2, 5, 1, 6, 7]
                  else
                    ![0, 2, 5, 3, 4, 6]
        else
          if i.val < 96 then
            if i.val < 91 then
              if i.val < 89 then
                if i.val < 88 then
                  ![0, 2, 5, 3, 4, 7]
                else
                  ![0, 2, 5, 3, 6, 7]
              else
                if i.val < 90 then
                  ![0, 2, 5, 4, 6, 7]
                else
                  ![0, 2, 6, 1, 3, 4]
            else
              if i.val < 93 then
                if i.val < 92 then
                  ![0, 2, 6, 1, 3, 5]
                else
                  ![0, 2, 6, 1, 3, 7]
              else
                if i.val < 94 then
                  ![0, 2, 6, 1, 4, 5]
                else
                  if i.val < 95 then
                    ![0, 2, 6, 1, 4, 7]
                  else
                    ![0, 2, 6, 1, 5, 7]
          else
            if i.val < 100 then
              if i.val < 98 then
                if i.val < 97 then
                  ![0, 2, 6, 3, 4, 5]
                else
                  ![0, 2, 6, 3, 4, 7]
              else
                if i.val < 99 then
                  ![0, 2, 6, 3, 5, 7]
                else
                  ![0, 2, 6, 4, 5, 7]
            else
              if i.val < 102 then
                if i.val < 101 then
                  ![0, 2, 7, 1, 3, 4]
                else
                  ![0, 2, 7, 1, 3, 5]
              else
                if i.val < 103 then
                  ![0, 2, 7, 1, 3, 6]
                else
                  if i.val < 104 then
                    ![0, 2, 7, 1, 4, 5]
                  else
                    ![0, 2, 7, 1, 4, 6]
      else
        if i.val < 122 then
          if i.val < 113 then
            if i.val < 109 then
              if i.val < 107 then
                if i.val < 106 then
                  ![0, 2, 7, 1, 5, 6]
                else
                  ![0, 2, 7, 3, 4, 5]
              else
                if i.val < 108 then
                  ![0, 2, 7, 3, 4, 6]
                else
                  ![0, 2, 7, 3, 5, 6]
            else
              if i.val < 111 then
                if i.val < 110 then
                  ![0, 2, 7, 4, 5, 6]
                else
                  ![0, 3, 4, 1, 2, 5]
              else
                if i.val < 112 then
                  ![0, 3, 4, 1, 2, 6]
                else
                  ![0, 3, 4, 1, 2, 7]
          else
            if i.val < 117 then
              if i.val < 115 then
                if i.val < 114 then
                  ![0, 3, 4, 1, 5, 6]
                else
                  ![0, 3, 4, 1, 5, 7]
              else
                if i.val < 116 then
                  ![0, 3, 4, 1, 6, 7]
                else
                  ![0, 3, 4, 2, 5, 6]
            else
              if i.val < 119 then
                if i.val < 118 then
                  ![0, 3, 4, 2, 5, 7]
                else
                  ![0, 3, 4, 2, 6, 7]
              else
                if i.val < 120 then
                  ![0, 3, 4, 5, 6, 7]
                else
                  if i.val < 121 then
                    ![0, 3, 5, 1, 2, 4]
                  else
                    ![0, 3, 5, 1, 2, 6]
        else
          if i.val < 131 then
            if i.val < 126 then
              if i.val < 124 then
                if i.val < 123 then
                  ![0, 3, 5, 1, 2, 7]
                else
                  ![0, 3, 5, 1, 4, 6]
              else
                if i.val < 125 then
                  ![0, 3, 5, 1, 4, 7]
                else
                  ![0, 3, 5, 1, 6, 7]
            else
              if i.val < 128 then
                if i.val < 127 then
                  ![0, 3, 5, 2, 4, 6]
                else
                  ![0, 3, 5, 2, 4, 7]
              else
                if i.val < 129 then
                  ![0, 3, 5, 2, 6, 7]
                else
                  if i.val < 130 then
                    ![0, 3, 5, 4, 6, 7]
                  else
                    ![0, 3, 6, 1, 2, 4]
          else
            if i.val < 135 then
              if i.val < 133 then
                if i.val < 132 then
                  ![0, 3, 6, 1, 2, 5]
                else
                  ![0, 3, 6, 1, 2, 7]
              else
                if i.val < 134 then
                  ![0, 3, 6, 1, 4, 5]
                else
                  ![0, 3, 6, 1, 4, 7]
            else
              if i.val < 137 then
                if i.val < 136 then
                  ![0, 3, 6, 1, 5, 7]
                else
                  ![0, 3, 6, 2, 4, 5]
              else
                if i.val < 138 then
                  ![0, 3, 6, 2, 4, 7]
                else
                  if i.val < 139 then
                    ![0, 3, 6, 2, 5, 7]
                  else
                    ![0, 3, 6, 4, 5, 7]
  else
    if i.val < 210 then
      if i.val < 175 then
        if i.val < 157 then
          if i.val < 148 then
            if i.val < 144 then
              if i.val < 142 then
                if i.val < 141 then
                  ![0, 3, 7, 1, 2, 4]
                else
                  ![0, 3, 7, 1, 2, 5]
              else
                if i.val < 143 then
                  ![0, 3, 7, 1, 2, 6]
                else
                  ![0, 3, 7, 1, 4, 5]
            else
              if i.val < 146 then
                if i.val < 145 then
                  ![0, 3, 7, 1, 4, 6]
                else
                  ![0, 3, 7, 1, 5, 6]
              else
                if i.val < 147 then
                  ![0, 3, 7, 2, 4, 5]
                else
                  ![0, 3, 7, 2, 4, 6]
          else
            if i.val < 152 then
              if i.val < 150 then
                if i.val < 149 then
                  ![0, 3, 7, 2, 5, 6]
                else
                  ![0, 3, 7, 4, 5, 6]
              else
                if i.val < 151 then
                  ![0, 4, 5, 1, 2, 3]
                else
                  ![0, 4, 5, 1, 2, 6]
            else
              if i.val < 154 then
                if i.val < 153 then
                  ![0, 4, 5, 1, 2, 7]
                else
                  ![0, 4, 5, 1, 3, 6]
              else
                if i.val < 155 then
                  ![0, 4, 5, 1, 3, 7]
                else
                  if i.val < 156 then
                    ![0, 4, 5, 1, 6, 7]
                  else
                    ![0, 4, 5, 2, 3, 6]
        else
          if i.val < 166 then
            if i.val < 161 then
              if i.val < 159 then
                if i.val < 158 then
                  ![0, 4, 5, 2, 3, 7]
                else
                  ![0, 4, 5, 2, 6, 7]
              else
                if i.val < 160 then
                  ![0, 4, 5, 3, 6, 7]
                else
                  ![0, 4, 6, 1, 2, 3]
            else
              if i.val < 163 then
                if i.val < 162 then
                  ![0, 4, 6, 1, 2, 5]
                else
                  ![0, 4, 6, 1, 2, 7]
              else
                if i.val < 164 then
                  ![0, 4, 6, 1, 3, 5]
                else
                  if i.val < 165 then
                    ![0, 4, 6, 1, 3, 7]
                  else
                    ![0, 4, 6, 1, 5, 7]
          else
            if i.val < 170 then
              if i.val < 168 then
                if i.val < 167 then
                  ![0, 4, 6, 2, 3, 5]
                else
                  ![0, 4, 6, 2, 3, 7]
              else
                if i.val < 169 then
                  ![0, 4, 6, 2, 5, 7]
                else
                  ![0, 4, 6, 3, 5, 7]
            else
              if i.val < 172 then
                if i.val < 171 then
                  ![0, 4, 7, 1, 2, 3]
                else
                  ![0, 4, 7, 1, 2, 5]
              else
                if i.val < 173 then
                  ![0, 4, 7, 1, 2, 6]
                else
                  if i.val < 174 then
                    ![0, 4, 7, 1, 3, 5]
                  else
                    ![0, 4, 7, 1, 3, 6]
      else
        if i.val < 192 then
          if i.val < 183 then
            if i.val < 179 then
              if i.val < 177 then
                if i.val < 176 then
                  ![0, 4, 7, 1, 5, 6]
                else
                  ![0, 4, 7, 2, 3, 5]
              else
                if i.val < 178 then
                  ![0, 4, 7, 2, 3, 6]
                else
                  ![0, 4, 7, 2, 5, 6]
            else
              if i.val < 181 then
                if i.val < 180 then
                  ![0, 4, 7, 3, 5, 6]
                else
                  ![0, 5, 6, 1, 2, 3]
              else
                if i.val < 182 then
                  ![0, 5, 6, 1, 2, 4]
                else
                  ![0, 5, 6, 1, 2, 7]
          else
            if i.val < 187 then
              if i.val < 185 then
                if i.val < 184 then
                  ![0, 5, 6, 1, 3, 4]
                else
                  ![0, 5, 6, 1, 3, 7]
              else
                if i.val < 186 then
                  ![0, 5, 6, 1, 4, 7]
                else
                  ![0, 5, 6, 2, 3, 4]
            else
              if i.val < 189 then
                if i.val < 188 then
                  ![0, 5, 6, 2, 3, 7]
                else
                  ![0, 5, 6, 2, 4, 7]
              else
                if i.val < 190 then
                  ![0, 5, 6, 3, 4, 7]
                else
                  if i.val < 191 then
                    ![0, 5, 7, 1, 2, 3]
                  else
                    ![0, 5, 7, 1, 2, 4]
        else
          if i.val < 201 then
            if i.val < 196 then
              if i.val < 194 then
                if i.val < 193 then
                  ![0, 5, 7, 1, 2, 6]
                else
                  ![0, 5, 7, 1, 3, 4]
              else
                if i.val < 195 then
                  ![0, 5, 7, 1, 3, 6]
                else
                  ![0, 5, 7, 1, 4, 6]
            else
              if i.val < 198 then
                if i.val < 197 then
                  ![0, 5, 7, 2, 3, 4]
                else
                  ![0, 5, 7, 2, 3, 6]
              else
                if i.val < 199 then
                  ![0, 5, 7, 2, 4, 6]
                else
                  if i.val < 200 then
                    ![0, 5, 7, 3, 4, 6]
                  else
                    ![0, 6, 7, 1, 2, 3]
          else
            if i.val < 205 then
              if i.val < 203 then
                if i.val < 202 then
                  ![0, 6, 7, 1, 2, 4]
                else
                  ![0, 6, 7, 1, 2, 5]
              else
                if i.val < 204 then
                  ![0, 6, 7, 1, 3, 4]
                else
                  ![0, 6, 7, 1, 3, 5]
            else
              if i.val < 207 then
                if i.val < 206 then
                  ![0, 6, 7, 1, 4, 5]
                else
                  ![0, 6, 7, 2, 3, 4]
              else
                if i.val < 208 then
                  ![0, 6, 7, 2, 3, 5]
                else
                  if i.val < 209 then
                    ![0, 6, 7, 2, 4, 5]
                  else
                    ![0, 6, 7, 3, 4, 5]
    else
      if i.val < 245 then
        if i.val < 227 then
          if i.val < 218 then
            if i.val < 214 then
              if i.val < 212 then
                if i.val < 211 then
                  ![1, 2, 3, 4, 5, 6]
                else
                  ![1, 2, 3, 4, 5, 7]
              else
                if i.val < 213 then
                  ![1, 2, 3, 4, 6, 7]
                else
                  ![1, 2, 3, 5, 6, 7]
            else
              if i.val < 216 then
                if i.val < 215 then
                  ![1, 2, 4, 3, 5, 6]
                else
                  ![1, 2, 4, 3, 5, 7]
              else
                if i.val < 217 then
                  ![1, 2, 4, 3, 6, 7]
                else
                  ![1, 2, 4, 5, 6, 7]
          else
            if i.val < 222 then
              if i.val < 220 then
                if i.val < 219 then
                  ![1, 2, 5, 3, 4, 6]
                else
                  ![1, 2, 5, 3, 4, 7]
              else
                if i.val < 221 then
                  ![1, 2, 5, 3, 6, 7]
                else
                  ![1, 2, 5, 4, 6, 7]
            else
              if i.val < 224 then
                if i.val < 223 then
                  ![1, 2, 6, 3, 4, 5]
                else
                  ![1, 2, 6, 3, 4, 7]
              else
                if i.val < 225 then
                  ![1, 2, 6, 3, 5, 7]
                else
                  if i.val < 226 then
                    ![1, 2, 6, 4, 5, 7]
                  else
                    ![1, 2, 7, 3, 4, 5]
        else
          if i.val < 236 then
            if i.val < 231 then
              if i.val < 229 then
                if i.val < 228 then
                  ![1, 2, 7, 3, 4, 6]
                else
                  ![1, 2, 7, 3, 5, 6]
              else
                if i.val < 230 then
                  ![1, 2, 7, 4, 5, 6]
                else
                  ![1, 3, 4, 2, 5, 6]
            else
              if i.val < 233 then
                if i.val < 232 then
                  ![1, 3, 4, 2, 5, 7]
                else
                  ![1, 3, 4, 2, 6, 7]
              else
                if i.val < 234 then
                  ![1, 3, 4, 5, 6, 7]
                else
                  if i.val < 235 then
                    ![1, 3, 5, 2, 4, 6]
                  else
                    ![1, 3, 5, 2, 4, 7]
          else
            if i.val < 240 then
              if i.val < 238 then
                if i.val < 237 then
                  ![1, 3, 5, 2, 6, 7]
                else
                  ![1, 3, 5, 4, 6, 7]
              else
                if i.val < 239 then
                  ![1, 3, 6, 2, 4, 5]
                else
                  ![1, 3, 6, 2, 4, 7]
            else
              if i.val < 242 then
                if i.val < 241 then
                  ![1, 3, 6, 2, 5, 7]
                else
                  ![1, 3, 6, 4, 5, 7]
              else
                if i.val < 243 then
                  ![1, 3, 7, 2, 4, 5]
                else
                  if i.val < 244 then
                    ![1, 3, 7, 2, 4, 6]
                  else
                    ![1, 3, 7, 2, 5, 6]
      else
        if i.val < 262 then
          if i.val < 253 then
            if i.val < 249 then
              if i.val < 247 then
                if i.val < 246 then
                  ![1, 3, 7, 4, 5, 6]
                else
                  ![1, 4, 5, 2, 3, 6]
              else
                if i.val < 248 then
                  ![1, 4, 5, 2, 3, 7]
                else
                  ![1, 4, 5, 2, 6, 7]
            else
              if i.val < 251 then
                if i.val < 250 then
                  ![1, 4, 5, 3, 6, 7]
                else
                  ![1, 4, 6, 2, 3, 5]
              else
                if i.val < 252 then
                  ![1, 4, 6, 2, 3, 7]
                else
                  ![1, 4, 6, 2, 5, 7]
          else
            if i.val < 257 then
              if i.val < 255 then
                if i.val < 254 then
                  ![1, 4, 6, 3, 5, 7]
                else
                  ![1, 4, 7, 2, 3, 5]
              else
                if i.val < 256 then
                  ![1, 4, 7, 2, 3, 6]
                else
                  ![1, 4, 7, 2, 5, 6]
            else
              if i.val < 259 then
                if i.val < 258 then
                  ![1, 4, 7, 3, 5, 6]
                else
                  ![1, 5, 6, 2, 3, 4]
              else
                if i.val < 260 then
                  ![1, 5, 6, 2, 3, 7]
                else
                  if i.val < 261 then
                    ![1, 5, 6, 2, 4, 7]
                  else
                    ![1, 5, 6, 3, 4, 7]
        else
          if i.val < 271 then
            if i.val < 266 then
              if i.val < 264 then
                if i.val < 263 then
                  ![1, 5, 7, 2, 3, 4]
                else
                  ![1, 5, 7, 2, 3, 6]
              else
                if i.val < 265 then
                  ![1, 5, 7, 2, 4, 6]
                else
                  ![1, 5, 7, 3, 4, 6]
            else
              if i.val < 268 then
                if i.val < 267 then
                  ![1, 6, 7, 2, 3, 4]
                else
                  ![1, 6, 7, 2, 3, 5]
              else
                if i.val < 269 then
                  ![1, 6, 7, 2, 4, 5]
                else
                  if i.val < 270 then
                    ![1, 6, 7, 3, 4, 5]
                  else
                    ![2, 3, 4, 5, 6, 7]
          else
            if i.val < 275 then
              if i.val < 273 then
                if i.val < 272 then
                  ![2, 3, 5, 4, 6, 7]
                else
                  ![2, 3, 6, 4, 5, 7]
              else
                if i.val < 274 then
                  ![2, 3, 7, 4, 5, 6]
                else
                  ![2, 4, 5, 3, 6, 7]
            else
              if i.val < 277 then
                if i.val < 276 then
                  ![2, 4, 6, 3, 5, 7]
                else
                  ![2, 4, 7, 3, 5, 6]
              else
                if i.val < 278 then
                  ![2, 5, 6, 3, 4, 7]
                else
                  if i.val < 279 then
                    ![2, 5, 7, 3, 4, 6]
                  else
                    ![2, 6, 7, 3, 4, 5]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem fastTriple_correct (i : Fin 280) : fastTriple i = triplePair i := by
  fin_cases i <;> rfl

private def fastGenTriple (i : Fin 280) (k : Fin 2) (n : Fin 3) : Fin 8 :=
  fastTriple i ⟨3 * k.val + n.val, by omega⟩

private theorem fastGenTriple_eq (i : Fin 280) (k : Fin 2) (n : Fin 3) :
    fastGenTriple i k n = genTriple i k n :=
  congrFun (fastTriple_correct i) _

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
set_option Elab.async false in
public theorem genTriple_distinct : ∀ (i : Fin 280) (k : Fin 2),
    genTriple i k 0 ≠ genTriple i k 1 ∧ genTriple i k 0 ≠ genTriple i k 2 ∧
      genTriple i k 1 ≠ genTriple i k 2 := by
  have h : ∀ (i : Fin 280) (k : Fin 2),
      fastGenTriple i k 0 ≠ fastGenTriple i k 1 ∧
      fastGenTriple i k 0 ≠ fastGenTriple i k 2 ∧
      fastGenTriple i k 1 ≠ fastGenTriple i k 2 := by decide +kernel
  simpa only [fastGenTriple_eq] using h

private def adjacentIndex (r : Fin 7) (i : Fin 280) : Fin 280 :=
  (
    if i.val < 140 then
      if i.val < 70 then
        if i.val < 35 then
          if i.val < 17 then
            if i.val < 8 then
              if i.val < 4 then
                if i.val < 2 then
                  if i.val < 1 then
                    ![0, 0, 10, 0, 0, 1, 0]
                  else
                    ![1, 1, 11, 1, 3, 0, 2]
                else
                  if i.val < 3 then
                    ![2, 2, 12, 2, 4, 2, 1]
                  else
                    ![3, 3, 13, 6, 1, 3, 4]
              else
                if i.val < 6 then
                  if i.val < 5 then
                    ![4, 4, 14, 7, 2, 5, 3]
                  else
                    ![5, 5, 15, 8, 5, 4, 5]
                else
                  if i.val < 7 then
                    ![6, 6, 16, 3, 6, 6, 7]
                  else
                    ![7, 7, 17, 4, 7, 8, 6]
            else
              if i.val < 12 then
                if i.val < 10 then
                  if i.val < 9 then
                    ![8, 8, 18, 5, 9, 7, 8]
                  else
                    ![9, 9, 19, 9, 8, 9, 9]
                else
                  if i.val < 11 then
                    ![10, 60, 0, 20, 10, 11, 10]
                  else
                    ![11, 61, 1, 21, 13, 10, 12]
              else
                if i.val < 14 then
                  if i.val < 13 then
                    ![12, 62, 2, 22, 14, 12, 11]
                  else
                    ![13, 63, 3, 23, 11, 13, 14]
                else
                  if i.val < 15 then
                    ![14, 64, 4, 24, 12, 15, 13]
                  else
                    if i.val < 16 then
                      ![15, 65, 5, 25, 15, 14, 15]
                    else
                      ![16, 66, 6, 26, 16, 16, 17]
          else
            if i.val < 26 then
              if i.val < 21 then
                if i.val < 19 then
                  if i.val < 18 then
                    ![17, 67, 7, 27, 17, 18, 16]
                  else
                    ![18, 68, 8, 28, 19, 17, 18]
                else
                  if i.val < 20 then
                    ![19, 69, 9, 29, 18, 19, 19]
                  else
                    ![20, 70, 20, 10, 30, 21, 20]
              else
                if i.val < 23 then
                  if i.val < 22 then
                    ![21, 71, 21, 11, 31, 20, 22]
                  else
                    ![22, 72, 22, 12, 32, 22, 21]
                else
                  if i.val < 24 then
                    ![23, 73, 26, 13, 33, 23, 24]
                  else
                    if i.val < 25 then
                      ![24, 74, 27, 14, 34, 25, 23]
                    else
                      ![25, 75, 28, 15, 35, 24, 25]
            else
              if i.val < 30 then
                if i.val < 28 then
                  if i.val < 27 then
                    ![26, 76, 23, 16, 36, 26, 27]
                  else
                    ![27, 77, 24, 17, 37, 28, 26]
                else
                  if i.val < 29 then
                    ![28, 78, 25, 18, 38, 27, 28]
                  else
                    ![29, 79, 29, 19, 39, 29, 29]
              else
                if i.val < 32 then
                  if i.val < 31 then
                    ![30, 80, 30, 30, 20, 40, 30]
                  else
                    ![31, 81, 31, 33, 21, 41, 32]
                else
                  if i.val < 33 then
                    ![32, 82, 32, 34, 22, 42, 31]
                  else
                    if i.val < 34 then
                      ![33, 83, 36, 31, 23, 43, 34]
                    else
                      ![34, 84, 37, 32, 24, 44, 33]
        else
          if i.val < 52 then
            if i.val < 43 then
              if i.val < 39 then
                if i.val < 37 then
                  if i.val < 36 then
                    ![35, 85, 38, 35, 25, 45, 35]
                  else
                    ![36, 86, 33, 36, 26, 46, 37]
                else
                  if i.val < 38 then
                    ![37, 87, 34, 37, 27, 47, 36]
                  else
                    ![38, 88, 35, 39, 28, 48, 38]
              else
                if i.val < 41 then
                  if i.val < 40 then
                    ![39, 89, 39, 38, 29, 49, 39]
                  else
                    ![40, 90, 40, 40, 41, 30, 50]
                else
                  if i.val < 42 then
                    ![41, 91, 41, 43, 40, 31, 51]
                  else
                    ![42, 92, 42, 44, 42, 32, 52]
            else
              if i.val < 47 then
                if i.val < 45 then
                  if i.val < 44 then
                    ![43, 93, 46, 41, 43, 33, 53]
                  else
                    ![44, 94, 47, 42, 45, 34, 54]
                else
                  if i.val < 46 then
                    ![45, 95, 48, 45, 44, 35, 55]
                  else
                    ![46, 96, 43, 46, 46, 36, 56]
              else
                if i.val < 49 then
                  if i.val < 48 then
                    ![47, 97, 44, 47, 48, 37, 57]
                  else
                    ![48, 98, 45, 49, 47, 38, 58]
                else
                  if i.val < 50 then
                    ![49, 99, 49, 48, 49, 39, 59]
                  else
                    if i.val < 51 then
                      ![50, 100, 50, 50, 51, 50, 40]
                    else
                      ![51, 101, 51, 53, 50, 52, 41]
          else
            if i.val < 61 then
              if i.val < 56 then
                if i.val < 54 then
                  if i.val < 53 then
                    ![52, 102, 52, 54, 52, 51, 42]
                  else
                    ![53, 103, 56, 51, 53, 54, 43]
                else
                  if i.val < 55 then
                    ![54, 104, 57, 52, 55, 53, 44]
                  else
                    ![55, 105, 58, 55, 54, 55, 45]
              else
                if i.val < 58 then
                  if i.val < 57 then
                    ![56, 106, 53, 56, 56, 57, 46]
                  else
                    ![57, 107, 54, 57, 58, 56, 47]
                else
                  if i.val < 59 then
                    ![58, 108, 55, 59, 57, 58, 48]
                  else
                    if i.val < 60 then
                      ![59, 109, 59, 58, 59, 59, 49]
                    else
                      ![150, 10, 60, 70, 60, 61, 60]
            else
              if i.val < 65 then
                if i.val < 63 then
                  if i.val < 62 then
                    ![160, 11, 61, 71, 63, 60, 62]
                  else
                    ![170, 12, 62, 72, 64, 62, 61]
                else
                  if i.val < 64 then
                    ![180, 13, 63, 73, 61, 63, 64]
                  else
                    ![190, 14, 64, 74, 62, 65, 63]
              else
                if i.val < 67 then
                  if i.val < 66 then
                    ![200, 15, 65, 75, 65, 64, 65]
                  else
                    ![210, 16, 66, 76, 66, 66, 67]
                else
                  if i.val < 68 then
                    ![211, 17, 67, 77, 67, 68, 66]
                  else
                    if i.val < 69 then
                      ![212, 18, 68, 78, 69, 67, 68]
                    else
                      ![213, 19, 69, 79, 68, 69, 69]
      else
        if i.val < 105 then
          if i.val < 87 then
            if i.val < 78 then
              if i.val < 74 then
                if i.val < 72 then
                  if i.val < 71 then
                    ![120, 20, 110, 60, 80, 71, 70]
                  else
                    ![130, 21, 111, 61, 81, 70, 72]
                else
                  if i.val < 73 then
                    ![140, 22, 112, 62, 82, 72, 71]
                  else
                    ![181, 23, 113, 63, 83, 73, 74]
              else
                if i.val < 76 then
                  if i.val < 75 then
                    ![191, 24, 114, 64, 84, 75, 73]
                  else
                    ![201, 25, 115, 65, 85, 74, 75]
                else
                  if i.val < 77 then
                    ![214, 26, 116, 66, 86, 76, 77]
                  else
                    ![215, 27, 117, 67, 87, 78, 76]
            else
              if i.val < 82 then
                if i.val < 80 then
                  if i.val < 79 then
                    ![216, 28, 118, 68, 88, 77, 78]
                  else
                    ![217, 29, 119, 69, 89, 79, 79]
                else
                  if i.val < 81 then
                    ![110, 30, 120, 80, 70, 90, 80]
                  else
                    ![131, 31, 121, 83, 71, 91, 82]
              else
                if i.val < 84 then
                  if i.val < 83 then
                    ![141, 32, 122, 84, 72, 92, 81]
                  else
                    ![161, 33, 123, 81, 73, 93, 84]
                else
                  if i.val < 85 then
                    ![171, 34, 124, 82, 74, 94, 83]
                  else
                    if i.val < 86 then
                      ![202, 35, 125, 85, 75, 95, 85]
                    else
                      ![218, 36, 126, 86, 76, 96, 87]
          else
            if i.val < 96 then
              if i.val < 91 then
                if i.val < 89 then
                  if i.val < 88 then
                    ![219, 37, 127, 87, 77, 97, 86]
                  else
                    ![220, 38, 128, 89, 78, 98, 88]
                else
                  if i.val < 90 then
                    ![221, 39, 129, 88, 79, 99, 89]
                  else
                    ![111, 40, 130, 90, 91, 80, 100]
              else
                if i.val < 93 then
                  if i.val < 92 then
                    ![121, 41, 131, 93, 90, 81, 101]
                  else
                    ![142, 42, 132, 94, 92, 82, 102]
                else
                  if i.val < 94 then
                    ![151, 43, 133, 91, 93, 83, 103]
                  else
                    if i.val < 95 then
                      ![172, 44, 134, 92, 95, 84, 104]
                    else
                      ![192, 45, 135, 95, 94, 85, 105]
            else
              if i.val < 100 then
                if i.val < 98 then
                  if i.val < 97 then
                    ![222, 46, 136, 96, 96, 86, 106]
                  else
                    ![223, 47, 137, 97, 98, 87, 107]
                else
                  if i.val < 99 then
                    ![224, 48, 138, 99, 97, 88, 108]
                  else
                    ![225, 49, 139, 98, 99, 89, 109]
              else
                if i.val < 102 then
                  if i.val < 101 then
                    ![112, 50, 140, 100, 101, 100, 90]
                  else
                    ![122, 51, 141, 103, 100, 102, 91]
                else
                  if i.val < 103 then
                    ![132, 52, 142, 104, 102, 101, 92]
                  else
                    if i.val < 104 then
                      ![152, 53, 143, 101, 103, 104, 93]
                    else
                      ![162, 54, 144, 102, 105, 103, 94]
        else
          if i.val < 122 then
            if i.val < 113 then
              if i.val < 109 then
                if i.val < 107 then
                  if i.val < 106 then
                    ![182, 55, 145, 105, 104, 105, 95]
                  else
                    ![226, 56, 146, 106, 106, 107, 96]
                else
                  if i.val < 108 then
                    ![227, 57, 147, 107, 108, 106, 97]
                  else
                    ![228, 58, 148, 109, 107, 108, 98]
              else
                if i.val < 111 then
                  if i.val < 110 then
                    ![229, 59, 149, 108, 109, 109, 99]
                  else
                    ![80, 110, 70, 110, 120, 111, 110]
                else
                  if i.val < 112 then
                    ![90, 111, 71, 111, 121, 110, 112]
                  else
                    ![100, 112, 72, 112, 122, 112, 111]
            else
              if i.val < 117 then
                if i.val < 115 then
                  if i.val < 114 then
                    ![183, 116, 73, 113, 123, 113, 114]
                  else
                    ![193, 117, 74, 114, 124, 115, 113]
                else
                  if i.val < 116 then
                    ![203, 118, 75, 115, 125, 114, 115]
                  else
                    ![230, 113, 76, 116, 126, 116, 117]
              else
                if i.val < 119 then
                  if i.val < 118 then
                    ![231, 114, 77, 117, 127, 118, 116]
                  else
                    ![232, 115, 78, 118, 128, 117, 118]
                else
                  if i.val < 120 then
                    ![233, 119, 79, 119, 129, 119, 119]
                  else
                    if i.val < 121 then
                      ![70, 120, 80, 150, 110, 130, 120]
                    else
                      ![91, 121, 81, 151, 111, 131, 122]
          else
            if i.val < 131 then
              if i.val < 126 then
                if i.val < 124 then
                  if i.val < 123 then
                    ![101, 122, 82, 152, 112, 132, 121]
                  else
                    ![163, 126, 83, 153, 113, 133, 124]
                else
                  if i.val < 125 then
                    ![173, 127, 84, 154, 114, 134, 123]
                  else
                    ![204, 128, 85, 155, 115, 135, 125]
              else
                if i.val < 128 then
                  if i.val < 127 then
                    ![234, 123, 86, 156, 116, 136, 127]
                  else
                    ![235, 124, 87, 157, 117, 137, 126]
                else
                  if i.val < 129 then
                    ![236, 125, 88, 158, 118, 138, 128]
                  else
                    if i.val < 130 then
                      ![237, 129, 89, 159, 119, 139, 129]
                    else
                      ![71, 130, 90, 160, 131, 120, 140]
            else
              if i.val < 135 then
                if i.val < 133 then
                  if i.val < 132 then
                    ![81, 131, 91, 161, 130, 121, 141]
                  else
                    ![102, 132, 92, 162, 132, 122, 142]
                else
                  if i.val < 134 then
                    ![153, 136, 93, 163, 133, 123, 143]
                  else
                    ![174, 137, 94, 164, 135, 124, 144]
              else
                if i.val < 137 then
                  if i.val < 136 then
                    ![194, 138, 95, 165, 134, 125, 145]
                  else
                    ![238, 133, 96, 166, 136, 126, 146]
                else
                  if i.val < 138 then
                    ![239, 134, 97, 167, 138, 127, 147]
                  else
                    if i.val < 139 then
                      ![240, 135, 98, 168, 137, 128, 148]
                    else
                      ![241, 139, 99, 169, 139, 129, 149]
    else
      if i.val < 210 then
        if i.val < 175 then
          if i.val < 157 then
            if i.val < 148 then
              if i.val < 144 then
                if i.val < 142 then
                  if i.val < 141 then
                    ![72, 140, 100, 170, 141, 140, 130]
                  else
                    ![82, 141, 101, 171, 140, 142, 131]
                else
                  if i.val < 143 then
                    ![92, 142, 102, 172, 142, 141, 132]
                  else
                    ![154, 146, 103, 173, 143, 144, 133]
              else
                if i.val < 146 then
                  if i.val < 145 then
                    ![164, 147, 104, 174, 145, 143, 134]
                  else
                    ![184, 148, 105, 175, 144, 145, 135]
                else
                  if i.val < 147 then
                    ![242, 143, 106, 176, 146, 147, 136]
                  else
                    ![243, 144, 107, 177, 148, 146, 137]
            else
              if i.val < 152 then
                if i.val < 150 then
                  if i.val < 149 then
                    ![244, 145, 108, 178, 147, 148, 138]
                  else
                    ![245, 149, 109, 179, 149, 149, 139]
                else
                  if i.val < 151 then
                    ![60, 150, 150, 120, 150, 160, 150]
                  else
                    ![93, 151, 153, 121, 151, 161, 152]
              else
                if i.val < 154 then
                  if i.val < 153 then
                    ![103, 152, 154, 122, 152, 162, 151]
                  else
                    ![133, 156, 151, 123, 153, 163, 154]
                else
                  if i.val < 155 then
                    ![143, 157, 152, 124, 154, 164, 153]
                  else
                    if i.val < 156 then
                      ![205, 158, 155, 125, 155, 165, 155]
                    else
                      ![246, 153, 156, 126, 156, 166, 157]
          else
            if i.val < 166 then
              if i.val < 161 then
                if i.val < 159 then
                  if i.val < 158 then
                    ![247, 154, 157, 127, 157, 167, 156]
                  else
                    ![248, 155, 159, 128, 158, 168, 158]
                else
                  if i.val < 160 then
                    ![249, 159, 158, 129, 159, 169, 159]
                  else
                    ![61, 160, 160, 130, 180, 150, 170]
              else
                if i.val < 163 then
                  if i.val < 162 then
                    ![83, 161, 163, 131, 181, 151, 171]
                  else
                    ![104, 162, 164, 132, 182, 152, 172]
                else
                  if i.val < 164 then
                    ![123, 166, 161, 133, 183, 153, 173]
                  else
                    if i.val < 165 then
                      ![144, 167, 162, 134, 184, 154, 174]
                    else
                      ![195, 168, 165, 135, 185, 155, 175]
            else
              if i.val < 170 then
                if i.val < 168 then
                  if i.val < 167 then
                    ![250, 163, 166, 136, 186, 156, 176]
                  else
                    ![251, 164, 167, 137, 187, 157, 177]
                else
                  if i.val < 169 then
                    ![252, 165, 169, 138, 188, 158, 178]
                  else
                    ![253, 169, 168, 139, 189, 159, 179]
              else
                if i.val < 172 then
                  if i.val < 171 then
                    ![62, 170, 170, 140, 190, 170, 160]
                  else
                    ![84, 171, 173, 141, 191, 172, 161]
                else
                  if i.val < 173 then
                    ![94, 172, 174, 142, 192, 171, 162]
                  else
                    if i.val < 174 then
                      ![124, 176, 171, 143, 193, 174, 163]
                    else
                      ![134, 177, 172, 144, 194, 173, 164]
        else
          if i.val < 192 then
            if i.val < 183 then
              if i.val < 179 then
                if i.val < 177 then
                  if i.val < 176 then
                    ![185, 178, 175, 145, 195, 175, 165]
                  else
                    ![254, 173, 176, 146, 196, 177, 166]
                else
                  if i.val < 178 then
                    ![255, 174, 177, 147, 197, 176, 167]
                  else
                    ![256, 175, 179, 148, 198, 178, 168]
              else
                if i.val < 181 then
                  if i.val < 180 then
                    ![257, 179, 178, 149, 199, 179, 169]
                  else
                    ![63, 180, 180, 181, 160, 180, 190]
                else
                  if i.val < 182 then
                    ![73, 181, 183, 180, 161, 181, 191]
                  else
                    ![105, 182, 184, 182, 162, 182, 192]
            else
              if i.val < 187 then
                if i.val < 185 then
                  if i.val < 184 then
                    ![113, 186, 181, 183, 163, 183, 193]
                  else
                    ![145, 187, 182, 185, 164, 184, 194]
                else
                  if i.val < 186 then
                    ![175, 188, 185, 184, 165, 185, 195]
                  else
                    ![258, 183, 186, 186, 166, 186, 196]
              else
                if i.val < 189 then
                  if i.val < 188 then
                    ![259, 184, 187, 188, 167, 187, 197]
                  else
                    ![260, 185, 189, 187, 168, 188, 198]
                else
                  if i.val < 190 then
                    ![261, 189, 188, 189, 169, 189, 199]
                  else
                    if i.val < 191 then
                      ![64, 190, 190, 191, 170, 200, 180]
                    else
                      ![74, 191, 193, 190, 171, 201, 181]
          else
            if i.val < 201 then
              if i.val < 196 then
                if i.val < 194 then
                  if i.val < 193 then
                    ![95, 192, 194, 192, 172, 202, 182]
                  else
                    ![114, 196, 191, 193, 173, 203, 183]
                else
                  if i.val < 195 then
                    ![135, 197, 192, 195, 174, 204, 184]
                  else
                    ![165, 198, 195, 194, 175, 205, 185]
              else
                if i.val < 198 then
                  if i.val < 197 then
                    ![262, 193, 196, 196, 176, 206, 186]
                  else
                    ![263, 194, 197, 198, 177, 207, 187]
                else
                  if i.val < 199 then
                    ![264, 195, 199, 197, 178, 208, 188]
                  else
                    if i.val < 200 then
                      ![265, 199, 198, 199, 179, 209, 189]
                    else
                      ![65, 200, 200, 201, 200, 190, 200]
            else
              if i.val < 205 then
                if i.val < 203 then
                  if i.val < 202 then
                    ![75, 201, 203, 200, 202, 191, 201]
                  else
                    ![85, 202, 204, 202, 201, 192, 202]
                else
                  if i.val < 204 then
                    ![115, 206, 201, 203, 204, 193, 203]
                  else
                    ![125, 207, 202, 205, 203, 194, 204]
              else
                if i.val < 207 then
                  if i.val < 206 then
                    ![155, 208, 205, 204, 205, 195, 205]
                  else
                    ![266, 203, 206, 206, 207, 196, 206]
                else
                  if i.val < 208 then
                    ![267, 204, 207, 208, 206, 197, 207]
                  else
                    if i.val < 209 then
                      ![268, 205, 209, 207, 208, 198, 208]
                    else
                      ![269, 209, 208, 209, 209, 199, 209]
      else
        if i.val < 245 then
          if i.val < 227 then
            if i.val < 218 then
              if i.val < 214 then
                if i.val < 212 then
                  if i.val < 211 then
                    ![66, 210, 210, 214, 210, 210, 211]
                  else
                    ![67, 211, 211, 215, 211, 212, 210]
                else
                  if i.val < 213 then
                    ![68, 212, 212, 216, 213, 211, 212]
                  else
                    ![69, 213, 213, 217, 212, 213, 213]
              else
                if i.val < 216 then
                  if i.val < 215 then
                    ![76, 214, 230, 210, 218, 214, 215]
                  else
                    ![77, 215, 231, 211, 219, 216, 214]
                else
                  if i.val < 217 then
                    ![78, 216, 232, 212, 220, 215, 216]
                  else
                    ![79, 217, 233, 213, 221, 217, 217]
            else
              if i.val < 222 then
                if i.val < 220 then
                  if i.val < 219 then
                    ![86, 218, 234, 218, 214, 222, 219]
                  else
                    ![87, 219, 235, 219, 215, 223, 218]
                else
                  if i.val < 221 then
                    ![88, 220, 236, 221, 216, 224, 220]
                  else
                    ![89, 221, 237, 220, 217, 225, 221]
              else
                if i.val < 224 then
                  if i.val < 223 then
                    ![96, 222, 238, 222, 222, 218, 226]
                  else
                    ![97, 223, 239, 223, 224, 219, 227]
                else
                  if i.val < 225 then
                    ![98, 224, 240, 225, 223, 220, 228]
                  else
                    if i.val < 226 then
                      ![99, 225, 241, 224, 225, 221, 229]
                    else
                      ![106, 226, 242, 226, 226, 227, 222]
          else
            if i.val < 236 then
              if i.val < 231 then
                if i.val < 229 then
                  if i.val < 228 then
                    ![107, 227, 243, 227, 228, 226, 223]
                  else
                    ![108, 228, 244, 229, 227, 228, 224]
                else
                  if i.val < 230 then
                    ![109, 229, 245, 228, 229, 229, 225]
                  else
                    ![116, 258, 214, 230, 234, 230, 231]
              else
                if i.val < 233 then
                  if i.val < 232 then
                    ![117, 262, 215, 231, 235, 232, 230]
                  else
                    ![118, 266, 216, 232, 236, 231, 232]
                else
                  if i.val < 234 then
                    ![119, 270, 217, 233, 237, 233, 233]
                  else
                    if i.val < 235 then
                      ![126, 250, 218, 246, 230, 238, 235]
                    else
                      ![127, 254, 219, 247, 231, 239, 234]
            else
              if i.val < 240 then
                if i.val < 238 then
                  if i.val < 237 then
                    ![128, 267, 220, 248, 232, 240, 236]
                  else
                    ![129, 271, 221, 249, 233, 241, 237]
                else
                  if i.val < 239 then
                    ![136, 246, 222, 250, 238, 234, 242]
                  else
                    ![137, 255, 223, 251, 240, 235, 243]
              else
                if i.val < 242 then
                  if i.val < 241 then
                    ![138, 263, 224, 252, 239, 236, 244]
                  else
                    ![139, 272, 225, 253, 241, 237, 245]
                else
                  if i.val < 243 then
                    ![146, 247, 226, 254, 242, 243, 238]
                  else
                    if i.val < 244 then
                      ![147, 251, 227, 255, 244, 242, 239]
                    else
                      ![148, 259, 228, 256, 243, 244, 240]
        else
          if i.val < 262 then
            if i.val < 253 then
              if i.val < 249 then
                if i.val < 247 then
                  if i.val < 246 then
                    ![149, 273, 229, 257, 245, 245, 241]
                  else
                    ![156, 238, 246, 234, 246, 250, 247]
                else
                  if i.val < 248 then
                    ![157, 242, 247, 235, 247, 251, 246]
                  else
                    ![158, 268, 249, 236, 248, 252, 248]
              else
                if i.val < 251 then
                  if i.val < 250 then
                    ![159, 274, 248, 237, 249, 253, 249]
                  else
                    ![166, 234, 250, 238, 258, 246, 254]
                else
                  if i.val < 252 then
                    ![167, 243, 251, 239, 259, 247, 255]
                  else
                    ![168, 264, 253, 240, 260, 248, 256]
            else
              if i.val < 257 then
                if i.val < 255 then
                  if i.val < 254 then
                    ![169, 275, 252, 241, 261, 249, 257]
                  else
                    ![176, 235, 254, 242, 262, 255, 250]
                else
                  if i.val < 256 then
                    ![177, 239, 255, 243, 263, 254, 251]
                  else
                    ![178, 260, 257, 244, 264, 256, 252]
              else
                if i.val < 259 then
                  if i.val < 258 then
                    ![179, 276, 256, 245, 265, 257, 253]
                  else
                    ![186, 230, 258, 258, 250, 258, 262]
                else
                  if i.val < 260 then
                    ![187, 244, 259, 260, 251, 259, 263]
                  else
                    if i.val < 261 then
                      ![188, 256, 261, 259, 252, 260, 264]
                    else
                      ![189, 277, 260, 261, 253, 261, 265]
          else
            if i.val < 271 then
              if i.val < 266 then
                if i.val < 264 then
                  if i.val < 263 then
                    ![196, 231, 262, 262, 254, 266, 258]
                  else
                    ![197, 240, 263, 264, 255, 267, 259]
                else
                  if i.val < 265 then
                    ![198, 252, 265, 263, 256, 268, 260]
                  else
                    ![199, 278, 264, 265, 257, 269, 261]
              else
                if i.val < 268 then
                  if i.val < 267 then
                    ![206, 232, 266, 266, 267, 262, 266]
                  else
                    ![207, 236, 267, 268, 266, 263, 267]
                else
                  if i.val < 269 then
                    ![208, 248, 269, 267, 268, 264, 268]
                  else
                    if i.val < 270 then
                      ![209, 279, 268, 269, 269, 265, 269]
                    else
                      ![270, 233, 270, 270, 271, 270, 270]
            else
              if i.val < 275 then
                if i.val < 273 then
                  if i.val < 272 then
                    ![271, 237, 271, 274, 270, 272, 271]
                  else
                    ![272, 241, 272, 275, 272, 271, 273]
                else
                  if i.val < 274 then
                    ![273, 245, 273, 276, 273, 273, 272]
                  else
                    ![274, 249, 279, 271, 274, 275, 274]
              else
                if i.val < 277 then
                  if i.val < 276 then
                    ![275, 253, 278, 272, 277, 274, 276]
                  else
                    ![276, 257, 277, 273, 278, 276, 275]
                else
                  if i.val < 278 then
                    ![277, 261, 276, 277, 275, 277, 278]
                  else
                    if i.val < 279 then
                      ![278, 265, 275, 278, 276, 279, 277]
                    else
                      ![279, 269, 274, 279, 279, 278, 279]
  ) r

private def adjacentChoice (r : Fin 7) (i : Fin 280) (k : Fin 2) : Fin 12 :=
  (
    if i.val < 140 then
      if i.val < 70 then
        if i.val < 35 then
          if i.val < 17 then
            if i.val < 8 then
              if i.val < 4 then
                if i.val < 2 then
                  if i.val < 1 then
                    ![![4, 6], ![5, 6], ![0, 6], ![0, 10], ![0, 11], ![0, 6], ![0, 6]]
                  else
                    ![![4, 6], ![5, 6], ![0, 6], ![0, 10], ![0, 6], ![0, 6], ![0, 6]]
                else
                  if i.val < 3 then
                    ![![4, 6], ![5, 6], ![0, 6], ![0, 10], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![4, 6], ![5, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11], ![0, 6]]
              else
                if i.val < 6 then
                  if i.val < 5 then
                    ![![4, 6], ![5, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![4, 6], ![5, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11]]
                else
                  if i.val < 7 then
                    ![![4, 6], ![5, 6], ![0, 6], ![0, 6], ![0, 10], ![0, 11], ![0, 6]]
                  else
                    ![![4, 6], ![5, 6], ![0, 6], ![0, 6], ![0, 10], ![0, 6], ![0, 6]]
            else
              if i.val < 12 then
                if i.val < 10 then
                  if i.val < 9 then
                    ![![4, 6], ![5, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11]]
                  else
                    ![![4, 6], ![5, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 10], ![0, 11]]
                else
                  if i.val < 11 then
                    ![![4, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11], ![0, 6], ![0, 6]]
                  else
                    ![![4, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
              else
                if i.val < 14 then
                  if i.val < 13 then
                    ![![4, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![4, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11], ![0, 6]]
                else
                  if i.val < 15 then
                    ![![4, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    if i.val < 16 then
                      ![![4, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11]]
                    else
                      ![![4, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 10], ![0, 11], ![0, 6]]
          else
            if i.val < 26 then
              if i.val < 21 then
                if i.val < 19 then
                  if i.val < 18 then
                    ![![4, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 10], ![0, 6], ![0, 6]]
                  else
                    ![![4, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11]]
                else
                  if i.val < 20 then
                    ![![4, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 10], ![0, 11]]
                  else
                    ![![4, 6], ![0, 6], ![0, 10], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
              else
                if i.val < 23 then
                  if i.val < 22 then
                    ![![4, 6], ![0, 6], ![0, 10], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![4, 6], ![0, 6], ![0, 10], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                else
                  if i.val < 24 then
                    ![![4, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11], ![0, 6]]
                  else
                    if i.val < 25 then
                      ![![4, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                    else
                      ![![4, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11]]
            else
              if i.val < 30 then
                if i.val < 28 then
                  if i.val < 27 then
                    ![![4, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11], ![0, 6]]
                  else
                    ![![4, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                else
                  if i.val < 29 then
                    ![![4, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11]]
                  else
                    ![![4, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 10], ![0, 11]]
              else
                if i.val < 32 then
                  if i.val < 31 then
                    ![![4, 6], ![0, 6], ![0, 10], ![0, 11], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![4, 6], ![0, 6], ![0, 10], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                else
                  if i.val < 33 then
                    ![![4, 6], ![0, 6], ![0, 10], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    if i.val < 34 then
                      ![![4, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                    else
                      ![![4, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
        else
          if i.val < 52 then
            if i.val < 43 then
              if i.val < 39 then
                if i.val < 37 then
                  if i.val < 36 then
                    ![![4, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11]]
                  else
                    ![![4, 6], ![0, 6], ![0, 6], ![0, 10], ![0, 6], ![0, 6], ![0, 6]]
                else
                  if i.val < 38 then
                    ![![4, 6], ![0, 6], ![0, 6], ![0, 10], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![4, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11]]
              else
                if i.val < 41 then
                  if i.val < 40 then
                    ![![4, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11]]
                  else
                    ![![4, 6], ![0, 6], ![0, 10], ![0, 11], ![0, 6], ![0, 6], ![0, 6]]
                else
                  if i.val < 42 then
                    ![![4, 6], ![0, 6], ![0, 10], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![4, 6], ![0, 6], ![0, 10], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
            else
              if i.val < 47 then
                if i.val < 45 then
                  if i.val < 44 then
                    ![![4, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11], ![0, 6], ![0, 6]]
                  else
                    ![![4, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                else
                  if i.val < 46 then
                    ![![4, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![4, 6], ![0, 6], ![0, 6], ![0, 10], ![0, 11], ![0, 6], ![0, 6]]
              else
                if i.val < 49 then
                  if i.val < 48 then
                    ![![4, 6], ![0, 6], ![0, 6], ![0, 10], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![4, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                else
                  if i.val < 50 then
                    ![![4, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 10], ![0, 6], ![0, 6]]
                  else
                    if i.val < 51 then
                      ![![4, 6], ![0, 6], ![0, 10], ![0, 11], ![0, 6], ![0, 6], ![0, 6]]
                    else
                      ![![4, 6], ![0, 6], ![0, 10], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
          else
            if i.val < 61 then
              if i.val < 56 then
                if i.val < 54 then
                  if i.val < 53 then
                    ![![4, 6], ![0, 6], ![0, 10], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![4, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11], ![0, 6], ![0, 6]]
                else
                  if i.val < 55 then
                    ![![4, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![4, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11], ![0, 6]]
              else
                if i.val < 58 then
                  if i.val < 57 then
                    ![![4, 6], ![0, 6], ![0, 6], ![0, 10], ![0, 11], ![0, 6], ![0, 6]]
                  else
                    ![![4, 6], ![0, 6], ![0, 6], ![0, 10], ![0, 6], ![0, 6], ![0, 6]]
                else
                  if i.val < 59 then
                    ![![4, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11], ![0, 6]]
                  else
                    if i.val < 60 then
                      ![![4, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 10], ![0, 11], ![0, 6]]
                    else
                      ![![6, 0], ![0, 6], ![5, 6], ![0, 6], ![0, 11], ![0, 6], ![0, 6]]
            else
              if i.val < 65 then
                if i.val < 63 then
                  if i.val < 62 then
                    ![![6, 0], ![0, 6], ![5, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![6, 0], ![0, 6], ![5, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                else
                  if i.val < 64 then
                    ![![6, 0], ![0, 6], ![5, 6], ![0, 6], ![0, 6], ![0, 11], ![0, 6]]
                  else
                    ![![6, 0], ![0, 6], ![5, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
              else
                if i.val < 67 then
                  if i.val < 66 then
                    ![![6, 0], ![0, 6], ![5, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11]]
                  else
                    ![![0, 6], ![0, 6], ![5, 6], ![0, 6], ![0, 10], ![0, 11], ![0, 6]]
                else
                  if i.val < 68 then
                    ![![0, 6], ![0, 6], ![5, 6], ![0, 6], ![0, 10], ![0, 6], ![0, 6]]
                  else
                    if i.val < 69 then
                      ![![0, 6], ![0, 6], ![5, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11]]
                    else
                      ![![0, 6], ![0, 6], ![5, 6], ![0, 6], ![0, 6], ![0, 10], ![0, 11]]
      else
        if i.val < 105 then
          if i.val < 87 then
            if i.val < 78 then
              if i.val < 74 then
                if i.val < 72 then
                  if i.val < 71 then
                    ![![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                else
                  if i.val < 73 then
                    ![![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11], ![0, 6]]
              else
                if i.val < 76 then
                  if i.val < 75 then
                    ![![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11]]
                else
                  if i.val < 77 then
                    ![![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11], ![0, 6]]
                  else
                    ![![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
            else
              if i.val < 82 then
                if i.val < 80 then
                  if i.val < 79 then
                    ![![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11]]
                  else
                    ![![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 10], ![0, 11]]
                else
                  if i.val < 81 then
                    ![![6, 0], ![0, 6], ![0, 6], ![0, 11], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
              else
                if i.val < 84 then
                  if i.val < 83 then
                    ![![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                else
                  if i.val < 85 then
                    ![![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    if i.val < 86 then
                      ![![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11]]
                    else
                      ![![0, 6], ![0, 6], ![0, 6], ![0, 10], ![0, 6], ![0, 6], ![0, 6]]
          else
            if i.val < 96 then
              if i.val < 91 then
                if i.val < 89 then
                  if i.val < 88 then
                    ![![0, 6], ![0, 6], ![0, 6], ![0, 10], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11]]
                else
                  if i.val < 90 then
                    ![![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11]]
                  else
                    ![![6, 0], ![0, 6], ![0, 6], ![0, 11], ![0, 6], ![0, 6], ![0, 6]]
              else
                if i.val < 93 then
                  if i.val < 92 then
                    ![![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                else
                  if i.val < 94 then
                    ![![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 11], ![0, 6], ![0, 6]]
                  else
                    if i.val < 95 then
                      ![![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                    else
                      ![![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
            else
              if i.val < 100 then
                if i.val < 98 then
                  if i.val < 97 then
                    ![![0, 6], ![0, 6], ![0, 6], ![0, 10], ![0, 11], ![0, 6], ![0, 6]]
                  else
                    ![![0, 6], ![0, 6], ![0, 6], ![0, 10], ![0, 6], ![0, 6], ![0, 6]]
                else
                  if i.val < 99 then
                    ![![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 10], ![0, 6], ![0, 6]]
              else
                if i.val < 102 then
                  if i.val < 101 then
                    ![![6, 0], ![0, 6], ![0, 6], ![0, 11], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                else
                  if i.val < 103 then
                    ![![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    if i.val < 104 then
                      ![![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 11], ![0, 6], ![0, 6]]
                    else
                      ![![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
        else
          if i.val < 122 then
            if i.val < 113 then
              if i.val < 109 then
                if i.val < 107 then
                  if i.val < 106 then
                    ![![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11], ![0, 6]]
                  else
                    ![![0, 6], ![0, 6], ![0, 6], ![0, 10], ![0, 11], ![0, 6], ![0, 6]]
                else
                  if i.val < 108 then
                    ![![0, 6], ![0, 6], ![0, 6], ![0, 10], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11], ![0, 6]]
              else
                if i.val < 111 then
                  if i.val < 110 then
                    ![![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 10], ![0, 11], ![0, 6]]
                  else
                    ![![6, 0], ![0, 10], ![0, 6], ![5, 6], ![0, 6], ![0, 6], ![0, 6]]
                else
                  if i.val < 112 then
                    ![![6, 0], ![0, 10], ![0, 6], ![5, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![6, 0], ![0, 10], ![0, 6], ![5, 6], ![0, 6], ![0, 6], ![0, 6]]
            else
              if i.val < 117 then
                if i.val < 115 then
                  if i.val < 114 then
                    ![![6, 0], ![0, 6], ![0, 6], ![5, 6], ![0, 6], ![0, 11], ![0, 6]]
                  else
                    ![![6, 0], ![0, 6], ![0, 6], ![5, 6], ![0, 6], ![0, 6], ![0, 6]]
                else
                  if i.val < 116 then
                    ![![6, 0], ![0, 6], ![0, 6], ![5, 6], ![0, 6], ![0, 6], ![0, 11]]
                  else
                    ![![0, 6], ![0, 6], ![0, 6], ![5, 6], ![0, 6], ![0, 11], ![0, 6]]
              else
                if i.val < 119 then
                  if i.val < 118 then
                    ![![0, 6], ![0, 6], ![0, 6], ![5, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![0, 6], ![0, 6], ![0, 6], ![5, 6], ![0, 6], ![0, 6], ![0, 11]]
                else
                  if i.val < 120 then
                    ![![0, 6], ![0, 6], ![0, 6], ![5, 6], ![0, 6], ![0, 10], ![0, 11]]
                  else
                    if i.val < 121 then
                      ![![6, 0], ![0, 10], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                    else
                      ![![6, 0], ![0, 10], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
          else
            if i.val < 131 then
              if i.val < 126 then
                if i.val < 124 then
                  if i.val < 123 then
                    ![![6, 0], ![0, 10], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                else
                  if i.val < 125 then
                    ![![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11]]
              else
                if i.val < 128 then
                  if i.val < 127 then
                    ![![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                else
                  if i.val < 129 then
                    ![![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11]]
                  else
                    if i.val < 130 then
                      ![![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11]]
                    else
                      ![![6, 0], ![0, 10], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
            else
              if i.val < 135 then
                if i.val < 133 then
                  if i.val < 132 then
                    ![![6, 0], ![0, 10], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![6, 0], ![0, 10], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                else
                  if i.val < 134 then
                    ![![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 11], ![0, 6], ![0, 6]]
                  else
                    ![![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
              else
                if i.val < 137 then
                  if i.val < 136 then
                    ![![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11], ![0, 6], ![0, 6]]
                else
                  if i.val < 138 then
                    ![![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    if i.val < 139 then
                      ![![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                    else
                      ![![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 10], ![0, 6], ![0, 6]]
    else
      if i.val < 210 then
        if i.val < 175 then
          if i.val < 157 then
            if i.val < 148 then
              if i.val < 144 then
                if i.val < 142 then
                  if i.val < 141 then
                    ![![6, 0], ![0, 10], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![6, 0], ![0, 10], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                else
                  if i.val < 143 then
                    ![![6, 0], ![0, 10], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 11], ![0, 6], ![0, 6]]
              else
                if i.val < 146 then
                  if i.val < 145 then
                    ![![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11], ![0, 6]]
                else
                  if i.val < 147 then
                    ![![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11], ![0, 6], ![0, 6]]
                  else
                    ![![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
            else
              if i.val < 152 then
                if i.val < 150 then
                  if i.val < 149 then
                    ![![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11], ![0, 6]]
                  else
                    ![![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 10], ![0, 11], ![0, 6]]
                else
                  if i.val < 151 then
                    ![![6, 0], ![0, 10], ![0, 11], ![0, 6], ![5, 6], ![0, 6], ![0, 6]]
                  else
                    ![![6, 0], ![0, 10], ![0, 6], ![0, 6], ![5, 6], ![0, 6], ![0, 6]]
              else
                if i.val < 154 then
                  if i.val < 153 then
                    ![![6, 0], ![0, 10], ![0, 6], ![0, 6], ![5, 6], ![0, 6], ![0, 6]]
                  else
                    ![![6, 0], ![0, 6], ![0, 6], ![0, 6], ![5, 6], ![0, 6], ![0, 6]]
                else
                  if i.val < 155 then
                    ![![6, 0], ![0, 6], ![0, 6], ![0, 6], ![5, 6], ![0, 6], ![0, 6]]
                  else
                    if i.val < 156 then
                      ![![6, 0], ![0, 6], ![0, 6], ![0, 6], ![5, 6], ![0, 6], ![0, 11]]
                    else
                      ![![0, 6], ![0, 6], ![0, 10], ![0, 6], ![5, 6], ![0, 6], ![0, 6]]
          else
            if i.val < 166 then
              if i.val < 161 then
                if i.val < 159 then
                  if i.val < 158 then
                    ![![0, 6], ![0, 6], ![0, 10], ![0, 6], ![5, 6], ![0, 6], ![0, 6]]
                  else
                    ![![0, 6], ![0, 6], ![0, 6], ![0, 6], ![5, 6], ![0, 6], ![0, 11]]
                else
                  if i.val < 160 then
                    ![![0, 6], ![0, 6], ![0, 6], ![0, 6], ![5, 6], ![0, 6], ![0, 11]]
                  else
                    ![![6, 0], ![0, 10], ![0, 11], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
              else
                if i.val < 163 then
                  if i.val < 162 then
                    ![![6, 0], ![0, 10], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![6, 0], ![0, 10], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                else
                  if i.val < 164 then
                    ![![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    if i.val < 165 then
                      ![![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                    else
                      ![![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
            else
              if i.val < 170 then
                if i.val < 168 then
                  if i.val < 167 then
                    ![![0, 6], ![0, 6], ![0, 10], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![0, 6], ![0, 6], ![0, 10], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                else
                  if i.val < 169 then
                    ![![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
              else
                if i.val < 172 then
                  if i.val < 171 then
                    ![![6, 0], ![0, 10], ![0, 11], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![6, 0], ![0, 10], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                else
                  if i.val < 173 then
                    ![![6, 0], ![0, 10], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    if i.val < 174 then
                      ![![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                    else
                      ![![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
        else
          if i.val < 192 then
            if i.val < 183 then
              if i.val < 179 then
                if i.val < 177 then
                  if i.val < 176 then
                    ![![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11], ![0, 6]]
                  else
                    ![![0, 6], ![0, 6], ![0, 10], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                else
                  if i.val < 178 then
                    ![![0, 6], ![0, 6], ![0, 10], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11], ![0, 6]]
              else
                if i.val < 181 then
                  if i.val < 180 then
                    ![![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11], ![0, 6]]
                  else
                    ![![6, 0], ![0, 10], ![0, 11], ![0, 6], ![0, 6], ![5, 6], ![0, 6]]
                else
                  if i.val < 182 then
                    ![![6, 0], ![0, 10], ![0, 6], ![0, 6], ![0, 6], ![5, 6], ![0, 6]]
                  else
                    ![![6, 0], ![0, 10], ![0, 6], ![0, 6], ![0, 6], ![5, 6], ![0, 6]]
            else
              if i.val < 187 then
                if i.val < 185 then
                  if i.val < 184 then
                    ![![6, 0], ![0, 6], ![0, 6], ![0, 11], ![0, 6], ![5, 6], ![0, 6]]
                  else
                    ![![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![5, 6], ![0, 6]]
                else
                  if i.val < 186 then
                    ![![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![5, 6], ![0, 6]]
                  else
                    ![![0, 6], ![0, 6], ![0, 10], ![0, 11], ![0, 6], ![5, 6], ![0, 6]]
              else
                if i.val < 189 then
                  if i.val < 188 then
                    ![![0, 6], ![0, 6], ![0, 10], ![0, 6], ![0, 6], ![5, 6], ![0, 6]]
                  else
                    ![![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![5, 6], ![0, 6]]
                else
                  if i.val < 190 then
                    ![![0, 6], ![0, 6], ![0, 6], ![0, 10], ![0, 6], ![5, 6], ![0, 6]]
                  else
                    if i.val < 191 then
                      ![![6, 0], ![0, 10], ![0, 11], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                    else
                      ![![6, 0], ![0, 10], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
          else
            if i.val < 201 then
              if i.val < 196 then
                if i.val < 194 then
                  if i.val < 193 then
                    ![![6, 0], ![0, 10], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![6, 0], ![0, 6], ![0, 6], ![0, 11], ![0, 6], ![0, 6], ![0, 6]]
                else
                  if i.val < 195 then
                    ![![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
              else
                if i.val < 198 then
                  if i.val < 197 then
                    ![![0, 6], ![0, 6], ![0, 10], ![0, 11], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![0, 6], ![0, 6], ![0, 10], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                else
                  if i.val < 199 then
                    ![![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    if i.val < 200 then
                      ![![0, 6], ![0, 6], ![0, 6], ![0, 10], ![0, 6], ![0, 6], ![0, 6]]
                    else
                      ![![6, 0], ![0, 10], ![0, 11], ![0, 6], ![0, 6], ![0, 6], ![5, 6]]
            else
              if i.val < 205 then
                if i.val < 203 then
                  if i.val < 202 then
                    ![![6, 0], ![0, 10], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![5, 6]]
                  else
                    ![![6, 0], ![0, 10], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![5, 6]]
                else
                  if i.val < 204 then
                    ![![6, 0], ![0, 6], ![0, 6], ![0, 11], ![0, 6], ![0, 6], ![5, 6]]
                  else
                    ![![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![5, 6]]
              else
                if i.val < 207 then
                  if i.val < 206 then
                    ![![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 11], ![0, 6], ![5, 6]]
                  else
                    ![![0, 6], ![0, 6], ![0, 10], ![0, 11], ![0, 6], ![0, 6], ![5, 6]]
                else
                  if i.val < 208 then
                    ![![0, 6], ![0, 6], ![0, 10], ![0, 6], ![0, 6], ![0, 6], ![5, 6]]
                  else
                    if i.val < 209 then
                      ![![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11], ![0, 6], ![5, 6]]
                    else
                      ![![0, 6], ![0, 6], ![0, 6], ![0, 10], ![0, 11], ![0, 6], ![5, 6]]
      else
        if i.val < 245 then
          if i.val < 227 then
            if i.val < 218 then
              if i.val < 214 then
                if i.val < 212 then
                  if i.val < 211 then
                    ![![0, 6], ![4, 6], ![5, 6], ![0, 6], ![0, 10], ![0, 11], ![0, 6]]
                  else
                    ![![0, 6], ![4, 6], ![5, 6], ![0, 6], ![0, 10], ![0, 6], ![0, 6]]
                else
                  if i.val < 213 then
                    ![![0, 6], ![4, 6], ![5, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11]]
                  else
                    ![![0, 6], ![4, 6], ![5, 6], ![0, 6], ![0, 6], ![0, 10], ![0, 11]]
              else
                if i.val < 216 then
                  if i.val < 215 then
                    ![![0, 6], ![4, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11], ![0, 6]]
                  else
                    ![![0, 6], ![4, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                else
                  if i.val < 217 then
                    ![![0, 6], ![4, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11]]
                  else
                    ![![0, 6], ![4, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 10], ![0, 11]]
            else
              if i.val < 222 then
                if i.val < 220 then
                  if i.val < 219 then
                    ![![0, 6], ![4, 6], ![0, 6], ![0, 10], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![0, 6], ![4, 6], ![0, 6], ![0, 10], ![0, 6], ![0, 6], ![0, 6]]
                else
                  if i.val < 221 then
                    ![![0, 6], ![4, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11]]
                  else
                    ![![0, 6], ![4, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11]]
              else
                if i.val < 224 then
                  if i.val < 223 then
                    ![![0, 6], ![4, 6], ![0, 6], ![0, 10], ![0, 11], ![0, 6], ![0, 6]]
                  else
                    ![![0, 6], ![4, 6], ![0, 6], ![0, 10], ![0, 6], ![0, 6], ![0, 6]]
                else
                  if i.val < 225 then
                    ![![0, 6], ![4, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    if i.val < 226 then
                      ![![0, 6], ![4, 6], ![0, 6], ![0, 6], ![0, 10], ![0, 6], ![0, 6]]
                    else
                      ![![0, 6], ![4, 6], ![0, 6], ![0, 10], ![0, 11], ![0, 6], ![0, 6]]
          else
            if i.val < 236 then
              if i.val < 231 then
                if i.val < 229 then
                  if i.val < 228 then
                    ![![0, 6], ![4, 6], ![0, 6], ![0, 10], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![0, 6], ![4, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11], ![0, 6]]
                else
                  if i.val < 230 then
                    ![![0, 6], ![4, 6], ![0, 6], ![0, 6], ![0, 10], ![0, 11], ![0, 6]]
                  else
                    ![![0, 6], ![6, 0], ![0, 6], ![5, 6], ![0, 6], ![0, 11], ![0, 6]]
              else
                if i.val < 233 then
                  if i.val < 232 then
                    ![![0, 6], ![6, 0], ![0, 6], ![5, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![0, 6], ![6, 0], ![0, 6], ![5, 6], ![0, 6], ![0, 6], ![0, 11]]
                else
                  if i.val < 234 then
                    ![![0, 6], ![0, 6], ![0, 6], ![5, 6], ![0, 6], ![0, 10], ![0, 11]]
                  else
                    if i.val < 235 then
                      ![![0, 6], ![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                    else
                      ![![0, 6], ![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
            else
              if i.val < 240 then
                if i.val < 238 then
                  if i.val < 237 then
                    ![![0, 6], ![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11]]
                  else
                    ![![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11]]
                else
                  if i.val < 239 then
                    ![![0, 6], ![6, 0], ![0, 6], ![0, 6], ![0, 11], ![0, 6], ![0, 6]]
                  else
                    ![![0, 6], ![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
              else
                if i.val < 242 then
                  if i.val < 241 then
                    ![![0, 6], ![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 10], ![0, 6], ![0, 6]]
                else
                  if i.val < 243 then
                    ![![0, 6], ![6, 0], ![0, 6], ![0, 6], ![0, 11], ![0, 6], ![0, 6]]
                  else
                    if i.val < 244 then
                      ![![0, 6], ![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                    else
                      ![![0, 6], ![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 11], ![0, 6]]
        else
          if i.val < 262 then
            if i.val < 253 then
              if i.val < 249 then
                if i.val < 247 then
                  if i.val < 246 then
                    ![![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 10], ![0, 11], ![0, 6]]
                  else
                    ![![0, 6], ![6, 0], ![0, 10], ![0, 6], ![5, 6], ![0, 6], ![0, 6]]
                else
                  if i.val < 248 then
                    ![![0, 6], ![6, 0], ![0, 10], ![0, 6], ![5, 6], ![0, 6], ![0, 6]]
                  else
                    ![![0, 6], ![6, 0], ![0, 6], ![0, 6], ![5, 6], ![0, 6], ![0, 11]]
              else
                if i.val < 251 then
                  if i.val < 250 then
                    ![![0, 6], ![0, 6], ![0, 6], ![0, 6], ![5, 6], ![0, 6], ![0, 11]]
                  else
                    ![![0, 6], ![6, 0], ![0, 10], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                else
                  if i.val < 252 then
                    ![![0, 6], ![6, 0], ![0, 10], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![0, 6], ![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
            else
              if i.val < 257 then
                if i.val < 255 then
                  if i.val < 254 then
                    ![![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![0, 6], ![6, 0], ![0, 10], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                else
                  if i.val < 256 then
                    ![![0, 6], ![6, 0], ![0, 10], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![0, 6], ![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 11], ![0, 6]]
              else
                if i.val < 259 then
                  if i.val < 258 then
                    ![![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11], ![0, 6]]
                  else
                    ![![0, 6], ![6, 0], ![0, 10], ![0, 11], ![0, 6], ![5, 6], ![0, 6]]
                else
                  if i.val < 260 then
                    ![![0, 6], ![6, 0], ![0, 10], ![0, 6], ![0, 6], ![5, 6], ![0, 6]]
                  else
                    if i.val < 261 then
                      ![![0, 6], ![6, 0], ![0, 6], ![0, 6], ![0, 6], ![5, 6], ![0, 6]]
                    else
                      ![![0, 6], ![0, 6], ![0, 6], ![0, 10], ![0, 6], ![5, 6], ![0, 6]]
          else
            if i.val < 271 then
              if i.val < 266 then
                if i.val < 264 then
                  if i.val < 263 then
                    ![![0, 6], ![6, 0], ![0, 10], ![0, 11], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![0, 6], ![6, 0], ![0, 10], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                else
                  if i.val < 265 then
                    ![![0, 6], ![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![0, 6], ![0, 6], ![0, 6], ![0, 10], ![0, 6], ![0, 6], ![0, 6]]
              else
                if i.val < 268 then
                  if i.val < 267 then
                    ![![0, 6], ![6, 0], ![0, 10], ![0, 11], ![0, 6], ![0, 6], ![5, 6]]
                  else
                    ![![0, 6], ![6, 0], ![0, 10], ![0, 6], ![0, 6], ![0, 6], ![5, 6]]
                else
                  if i.val < 269 then
                    ![![0, 6], ![6, 0], ![0, 6], ![0, 6], ![0, 11], ![0, 6], ![5, 6]]
                  else
                    if i.val < 270 then
                      ![![0, 6], ![0, 6], ![0, 6], ![0, 10], ![0, 11], ![0, 6], ![5, 6]]
                    else
                      ![![0, 6], ![0, 6], ![4, 6], ![5, 6], ![0, 6], ![0, 10], ![0, 11]]
            else
              if i.val < 275 then
                if i.val < 273 then
                  if i.val < 272 then
                    ![![0, 6], ![0, 6], ![4, 6], ![0, 6], ![0, 6], ![0, 6], ![0, 11]]
                  else
                    ![![0, 6], ![0, 6], ![4, 6], ![0, 6], ![0, 10], ![0, 6], ![0, 6]]
                else
                  if i.val < 274 then
                    ![![0, 6], ![0, 6], ![4, 6], ![0, 6], ![0, 10], ![0, 11], ![0, 6]]
                  else
                    ![![0, 6], ![0, 6], ![6, 0], ![0, 6], ![5, 6], ![0, 6], ![0, 11]]
              else
                if i.val < 277 then
                  if i.val < 276 then
                    ![![0, 6], ![0, 6], ![6, 0], ![0, 6], ![0, 6], ![0, 6], ![0, 6]]
                  else
                    ![![0, 6], ![0, 6], ![6, 0], ![0, 6], ![0, 6], ![0, 11], ![0, 6]]
                else
                  if i.val < 278 then
                    ![![0, 6], ![0, 6], ![6, 0], ![0, 10], ![0, 6], ![5, 6], ![0, 6]]
                  else
                    if i.val < 279 then
                      ![![0, 6], ![0, 6], ![6, 0], ![0, 10], ![0, 6], ![0, 6], ![0, 6]]
                    else
                      ![![0, 6], ![0, 6], ![6, 0], ![0, 10], ![0, 11], ![0, 6], ![5, 6]]
  ) r k

private def targetGenerator (r : Fin 7) (i : Fin 280) (k : Fin 2) : Fin 2 :=
  ⟨(adjacentChoice r i k).val / 6, by omega⟩
private def targetOrder (r : Fin 7) (i : Fin 280) (k : Fin 2) : Fin 6 :=
  ⟨(adjacentChoice r i k).val % 6, Nat.mod_lt _ (by decide)⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
set_option Elab.async false in
private theorem adjacent_triple_certificate : ∀ (r : Fin 7) (i : Fin 280) (k : Fin 2) (n : Fin 3),
    Equiv.swap r.castSucc r.succ (genTriple i k n) =
      genTriple (adjacentIndex r i) (targetGenerator r i k) (tripleOrder (targetOrder r i k) n) := by
  have h : ∀ (r : Fin 7) (i : Fin 280) (k : Fin 2) (n : Fin 3),
      Equiv.swap r.castSucc r.succ (fastGenTriple i k n) =
        fastGenTriple (adjacentIndex r i) (targetGenerator r i k)
          (tripleOrder (targetOrder r i k) n) := by decide +kernel
  simpa only [fastGenTriple_eq] using h

/-- Adjacent transpositions carry the two triples to a listed pair. -/
public theorem adjacent_triples (r : Fin 7) (i : Fin 280) :
    ∃ j : Fin 280, ∀ k : Fin 2, ∃ l : Fin 2, ∃ q : Fin 6, ∀ n : Fin 3,
      Equiv.swap r.castSucc r.succ (genTriple i k n) =
        genTriple j l (tripleOrder q n) := by
  exact ⟨adjacentIndex r i, fun k =>
    ⟨targetGenerator r i k, targetOrder r i k, adjacent_triple_certificate r i k⟩⟩

end Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement.EightPoint.Coverage
