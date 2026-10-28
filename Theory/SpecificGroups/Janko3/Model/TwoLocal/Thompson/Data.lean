module

public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Thompson.Generators
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Thompson.Enumeration

/-!
# Collection data for the J₃ local normal forms

The mixed radices give 64 representatives in the proposed two-subgroup and
1152 in the local candidate. Power and conjugation tables are just candidate
indices here; `Relations` proves each equality on all 6156 letters.
Source: ATLAS J3G1-p6156B0; GLS 3, Table 5.3h, printed p.269.
-/

namespace Sporadic.Janko3.TwoLocal.ThompsonCertificate
@[expose] public def radix (k : ℕ) : ℕ := if k = 6 ∨ k = 7 then 3 else 2
@[expose] public def width : ℕ → ℕ := NormalForm.size radix
@[expose] public def representative : ℕ → ℕ → Model := NormalForm.rep gen radix
@[expose] public def chainSubgroup : ℕ → Subgroup Model := NormalForm.series gen
@[expose] public def conjugateDepth (k i : ℕ) : ℕ := if i < 6 then min k 6 else k

@[expose] public def powerIndex : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 12
  | 5 => 0
  | 6 => 44
  | 7 => 8
  | 8 => 50
  | _ => 0

@[expose] public def conjugateIndex (k i : ℕ) : ℕ :=
  (match k with
    | 0 => []
    | 1 => [1]
    | 2 => [1, 2]
    | 3 => [1, 2, 4]
    | 4 => [13, 11, 8, 4]
    | 5 => [4, 14, 1, 13, 21]
    | 6 => [11, 3, 7, 14, 31, 37]
    | 7 => [4, 2, 13, 8, 40, 61, 90]
    | 8 => [20, 41, 29, 17, 25, 2, 254, 115]
    | _ => []).getD i 0

@[expose] public def inverseConjugateIndex (k i : ℕ) : ℕ :=
  (match k with
    | 0 => []
    | 1 => [1]
    | 2 => [1, 2]
    | 3 => [1, 2, 4]
    | 4 => [13, 11, 8, 4]
    | 5 => [4, 14, 1, 13, 21]
    | 6 => [15, 13, 6, 3, 23, 41]
    | 7 => [13, 2, 1, 8, 60, 24, 115]
    | 8 => [17, 32, 24, 20, 21, 7, 239, 114]
    | _ => []).getD i 0

end Sporadic.Janko3.TwoLocal.ThompsonCertificate
