module
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.Representatives

/-!
# Compact recovery certificates for whole-group thirteen-pairs

Recovering the standard generator `a` suffices: every pair already contains
`ab`, and hence also contains `b = a⁻¹(ab)`. To evaluate recovery words, move
signed powers through conjugation before applying the permutations. This
avoids reevaluating the long representative word for each repeated factor.
The existing three-point-base checker supplies the equality proof.

`blockTest_sound` applies this argument to a bounded interval of the exact
published representative family, omitting only zero and `exceptionalIndices`.
It requires a kernel-checked Boolean certificate; discovery data alone asserts
no generation result.

Source: the primary ATLAS Tits generators, with conventions and attribution in
`../source/README.md`. The independent word search is in `source/discover.py`.
-/

namespace Tits.MinimumIndexThirteen.PairGeneration
namespace GenericGeneration
open Atlas1600OrderCertificate

public theorem eq_top_of_recoveryA (code : Nat) (w : List (Bool × Int))
    (h : recoveryTest code w 2 = true) :
    pairSubgroup (standardWord code) = ⊤ := by
  have ha : standardGenerator false ∈ pairSubgroup (standardWord code) :=
    recoveryTest_sound code w 2 h
  apply eq_top_of_standardGenerators_mem _ ha
  have hu : generator ∈ pairSubgroup (standardWord code) :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers generator)
  have hb := (pairSubgroup (standardWord code)).mul_mem
    ((pairSubgroup (standardWord code)).inv_mem ha) hu
  change (standardGenerator false)⁻¹ *
    (standardGenerator false * standardGenerator true) ∈ _ at hb
  simpa only [inv_mul_cancel_left] using hb

@[expose] public def poweredWord (code : Nat) (w : List (Bool × Int)) :
    Equiv.Perm (Fin 1600) :=
  (w.map (fun s => if s.1 then
    fastWord code * (L0G0 * L0G1) ^ s.2 * (fastWord code)⁻¹
    else (L0G0 * L0G1) ^ s.2)).prod

public theorem poweredWord_eq (code : Nat) (w : List (Bool × Int)) :
    poweredWord code w = fastPairWord code w := by
  unfold poweredWord fastPairWord pairWord
  congr 1
  apply List.map_congr_left
  rintro ⟨b, e⟩ _
  cases b
  · rfl
  · exact conj_zpow.symm

@[expose] public def test (code : Nat) (w : List (Bool × Int)) : Bool :=
  (poweredWord code w 0 == L0G0 0) &&
  (poweredWord code w 1 == L0G0 1) &&
  (poweredWord code w 2 == L0G0 2)

public theorem eq_top_of_test (code : Nat) (w : List (Bool × Int))
    (h : test code w = true) : pairSubgroup (standardWord code) = ⊤ := by
  apply eq_top_of_recoveryA code w
  have ht : fastWord 2 = L0G0 := by
    change L0G0 * 1 = L0G0
    exact mul_one _
  simpa only [test, recoveryTest, poweredWord_eq, ht] using h

/-- Check a bounded interval without asking for a word at excluded indices. -/
@[expose] public def blockTest (lo count : Nat)
    (words : Fin count → List (Bool × Int)) : Bool :=
  checkFin fun i =>
    if hk : lo + i.val < 3010 then
      let k : Fin 3010 := ⟨lo + i.val, hk⟩
      if k = 0 ∨ k ∈ exceptionalIndices then true
      else test (representativeCode k) (words i)
    else true

/-- A bounded word certificate gives generation on that literal index interval. -/
public theorem blockTest_sound (lo count : Nat)
    (words : Fin count → List (Bool × Int))
    (h : blockTest lo count words = true)
    (k : Fin 3010) (hlo : lo ≤ k.val) (hhi : k.val < lo + count)
    (hk : k ≠ 0) (he : k ∉ exceptionalIndices) :
    pairSubgroup (representative k) = ⊤ := by
  let i : Fin count := ⟨k.val - lo, by omega⟩
  have hi : lo + i.val = k.val := by dsimp [i]; omega
  have hh := (checkFin_spec _).mp h i
  dsimp only at hh
  simp only [hi, dif_pos k.isLt] at hh
  change (if k = 0 ∨ k ∈ exceptionalIndices then true
    else test (representativeCode k) (words i)) = true at hh
  rw [if_neg (not_or.mpr ⟨hk, he⟩)] at hh
  exact eq_top_of_test _ _ hh

end GenericGeneration
end Tits.MinimumIndexThirteen.PairGeneration
