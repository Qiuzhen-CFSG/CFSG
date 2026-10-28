module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.FirstFusion.OrbitChecks
public import Theory.GroupTheory.GeneratorCosetCoverIndex

/-!
# The odd-index centralizer of the concrete J₂ commutator involution

The certified rows are exactly the conjugates of `t` under the explicit
carrier words `rep`. Generator transitions give a right-coset cover by
`C(t)`, and the checked four-point fingerprints separate its 315 cosets.
Consequently the centralizer has odd index, without using the group order.
The same cover proves that its actual Schreier factors generate it.

This odd-index subgroup contains a Sylow two-subgroup and is the local
subgroup used by `Reduction` to control arbitrary involutions. All words and
all conjugators are elements of the degree-100 ATLAS generated carrier.
Source: ATLAS `J2G1-p100B0`; GLS3, Table 5.3g motivates the involution fusion.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.GeneratorPair.FirstFusion
open Theory.GroupTheory OrbitData

def centralizer : Subgroup Carrier := Subgroup.centralizer ({t} : Set Carrier)
def rep (i : Fin 315) : Carrier := evalWord letter (words i)

theorem rep_zero : rep 0 = 1 := rfl

theorem row_spec (i : Fin 315) (p : Fin 100) :
    inclusion ((rep i)⁻¹ * t * rep i) p = value i p := by
  have aux : ∀ (n : Nat) (j : Fin 315), j.val = n → ∀ q : Fin 100,
      inclusion ((rep j)⁻¹ * t * rep j) q = value j q := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro j hj q
      by_cases hzero : j = 0
      · subst j
        simpa only [rep_zero, inv_one, one_mul, mul_one, inclusion_t] using
          (value_zero q).symm
      obtain ⟨hlt, hw, hn⟩ := word_data j hzero
      have hp := ih (parent j).val (hj ▸ hlt) (parent j) rfl
      have hr : rep j = rep (parent j) * letter (parentLetter j) := by
        simp only [rep, hw, evalWord_append, evalWord, mul_one]
      have he : (rep j)⁻¹ * t * rep j =
          (letter (parentLetter j))⁻¹ * ((rep (parent j))⁻¹ * t * rep (parent j)) *
            letter (parentLetter j) := by rw [hr]; simp only [mul_inv_rev, mul_assoc]
      rw [he, map_mul, map_mul, map_inv, inclusion_letter]
      change (permLetter (parentLetter j))⁻¹
        (inclusion ((rep (parent j))⁻¹ * t * rep (parent j))
          (permLetter (parentLetter j) q)) = value j q
      rw [hp, ← value_step, hn]
  exact aux i.val i rfl p

theorem row_injective : Function.Injective value := by
  intro i j hij
  have h := congrArg (fun f => identify (fingerprint f)) hij
  simpa only [fingerprint_left_inverse] using h

theorem step_mem (i : Fin 315) (s : Fin 3) :
    rep i * letter s * (rep (next i s))⁻¹ ∈ centralizer := by
  have h : (rep (next i s))⁻¹ * t * rep (next i s) =
      (letter s)⁻¹ * ((rep i)⁻¹ * t * rep i) * letter s := by
    apply inclusion_injective
    apply Equiv.ext
    intro p
    rw [row_spec, map_mul, map_mul, map_inv, inclusion_letter]
    change value (next i s) p =
      (permLetter s)⁻¹ (inclusion ((rep i)⁻¹ * t * rep i) (permLetter s p))
    rw [row_spec]
    exact value_step i s p
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  have he := congrArg (fun z : Carrier => rep i * letter s * z * (rep (next i s))⁻¹) h
  simpa [mul_assoc] using he

def cosetCover : Subgroup.GeneratorCosetCover centralizer letter (Fin 315) where
  repr := rep
  initial := 0
  initial_eq := rep_zero
  step i s := ⟨⟨_, step_mem i s⟩, next i s, by simp [mul_assoc]⟩
  inv_step i s := by
    rw [← letter_inv]
    exact ⟨⟨_, step_mem i (invLetter s)⟩, next i (invLetter s), by simp [mul_assoc]⟩

theorem coset_separation (i j : Fin 315)
    (h : rep i * (rep j)⁻¹ ∈ centralizer) : i = j := by
  have hc := Subgroup.mem_centralizer_singleton_iff.mp h
  have he := congrArg (fun z : Carrier => (rep i)⁻¹ * z * rep j) hc
  have hv : (rep j)⁻¹ * t * rep j = (rep i)⁻¹ * t * rep i := by
    simpa [mul_assoc] using he
  apply row_injective
  funext p
  rw [← row_spec, ← row_spec, hv]

theorem centralizer_index : centralizer.index = 315 := by
  apply Nat.le_antisymm
  · simpa only [Nat.card_fin] using cosetCover.index_le_card letter_generates
  · simpa only [Nat.card_fin] using
      Subgroup.card_le_index_of_rightCoset_separation centralizer rep coset_separation

theorem centralizer_odd_index : ¬ 2 ∣ centralizer.index := by
  rw [centralizer_index]
  decide

/-- The actual Schreier factors of the certified right-coset transversal. -/
def schreier (is : Fin 315 × Fin 3) : Carrier :=
  rep is.1 * letter is.2 * (rep (next is.1 is.2))⁻¹

theorem centralizer_eq_closure_schreier :
    centralizer = Subgroup.closure (Set.range schreier) := by
  let H := Subgroup.closure (Set.range schreier)
  have hle : H ≤ centralizer := by
    apply (Subgroup.closure_le centralizer).mpr
    rintro _ ⟨⟨i, s⟩, rfl⟩
    exact step_mem i s
  have hs (i : Fin 315) (s : Fin 3) : schreier (i, s) ∈ H :=
    Subgroup.subset_closure ⟨(i, s), rfl⟩
  let cover : Subgroup.GeneratorCosetCover H letter (Fin 315) := {
    repr := rep
    initial := 0
    initial_eq := rep_zero
    step i s := ⟨⟨_, hs i s⟩, next i s, by simp [schreier, mul_assoc]⟩
    inv_step i s := by
      rw [← letter_inv]
      exact ⟨⟨_, hs i (invLetter s)⟩, next i (invLetter s), by
        simp [schreier, mul_assoc]⟩ }
  apply le_antisymm _ hle
  intro x hx
  obtain ⟨h, i, hi⟩ := cover.covers letter_generates x
  change x = h.val * rep i at hi
  have hr : rep i ∈ centralizer := by
    have hm := centralizer.mul_mem (centralizer.inv_mem (hle h.property)) hx
    simpa only [hi, inv_mul_cancel_left] using hm
  have hi0 : i = 0 := coset_separation i 0 (by simpa only [rep_zero, inv_one, mul_one] using hr)
  simpa only [hi, hi0, rep_zero, mul_one] using h.property

end Sporadic.LeechRelated.J2.GeneratorPair.FirstFusion
