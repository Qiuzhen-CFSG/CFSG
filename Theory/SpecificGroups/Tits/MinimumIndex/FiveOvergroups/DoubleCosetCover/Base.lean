module
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Encoding
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Base
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Soundness of the five-overgroup double-coset certificates

Right-coset representatives are words `d * h`, where `d` is one of the fixed
source words and `h` is a word in the literal candidate generators. A finite
transition table supplies an equality `r * g = h' * r'` for each representative
and each of the two ATLAS generators. Word induction gives the ambient cover;
inverse letters follow from the orders two and three of those generators.

Numeric checks compare images at the certified base 0, 1, 2 and therefore
prove equalities in the actual Atlas group. No subgroup-order, distinctness,
or maximal-subgroup assumption occurs in the soundness theorem.
Source: primary ATLAS max4/max8 programs and `FiveOvergroups/Representatives`.
-/

namespace Tits.MinimumIndexFiveOvergroups.DoubleCosetCertificate
open Theory.GroupTheory Atlas1600OrderCertificate

private theorem letter_inv_a : (letter 0)⁻¹ = letter 0 := by rfl
private theorem letter_inv_b : (letter 1)⁻¹ = letter 1 * letter 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  rfl

public theorem induction_right (P : Atlas1600Group → Prop) (hone : P 1)
    (hstep : ∀ x, P x → ∀ i : Fin 2, P (x * letter i.castSucc.castSucc))
    (x : Atlas1600Group) : P x := by
  let H := Subgroup.closure ({letter 0, letter 1} : Set Atlas1600Group)
  let inc : Atlas1600Group →* Equiv.Perm (Fin 1600) :=
    { toFun := fun g => g.val, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have hle : atlas1600Subgroup ≤ H.map inc := by
    apply (Subgroup.closure_le _).mpr
    rintro _ (rfl | rfl)
    · exact ⟨letter 0, Subgroup.subset_closure (by simp), rfl⟩
    · exact ⟨letter 1, Subgroup.subset_closure (by simp), rfl⟩
  obtain ⟨y, hy, he⟩ := hle x.property
  have he' : y = x := Subtype.ext he
  have hx : x ∈ H := he' ▸ hy
  clear he he' hy y
  induction hx using Subgroup.closure_induction_right with
  | one => exact hone
  | mul_right g hg y hy ih =>
    rcases hy with rfl | rfl
    · exact hstep g ih 0
    · exact hstep g ih 1
  | mul_inv_cancel g hg y hy ih =>
    rcases hy with rfl | rfl
    · rw [letter_inv_a]
      exact hstep g ih 0
    · rw [letter_inv_b, ← mul_assoc]
      exact hstep _ (hstep g ih 1) 1

public theorem cover_of_transitions {I : Type*} (H : Subgroup Atlas1600Group)
    (rep : I → Atlas1600Group) (base : I) (hbase : rep base = 1)
    (hstep : ∀ r (g : Fin 2), ∃ (h : H) (s : I),
      rep r * letter g.castSucc.castSucc = h.val * rep s)
    (x : Atlas1600Group) : ∃ (h : H) (r : I), x = h.val * rep r := by
  apply induction_right (fun x => ∃ (h : H) (r : I), x = h.val * rep r)
  · exact ⟨1, base, by simp [hbase]⟩
  · rintro x ⟨h, r, rfl⟩ g
    obtain ⟨k, s, hs⟩ := hstep r g
    exact ⟨h * k, s, by simpa only [Subgroup.coe_mul, mul_assoc] using congrArg (h.val * ·) hs⟩

public theorem test_sound {n m : Nat} [NeZero n] [NeZero m]
    (pair : Atlas1600Group × Atlas1600Group) (reps : Fin n → Atlas1600Group)
    (maps : Fin 4 → Fin 1600 → Fin 1600) (repMaps : Fin n → Fin 1600 → Fin 1600)
    (hmaps : ∀ i p, maps i p = (gen pair i).val p)
    (hreps : ∀ i p, repMaps i p = (reps i).val p)
    (nodes : Fin m → Nat) (steps : Fin m → Fin 2 → Nat) (r : Fin m) (g : Fin 2)
    (h : test maps repMaps nodes steps r g = true) :
    nodeValue pair reps (nodes r) * letter g.castSucc.castSucc =
      value pair (steps r g / 32768) * nodeValue pair reps (nodes (target (steps r g))) := by
  have hn (c : Nat) (p : Fin 1600) :
      fastNode maps repMaps c p = (nodeValue pair reps c).val p := by
    simp only [fastNode, nodeValue, hreps, fastValue_spec pair maps hmaps]
    rfl
  simp only [test, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨⟨h0, h1⟩, h2⟩
  apply ConverseLocalCoverage.DoubleCosetCertificate.threePoint_ext
  · change (nodeValue pair reps (nodes r)).val ((letter g.castSucc.castSucc).val 0) =
      (value pair (steps r g / 32768)).val
        ((nodeValue pair reps (nodes (target (steps r g)))).val 0)
    simpa only [hn, fastLetter_spec, fastValue_spec pair maps hmaps] using h0
  · change (nodeValue pair reps (nodes r)).val ((letter g.castSucc.castSucc).val 1) =
      (value pair (steps r g / 32768)).val
        ((nodeValue pair reps (nodes (target (steps r g)))).val 1)
    simpa only [hn, fastLetter_spec, fastValue_spec pair maps hmaps] using h1
  · change (nodeValue pair reps (nodes r)).val ((letter g.castSucc.castSucc).val 2) =
      (value pair (steps r g / 32768)).val
        ((nodeValue pair reps (nodes (target (steps r g)))).val 2)
    simpa only [hn, fastLetter_spec, fastValue_spec pair maps hmaps] using h2

public theorem doubleCoset_cover_of_tests {n m : Nat} [NeZero n] [NeZero m]
    (pair : Atlas1600Group × Atlas1600Group) (reps : Fin n → Atlas1600Group)
    (maps : Fin 4 → Fin 1600 → Fin 1600) (repMaps : Fin n → Fin 1600 → Fin 1600)
    (hmaps : ∀ i p, maps i p = (gen pair i).val p)
    (hreps : ∀ i p, repMaps i p = (reps i).val p)
    (nodes : Fin m → Nat) (steps : Fin m → Fin 2 → Nat)
    (base : Fin m) (hbase : nodes base = 0) (hreps0 : reps 0 = 1)
    (h : ∀ r g, test maps repMaps nodes steps r g = true) (x : Atlas1600Group) :
    ∃ (a b : Subgroup.closure ({pair.1, pair.2} : Set Atlas1600Group)) (i : Fin n),
      x = a.val * reps i * b.val := by
  let H := Subgroup.closure ({pair.1, pair.2} : Set Atlas1600Group)
  have hinit : nodeValue pair reps (nodes base) = 1 := by
    rw [hbase]
    have hl : label (n := n) 0 = 0 := by apply Fin.ext; simp [label]
    simp only [nodeValue, hl, Nat.zero_div, value, decode,
      List.map_nil, List.prod_nil, mul_one, hreps0]

  have hstep (r : Fin m) (g : Fin 2) : ∃ (a : H) (s : Fin m),
      nodeValue pair reps (nodes r) * letter g.castSucc.castSucc =
        a.val * nodeValue pair reps (nodes s) :=
    ⟨⟨value pair (steps r g / 32768), value_mem pair _⟩, target (steps r g),
      test_sound pair reps maps repMaps hmaps hreps nodes steps r g (h r g)⟩
  obtain ⟨a, r, hr⟩ := cover_of_transitions H (fun r => nodeValue pair reps (nodes r))
    base hinit hstep x
  exact ⟨a, ⟨value pair (nodes r / 32), value_mem pair _⟩, label (nodes r),
    by simpa only [nodeValue, mul_assoc] using hr⟩

end Tits.MinimumIndexFiveOvergroups.DoubleCosetCertificate
