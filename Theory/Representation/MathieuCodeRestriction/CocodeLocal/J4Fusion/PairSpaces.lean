module
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal

/-!
# Small subspaces consisting of Todd pair vectors

Golay minimum distance eight lifts a relation among three pair vectors to
an equality of the original permutation words. Three independent vectors
would have seven nonzero sums of weight two. Each active coordinate occurs
in four of these sums, contradicting the total weight fourteen. Hence such
a subspace has order at most four and dimension at most two.

The coordinate-counting argument follows the existing binary constant-weight
proof in `BinaryPermutation/SixConstantWeight`, without finite enumeration.
The original Golay bound is reused through `CocodeLocal`; its ATLAS source
and license attribution remain in that module and `LICENSES/ATLAS.txt`.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (6.3)(b), p.602.
-/

public section
open scoped BigOperators
namespace MathieuCode.J4Fusion

/-- A relation among three pair classes lifts to the literal permutation
words: their total possible support has size six, below Golay distance eight. -/
theorem pair_add_lifts (A B C : PointPair)
    (he : pairVector A + pairVector B = pairVector C) :
    wordOfSet A.val + wordOfSet B.val = wordOfSet C.val := by
  have hq : codeInCore.mkQ
      ((⟨wordOfSet A.val,wordOfSet_mem_core A⟩ : Core) +
        ⟨wordOfSet B.val,wordOfSet_mem_core B⟩) =
      codeInCore.mkQ ⟨wordOfSet C.val,wordOfSet_mem_core C⟩ := by
    rw [map_add]
    exact he
  have hm : wordOfSet A.val + wordOfSet B.val - wordOfSet C.val ∈ golay :=
    (Submodule.Quotient.eq codeInCore).mp hq
  apply sub_eq_zero.mp
  by_contra hn
  have hl := native_golay_minimum hm hn
  have hu : hammingNorm (wordOfSet A.val + wordOfSet B.val - wordOfSet C.val) ≤
      (A.val ∪ B.val ∪ C.val).card := by
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hi
    by_contra hh
    simp only [Finset.mem_union,not_or] at hh
    simp [wordOfSet,hh.1.1,hh.1.2,hh.2] at hi
  have hc := (Finset.card_union_le (A.val ∪ B.val) C.val).trans
    (Nat.add_le_add_right (Finset.card_union_le A.val B.val) C.val.card)
  rw [A.property,B.property,C.property] at hc
  omega

private def bit (x : ZMod 2) : ℕ := if x = 0 then 0 else 1

private theorem bit_triple (a b c : ZMod 2) :
    bit a + bit b + bit c + bit (a+b) + bit (a+c) + bit (b+c) + bit (a+b+c) =
      4 * (if a = 0 ∧ b = 0 ∧ c = 0 then 0 else 1) := by
  revert a b c
  decide

private theorem triple_weight (v w x : Full) :
    hammingNorm v + hammingNorm w + hammingNorm x + hammingNorm (v+w) +
      hammingNorm (v+x) + hammingNorm (w+x) + hammingNorm (v+w+x) =
      4 * (Finset.univ.filter (fun i => ¬ (v i = 0 ∧ w i = 0 ∧ x i = 0))).card := by
  simp only [Atlas.Codes.hammingNorm_eq_sum,Pi.add_apply]
  change (∑ i,bit (v i)) + (∑ i,bit (w i)) + (∑ i,bit (x i)) +
    (∑ i,bit (v i+w i)) + (∑ i,bit (v i+x i)) + (∑ i,bit (w i+x i)) +
      (∑ i,bit (v i+w i+x i)) = _
  simp only [← Finset.sum_add_distrib,bit_triple]
  rw [← Finset.mul_sum]
  apply congrArg (fun n : ℕ => 4*n)
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp_all

private theorem cocode_add_self (v : Cocode) : v+v=0 := by
  rw [←two_smul (ZMod 2) v]
  rw [show (2 : ZMod 2) = 0 from rfl,zero_smul]

private theorem cocode_add_zero {v w : Cocode} (he : v+w=0) : w=v := by
  have hh := congrArg (fun x : Cocode => v+x) he
  simpa only [←add_assoc,cocode_add_self,zero_add,add_zero] using hh

/-- The rank bound in AS91 (6.3)(b): a subspace whose nonzero vectors
are all pair vectors has order at most four. The proof uses the lifted
three-word weight identity, not enumeration of subspaces. -/
theorem pair_space_card_le_four (U : Submodule (ZMod 2) Cocode)
    (hp : ∀ v ∈ U, v ≠ 0 → ∃ B : PointPair, v = pairVector B) : Nat.card U ≤ 4 := by
  classical
  have bound (v w : Cocode) (hc : ∀ x ∈ U, x = 0 ∨ x = v ∨ x = w ∨ x = v+w) :
      Nat.card U ≤ 4 := by
    let s : Finset Cocode := {0,v,w,v+w}
    let f : U → s := fun x => ⟨x.val,by simpa [s] using hc x.val x.property⟩
    have hi : Function.Injective f := fun a b he =>
      Subtype.ext (congrArg (fun x : s => x.val) he)
    have hs : s.card ≤ 4 := (Finset.card_insert_le _ _).trans
      (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans
        (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp)))))
    exact (Nat.card_le_card_of_injective f hi).trans (by
      simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using hs)
  by_cases hv : ∃ v ∈ U, v ≠ 0
  swap
  · apply bound 0 0
    intro x hx
    exact Or.inl (by by_contra hn; exact hv ⟨x,hx,hn⟩)
  obtain ⟨v,hvU,hv0⟩ := hv
  by_cases hw : ∃ w ∈ U, w ≠ 0 ∧ w ≠ v
  swap
  · apply bound v 0
    intro x hx
    by_cases hx0 : x=0
    · exact Or.inl hx0
    · exact Or.inr (Or.inl (by by_contra hn; exact hw ⟨x,hx,hx0,hn⟩))
  obtain ⟨w,hwU,hw0,hwv⟩ := hw
  apply bound v w
  intro x hxU
  by_contra hx
  have hn : x ≠ 0 ∧ x ≠ v ∧ x ≠ w ∧ x ≠ v+w := by simpa only [not_or] using hx
  have hvw : v+w ≠ 0 := fun he => hwv (cocode_add_zero he)
  have hvx : v+x ≠ 0 := fun he => hn.2.1 (cocode_add_zero he)
  have hwx : w+x ≠ 0 := fun he => hn.2.2.1 (cocode_add_zero he)
  have hvwx : v+w+x ≠ 0 := fun he => hn.2.2.2 (cocode_add_zero he)
  obtain ⟨A,hA⟩ := hp v hvU hv0
  obtain ⟨B,hB⟩ := hp w hwU hw0
  obtain ⟨C,hC⟩ := hp x hxU hn.1
  obtain ⟨D,hD⟩ := hp (v+w) (U.add_mem hvU hwU) hvw
  obtain ⟨F,hF⟩ := hp (v+x) (U.add_mem hvU hxU) hvx
  obtain ⟨H,hH⟩ := hp (w+x) (U.add_mem hwU hxU) hwx
  obtain ⟨J,hJ⟩ := hp (v+w+x) (U.add_mem (U.add_mem hvU hwU) hxU) hvwx
  have hAB := pair_add_lifts A B D (by rw [←hA,←hB,←hD])
  have hAC := pair_add_lifts A C F (by rw [←hA,←hC,←hF])
  have hBC := pair_add_lifts B C H (by rw [←hB,←hC,←hH])
  have hDC := pair_add_lifts D C J (by rw [←hD,←hC,←hJ])
  have ht := triple_weight (wordOfSet A.val) (wordOfSet B.val) (wordOfSet C.val)
  rw [hAB,hAC,hBC,hDC] at ht
  simp only [wordOfSet_weight,A.property,B.property,C.property,D.property,F.property,
    H.property,J.property] at ht
  omega

theorem pair_space_finrank_le_two (U : Submodule (ZMod 2) Cocode)
    (hp : ∀ v ∈ U, v ≠ 0 → ∃ B : PointPair, v = pairVector B) :
    Module.finrank (ZMod 2) U ≤ 2 := by
  have hc := pair_space_card_le_four U hp
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hc
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc

end MathieuCode.J4Fusion
