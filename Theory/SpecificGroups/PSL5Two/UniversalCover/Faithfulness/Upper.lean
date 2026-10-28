module

public import Theory.SpecificGroups.PSL5Two.UniversalCover.Faithfulness.Setup

/-!
# Collection and faithfulness of the positive binary Steinberg roots

The positive-root subgroup of the actual presentation has a normal form with
one Boolean exponent for each of its ten roots. We collect in descending row
order: `(3,4), (2,3), (2,4), (1,2), (1,3), (1,4), (0,1), …, (0,4)`.
The chain relations keep each remaining tail invariant under conjugation by
the root being collected. In this order the transvection matrices have no
cross terms, so their strictly upper entries recover all ten exponents.
Thus the published matrix map is injective on `upperSubgroup`.

The same collection step removes any specified simple root. A chain of two
positive roots has height at least two, so it cannot recreate the omitted
simple root. This proves the literal `UpperFactorization` used by the Bruhat
argument, without assuming finiteness or faithfulness of the whole group.

Source: the type A₄ Steinberg presentation argument underlying the PSL₅(2)
case of Aschbacher–Smith I.1.3, printed p.407, and GLS98 §6.1. This module
supplies the upper-subgroup step, not the whole multiplier calculation.
-/

@[expose] public section

namespace Theory.SpecificGroups.PSL5Two.UniversalCover.Faithfulness

private def rootBit (r : Root) (b : Bool) : SteinbergGroup := if b then generator r else 1

private theorem split_closure (s t : Set Root) (r : Root)
    (hs : ∀ q ∈ s, q = r ∨ q ∈ t)
    (hc : ∀ q ∈ t, MulAut.conj (generator r) (generator q) ∈
      Subgroup.closure (generator '' t))
    {g : SteinbergGroup} (hg : g ∈ Subgroup.closure (generator '' s)) :
    ∃ (b : Bool) (v : SteinbergGroup), v ∈ Subgroup.closure (generator '' t) ∧
      g = rootBit r b * v := by
  let H := Subgroup.closure (generator '' t)
  have step (q : Root) (hq : q ∈ s) (z : SteinbergGroup)
      (hz : ∃ (b : Bool) (v : SteinbergGroup), v ∈ H ∧ z = rootBit r b * v) :
      ∃ (b : Bool) (v : SteinbergGroup), v ∈ H ∧
        generator q * z = rootBit r b * v := by
    obtain ⟨b, v, hv, rfl⟩ := hz
    rcases hs q hq with rfl | hq
    · cases b
      · exact ⟨true, v, hv, by simp [rootBit]⟩
      · exact ⟨false, v, hv, by simp [rootBit, generator_relations.mul_self_assoc]⟩
    · have hqH : generator q ∈ H := Subgroup.subset_closure ⟨q, hq, rfl⟩
      cases b
      · exact ⟨false, generator q * v, H.mul_mem hqH hv, by simp [rootBit]⟩
      · refine ⟨true, MulAut.conj (generator r) (generator q) * v,
          H.mul_mem (hc q hq) hv, ?_⟩
        simp only [rootBit, ↓reduceIte, MulAut.conj_apply,
          generator_relations.inv, mul_assoc, generator_relations.mul_self_assoc]
  induction hg using Subgroup.closure_induction_left with
  | one => exact ⟨false, 1, H.one_mem, by simp [rootBit]⟩
  | mul_left x hx z _ ih =>
    obtain ⟨q, hq, rfl⟩ := hx
    exact step q hq z ih
  | inv_mul_cancel x hx z _ ih =>
    obtain ⟨q, hq, rfl⟩ := hx
    rw [generator_relations.inv]
    exact step q hq z ih

private theorem positive_conj_mem (H : Subgroup SteinbergGroup) (r s : Root)
    (hr : r ∈ positiveRoots) (hs : s ∈ positiveRoots)
    (hmem : generator s ∈ H)
    (hchain : ∀ i j k : Fin 5, ∀ hij : i < j, ∀ hjk : j < k,
      (r = root i j (ne_of_lt hij) ∧ s = root j k (ne_of_lt hjk)) ∨
      (s = root i j (ne_of_lt hij) ∧ r = root j k (ne_of_lt hjk)) →
      generator (root i k (ne_of_lt (lt_trans hij hjk))) ∈ H) :
    MulAut.conj (generator r) (generator s) ∈ H := by
  obtain ⟨⟨i,j⟩, hij⟩ := r
  obtain ⟨⟨k, l⟩, hkl⟩ := s
  change i < j at hr
  change k < l at hs
  change MulAut.conj (generator (root i j hij)) (generator (root k l hkl)) ∈ H
  by_cases hjk : j = k
  · subst k
    rw [generator_relations.conj_chain i j l hij hkl (ne_of_lt (lt_trans hr hs))]
    exact H.mul_mem (hchain i j l hr hs (Or.inl ⟨rfl, rfl⟩)) hmem
  by_cases hli : l = i
  · subst l
    rw [generator_relations.conj_chain_reverse k i j hkl hij (ne_of_lt (lt_trans hs hr))]
    exact H.mul_mem (hchain k i j hs hr (Or.inr ⟨rfl, rfl⟩)) hmem
  rw [generator_relations.conj_distant _ _ hjk hli]
  exact hmem

/-- Removing any one simple root leaves the required two-coset factorization. -/
theorem upperFactorization : UpperFactorization := by
  intro a u
  have hc (q : Root) (hq : q ∈ positiveRoots \ {simpleRoot a}) :
      MulAut.conj (generator (simpleRoot a)) (generator q) ∈ upperComplement a := by
    apply positive_conj_mem (upperComplement a) (simpleRoot a) q (simpleRoot_positive a) hq.1
      (Subgroup.subset_closure ⟨q, hq, rfl⟩)
    intro i j k hij hjk _
    apply Subgroup.subset_closure
    refine ⟨root i k (ne_of_lt (lt_trans hij hjk)), ⟨lt_trans hij hjk, ?_⟩, rfl⟩
    change root i k _ ≠ simpleRoot a
    intro he
    have hi := congrArg (fun r : Root => r.val.1.val) he
    have hk := congrArg (fun r : Root => r.val.2.val) he
    change i.val = a.val at hi
    change k.val = a.val + 1 at hk
    have hij' : i.val < j.val := hij
    have hjk' : j.val < k.val := hjk
    omega
  obtain ⟨b, v, hv, he⟩ := split_closure positiveRoots
    (positiveRoots \ {simpleRoot a}) (simpleRoot a)
    (fun q hq => by
      by_cases he : q = simpleRoot a
      · exact Or.inl he
      · exact Or.inr ⟨hq, he⟩) hc u.property
  exact ⟨b, ⟨v, hv⟩, he⟩

/-- A chain involving the first root stays among the remaining roots. -/
private def chainTail (r : Root) (l : List Root) (i j k : Fin 5) : Prop :=
  i < j → j < k →
    (r.val = (i, j) ∧ (j, k) ∈ l.map Subtype.val) ∨
    (r.val = (j, k) ∧ (i, j) ∈ l.map Subtype.val) →
      (i, k) ∈ l.map Subtype.val

private instance (r : Root) (l : List Root) (i j k : Fin 5) :
    Decidable (chainTail r l i j k) := by
  unfold chainTail
  infer_instance

private def collectionOrder : List Root → Prop
  | [] => True
  | r :: l => (r ∈ positiveRoots) ∧
      (∀ q ∈ l, q ∈ positiveRoots) ∧
      (∀ i j k : Fin 5, chainTail r l i j k) ∧ collectionOrder l

private instance (l : List Root) : Decidable (collectionOrder l) := by
  induction l with
  | nil => exact isTrue trivial
  | cons r l ih =>
    change Decidable (_ ∧ _ ∧ _ ∧ collectionOrder l)
    letI := ih
    unfold positiveRoots
    infer_instance

private def collectedWord (l : List Root) (b : Root → Bool) : SteinbergGroup :=
  (l.map (fun r => rootBit r (b r))).prod

/-- Successively remove the first root by the involution and conjugation relations. -/
private theorem exists_collectedWord (l : List Root) (hn : l.Nodup) (ho : collectionOrder l)
    {g : SteinbergGroup} (hg : g ∈ Subgroup.closure (generator '' {r | r ∈ l})) :
    ∃ b : Root → Bool, g = collectedWord l b := by
  induction l generalizing g with
  | nil =>
    have hg' : g = 1 := by simpa using hg
    exact ⟨fun _ => false, hg'⟩
  | cons r l ih =>
    have hn' := List.nodup_cons.mp hn
    obtain ⟨hr, hpos, hchain, ho'⟩ := ho
    have hc (q : Root) (hq : q ∈ l) :
        MulAut.conj (generator r) (generator q) ∈
          Subgroup.closure (generator '' {s | s ∈ l}) := by
      apply positive_conj_mem (Subgroup.closure (generator '' {s | s ∈ l})) r q
        hr (hpos q hq) (Subgroup.subset_closure ⟨q, hq, rfl⟩)
      intro i j k hij hjk hp
      apply Subgroup.subset_closure
      refine ⟨root i k (ne_of_lt (lt_trans hij hjk)), ?_, rfl⟩
      apply (List.mem_map_of_injective Subtype.val_injective).mp
      apply hchain i j k hij hjk
      rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, List.mem_map_of_mem hq⟩
      · exact Or.inr ⟨rfl, List.mem_map_of_mem hq⟩
    obtain ⟨e, v, hv, he⟩ := split_closure {s | s ∈ r :: l} {s | s ∈ l} r
      (by intro q hq; exact List.mem_cons.mp hq) hc hg
    obtain ⟨b, rfl⟩ := ih hn'.2 ho' hv
    refine ⟨Function.update b r e, ?_⟩
    rw [he]
    simp only [collectedWord, List.map_cons, List.prod_cons, Function.update_self]
    congr 1
    congr 1
    apply List.map_congr_left
    intro q hq
    rw [Function.update_of_ne (by intro he; subst q; exact hn'.1 hq)]

/-- Descending row order eliminates cross terms in the matrix product. -/
private def orderedRoots : List Root :=
  [root 3 4 (by decide), root 2 3 (by decide), root 2 4 (by decide),
   root 1 2 (by decide), root 1 3 (by decide), root 1 4 (by decide),
   root 0 1 (by decide), root 0 2 (by decide), root 0 3 (by decide),
   root 0 4 (by decide)]

private theorem orderedRoots_nodup : orderedRoots.Nodup := by decide

private theorem orderedRoots_order : collectionOrder orderedRoots := by decide

private theorem orderedRoots_mem (r : Root) : r ∈ orderedRoots ↔ r ∈ positiveRoots := by
  obtain ⟨⟨i, j⟩, hij⟩ := r
  fin_cases i <;> fin_cases j <;> simp_all [orderedRoots, positiveRoots, root]

private theorem upper_exists_collectedWord (u : upperSubgroup) :
    ∃ b : Root → Bool, u.val = collectedWord orderedRoots b := by
  apply exists_collectedWord orderedRoots orderedRoots_nodup orderedRoots_order
  simpa only [orderedRoots_mem, Set.ofPred_mem_eq, upperSubgroup] using u.property

open Matrix.SpecialLinearGroup

private theorem matrixMap_rootBit (r : Root) (b : Bool) :
    (matrixMap (rootBit r b) : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
      Matrix.transvection r.val.1 r.val.2 (if b then 1 else 0) := by
  cases b <;> simp [rootBit, matrixRoot, transvection_coe, Matrix.transvection]

private theorem transvection_mul_entry (i j a d : Fin 5) (c : ZMod 2)
    (M : Matrix (Fin 5) (Fin 5) (ZMod 2)) :
    (Matrix.transvection i j c * M) a d =
      M a d + if a = i then c * M j d else 0 := by
  by_cases h : a = i
  · subst a; simp
  · simp [Matrix.transvection_mul_apply_of_ne _ _ _ _ h, h]

private theorem transvection_entry (i j a d : Fin 5) (c : ZMod 2) :
    Matrix.transvection i j c a d =
      (if a = d then 1 else 0) + (if a = i ∧ d = j then c else 0) := by
  simp [Matrix.transvection, Matrix.single_apply, Matrix.one_apply, eq_comm]

/-- Each strictly upper entry reads off exactly its Boolean exponent. -/
private theorem matrixMap_collectedWord_entry (b : Root → Bool) (r : Root)
    (hr : r ∈ positiveRoots) :
    (matrixMap (collectedWord orderedRoots b) : Matrix (Fin 5) (Fin 5) (ZMod 2))
      r.val.1 r.val.2 = if b r then 1 else 0 := by
  have hm := (orderedRoots_mem r).mpr hr
  simp only [orderedRoots, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [collectedWord, orderedRoots, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, map_mul, map_one, coe_mul, coe_one, matrixMap_rootBit, root]
    norm_num [transvection_mul_entry, transvection_entry, Matrix.one_apply, Fin.ext_iff]
    rfl

private theorem bool_eq_of_bit_eq {b c : Bool}
    (h : (if b then 1 else 0 : ZMod 2) = if c then 1 else 0) : b = c := by
  cases b <;> cases c <;> simp_all

/-- The literal matrix representation is faithful on the subgroup generated
by the ten positive roots of the published presentation. -/
theorem matrixMap_upper_injective :
    Function.Injective (matrixMap.comp upperSubgroup.subtype) := by
  intro u v huv
  obtain ⟨b, hb⟩ := upper_exists_collectedWord u
  obtain ⟨c, hc⟩ := upper_exists_collectedWord v
  change matrixMap u.val = matrixMap v.val at huv
  rw [hb, hc] at huv
  have he (r : Root) (hr : r ∈ orderedRoots) : b r = c r := by
    apply bool_eq_of_bit_eq
    have hm := congrArg (fun A : SL => (A : Matrix (Fin 5) (Fin 5) (ZMod 2))
      r.val.1 r.val.2) huv
    rwa [matrixMap_collectedWord_entry b r ((orderedRoots_mem r).mp hr),
      matrixMap_collectedWord_entry c r ((orderedRoots_mem r).mp hr)] at hm
  apply Subtype.ext
  rw [hb, hc]
  unfold collectedWord
  congr 1
  apply List.map_congr_left
  intro r hr
  rw [he r hr]

end Theory.SpecificGroups.PSL5Two.UniversalCover.Faithfulness
