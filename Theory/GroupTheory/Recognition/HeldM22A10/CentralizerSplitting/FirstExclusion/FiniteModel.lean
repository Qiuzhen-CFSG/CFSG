module
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.FirstExclusion.ModelCharacter
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.FirstExclusion.FiniteModel.Enumeration
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.FirstExclusion.FiniteModel.Certificates
-- Internal implementation access for the private cardinality bridge below;
-- the public definition and boundary of `squareRootCount` stay unchanged.
import all Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.FirstExclusion.Pattern

/-!
# Intrinsic facts for the first nonsplit Held model

The certified enumeration is an equivalence with the actual generated subgroup
`NonsplitModels.First`. Commutation with the two generators determines its
center, and the square table shows that every involution has trivial character.
The remaining fourth-order elements have one of six squares. Each square has a
64-element centralizer, in which the mark is distinguished among nonidentity
central elements by having 20 square roots instead of 12. Square-root counts
are invariant under automorphisms, so every automorphism fixes the mark.

This proves `modelFacts` for the character, root and mark fixed by
`ModelCharacter`. The private import of `Pattern` is intentional: the counting
bridge needs its hidden definition body, without exposing that body to clients.

Source problem: Huppert--Blackburn III, XII.1.18(b), p.314, citing Held,
J. Algebra 8 (1968), 436--449, DOI 10.1016/0021-8693(68)90054-9.
-/

namespace Theory.GroupTheory.HeldM22A10.FirstExclusion
open NonsplitModels FiniteModel

private theorem center_cases (w : First) (hw : w ∈ Subgroup.center First) :
    w = 1 ∨ w = mark := by
  obtain ⟨i, rfl⟩ := element_surjective w
  have hA := Subgroup.mem_center_iff.mp hw
    (⟨firstA, Subgroup.subset_closure (by simp)⟩ : First)
  have hB := Subgroup.mem_center_iff.mp hw
    (⟨firstB, Subgroup.subset_closure (by simp)⟩ : First)
  have ha : perm i * firstA = firstA * perm i := (congrArg Subtype.val hA).symm
  have hb : perm i * firstB = firstB * perm i := (congrArg Subtype.val hB).symm
  rcases center_test i ha hb with rfl | rfl
  · exact Or.inl element_zero
  · exact Or.inr element_mark

private theorem kills_involutions (w : First) (hw : w ^ 2 = 1) : character w = 1 := by
  obtain ⟨i, rfl⟩ := element_surjective w
  have hs : square i = 0 :=
    element_injective ((element_square i).trans (hw.trans element_zero.symm))
  change ((action i 0).val : ZMod 2) = 0
  rw [← ZMod.natCast_mod, involution_test i hs]
  rfl

private abbrev C (k : Fin 6) := Subgroup.centralizer ({element (targets k)} : Set First)

private theorem mem_C_iff (k : Fin 6) (i : Index) :
    inCentralizer k i ↔ element i ∈ C k := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (centralizer_test k i).trans (by
    constructor
    · intro h; exact Subtype.ext h.symm
    · intro h; exact (congrArg Subtype.val h).symm)

private noncomputable def centralizerEnumeration (k : Fin 6) :
    {i : Index // inCentralizer k i} ≃ C k :=
  enumeration.subtypeEquiv (mem_C_iff k)

set_option maxRecDepth 10000 in
private theorem count_roots (k : Fin 6) (z : C k) (i : Index)
    (hz : (z : First) = element i) : squareRootCount z = rootCount k i := by
  let e₁ := (Equiv.subtypeSubtypeEquivSubtypeInter
    (inCentralizer k) (fun j => square j = i)).symm
  have hp (j : {j : Index // inCentralizer k j}) :
      square j.val = i ↔ (centralizerEnumeration k j) ^ 2 = z := by
    constructor
    · intro h
      apply Subtype.ext
      change element j.val ^ 2 = z.val
      rw [← element_square, h, ← hz]
    · intro h
      have he : element j.val ^ 2 = z.val := congrArg Subtype.val h
      exact element_injective ((element_square j.val).trans (he.trans hz))
  let e₂ := (centralizerEnumeration k).subtypeEquiv
    (p := fun j => square j.val = i) (q := fun x => x ^ 2 = z) hp
  unfold squareRootCount rootCount
  exact (Nat.card_congr (e₁.trans e₂).symm).trans Nat.card_eq_fintype_card

private theorem centralizer_facts (k : Fin 6) :
    Nat.card (C k) = 64 ∧
    ∀ z : C k, (z : First) = mark → ∀ a : MulAut (C k), (a z : First) = mark := by
  constructor
  · exact (Nat.card_congr (centralizerEnumeration k).symm).trans
      (Nat.card_eq_fintype_card.trans (centralizer_card_test k))
  · intro z hz a
    have hcentral : z ∈ Subgroup.center (C k) := by
      apply Subgroup.mem_center_iff.mpr
      intro x
      apply Subtype.ext
      change x.val * z.val = z.val * x.val
      rw [hz]
      exact Subgroup.mem_center_iff.mp mark_central x.val
    have hne : z ≠ 1 := by
      intro h
      exact mark_ne_one (hz.symm.trans (congrArg Subtype.val h))
    have hcount : squareRootCount z = 20 :=
      (count_roots k z markIndex (hz.trans element_mark.symm)).trans (mark_count_test k)
    have hunique : ∀ x : C k, x ∈ Subgroup.center (C k) → x ≠ 1 →
        squareRootCount x = 20 → x = z := by
      intro x hx hx1 hxc
      obtain ⟨i, hi⟩ := element_surjective x.val
      have himem : inCentralizer k i := (mem_C_iff k i).mpr (hi.symm ▸ x.property)
      have hcomm (j : Fin 2) : perm (centerWitnesses k j) * perm i =
          perm i * perm (centerWitnesses k j) := by
        let y : C k := centralizerEnumeration k
          ⟨centerWitnesses k j, witness_mem_test k j⟩
        have hh := Subgroup.mem_center_iff.mp hx y
        have he : element (centerWitnesses k j) * x.val =
            x.val * element (centerWitnesses k j) := congrArg Subtype.val hh
        rw [← hi] at he
        exact congrArg Subtype.val he
      rcases center_restriction_test k i himem (hcomm 0) (hcomm 1) with
        h0 | hm | h1 | h2
      · exact (hx1 (Subtype.ext (hi.symm.trans ((congrArg element h0).trans element_zero)))).elim
      · apply Subtype.ext
        exact hi.symm.trans (((congrArg element hm).trans element_mark).trans hz.symm)
      · have hn := count_roots k x i hi.symm
        rw [hxc, h1, (other_count_test k).1] at hn
        omega
      · have hn := count_roots k x i hi.symm
        rw [hxc, h2, (other_count_test k).2] at hn
        omega
    exact (congrArg Subtype.val
      (fixed_of_squareRootCount z 20 hcentral hne hcount hunique a)).trans hz

/-- The first nonsplit permutation model satisfies all three intrinsic finite
facts required by the ambient exclusion criterion. -/
public theorem modelFacts : ModelFacts where
  center_cases := center_cases
  kills_involutions := kills_involutions
  square_centralizers w hχ h2 h4 hm := by
    obtain ⟨i, rfl⟩ := element_surjective w
    have hp : (action i 0).val % 2 = 0 := by
      have he : ((action i 0).val : ZMod 2) = 0 := hχ
      simpa only [ZMod.val_natCast, ZMod.val_zero] using congrArg ZMod.val he
    have hs2 : square i ≠ 0 := by
      intro h
      exact h2 ((element_square i).symm.trans ((congrArg element h).trans element_zero))
    have hs4 : square (square i) = 0 := by
      apply element_injective
      rw [element_square, element_square, ← pow_mul]
      exact h4.trans element_zero.symm
    have hsm : square i ≠ markIndex := by
      intro h
      exact hm ((element_square i).symm.trans ((congrArg element h).trans element_mark))
    obtain ⟨k, hk⟩ := square_test i hp hs2 hs4 hsm
    rw [← element_square, hk]
    exact centralizer_facts k

end Theory.GroupTheory.HeldM22A10.FirstExclusion
