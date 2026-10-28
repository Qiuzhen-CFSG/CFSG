module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.LiftRelations
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Finite.Linear

/-!
# Kernel corrections of elementary lifts of the selected rows

Each involutive lift has eight classes modulo the common fixed kernel. The
commutation equations allow exactly two tuples of classes. They differ by
conjugation by the native kernel mask eight or sixteen, respectively.
Linearity reduces the square-to-fixed-kernel calculation to 264 basis identities;
a checked commutation table tests the 4096 four-tuples. All four quotient
generators and their literal actions are retained. The same three-generator
calculation handles the omitted-generator (d′) row without assuming that
the omitted lift is present.
Source: Kleidman--Wilson (1988), Propositions 2.3.4(i) and 2.3.5.
-/

set_option Elab.async false
@[expose] public noncomputable section
namespace Janko4.LocalStructure.ElementaryEightGeometry.Sections
open Cardinality.QuotientCount.Image SylowCore SylowCore.Transport

def rows : Fin 2 → Fin 4 → Fin 11 → ℕ := ![![![1, 2, 4, 1125, 1151, 1099, 64, 946, 1385, 1645, 1030], ![1, 2, 822, 1248, 1994, 1099, 1064, 128, 1625, 1768, 235], ![1, 2, 1133, 1838, 863, 787, 883, 131, 1385, 1557, 806], ![1, 2, 4, 1874, 1865, 1912, 1819, 128, 1385, 1640, 857]], ![![1, 2, 4, 1125, 1151, 1099, 64, 946, 1385, 1645, 1030], ![1, 816, 4, 831, 1478, 1732, 1064, 946, 261, 517, 1467], ![1, 1131, 4, 1874, 1615, 534, 883, 2015, 256, 512, 607], ![1, 2, 4, 1874, 1865, 1912, 1819, 128, 1385, 1640, 857]]]
private def codeRows : Fin 2 → Fin 4 → Fin 11 → ℕ := ![![![0, 0, 4, 0, 0, 0, 2, 0, 1, 1, 2], ![0, 0, 0, 0, 4, 0, 0, 2, 1, 5, 0], ![0, 0, 0, 0, 4, 0, 2, 0, 1, 5, 2], ![0, 0, 4, 0, 0, 0, 2, 1, 0, 0, 2]], ![![0, 4, 0, 0, 0, 0, 2, 0, 1, 5, 2], ![0, 0, 0, 0, 0, 4, 0, 2, 1, 5, 4], ![0, 0, 0, 0, 0, 4, 2, 0, 1, 5, 6], ![0, 4, 0, 0, 0, 0, 2, 1, 0, 4, 2]]]
def representative : Fin 2 → Fin 4 → Fin 8 → Fin 2048 := ![![![0, 312, 64, 376, 4, 316, 68, 380], ![0, 292, 128, 420, 28, 312, 156, 440], ![0, 260, 96, 356, 28, 280, 124, 376], ![0, 128, 120, 248, 4, 132, 124, 252]], ![![0, 312, 64, 376, 2, 314, 66, 378], ![0, 266, 130, 392, 50, 312, 176, 442], ![0, 256, 74, 330, 50, 306, 120, 376], ![0, 128, 120, 248, 2, 130, 122, 250]]]
def twist : Fin 2 → Fin 2048 := ![8,16]
private def alternate : Fin 2 → Fin 4 → Fin 8 := ![![4, 2, 6, 0], ![4, 7, 1, 4]]

private theorem rows_spec : ∀ (r : Fin 2) (j : Fin 4) (k : Fin 11),
    rows r j k = pairLabel ((starElement (correctedIndex r j)).val (basisPair k).1)
      ((starElement (correctedIndex r j)).val (basisPair k).2) := by decide +kernel

theorem action_eq (r : Fin 2) (j : Fin 4) (m : ℕ) :
    starMask (starElement (correctedIndex r j)) m = maskImage (rows r j) m := by
  unfold starMask
  congr 1
  exact (funext (rows_spec r j)).symm

def xor (m n : Fin 2048) : Fin 2048 :=
  ⟨m.val ^^^ n.val,Nat.xor_lt_two_pow (n := 11) m.isLt n.isLt⟩

private def cosetIndex (r : Fin 2) (j : Fin 4) (m : Fin 2048) : Fin 8 :=
  ⟨maskImage (codeRows r j) m.val % 8,Nat.mod_lt _ (by decide)⟩

private def decodeRows : Fin 2 → Fin 4 → Fin 11 → ℕ := ![![![312, 64, 4, 0, 0, 0, 0, 0, 0, 0, 0], ![292, 128, 28, 0, 0, 0, 0, 0, 0, 0, 0], ![260, 96, 28, 0, 0, 0, 0, 0, 0, 0, 0], ![128, 120, 4, 0, 0, 0, 0, 0, 0, 0, 0]], ![![312, 64, 2, 0, 0, 0, 0, 0, 0, 0, 0], ![266, 130, 50, 0, 0, 0, 0, 0, 0, 0, 0], ![256, 74, 50, 0, 0, 0, 0, 0, 0, 0, 0], ![128, 120, 2, 0, 0, 0, 0, 0, 0, 0, 0]]]
private def betaRows : Fin 2 → Fin 4 → Fin 3 → Fin 11 → ℕ := ![![![![0, 2, 4, 0, 0, 0, 0, 0, 0, 816, 1129], ![0, 818, 945, 0, 0, 0, 0, 0, 0, 818, 1881], ![0, 1129, 124, 0, 0, 0, 0, 0, 0, 1130, 1882]], ![![0, 1131, 0, 0, 0, 0, 0, 1133, 0, 1131, 0], ![0, 3, 0, 0, 0, 0, 0, 128, 0, 817, 1128], ![0, 0, 0, 0, 0, 0, 0, 1045, 0, 1129, 819]], ![![0, 818, 0, 0, 0, 0, 6, 0, 0, 1881, 6], ![0, 0, 0, 0, 0, 0, 945, 0, 0, 1131, 131], ![0, 3, 0, 0, 0, 0, 124, 0, 0, 816, 1045]], ![![4, 6, 0, 0, 0, 0, 0, 0, 0, 6, 1133], ![945, 131, 0, 0, 0, 0, 0, 0, 0, 131, 1256], ![124, 1045, 0, 0, 0, 0, 0, 0, 0, 1830, 1045]]], ![![![0, 2, 4, 0, 0, 0, 0, 0, 0, 816, 1129], ![0, 1761, 818, 0, 0, 0, 0, 0, 0, 1491, 5], ![0, 261, 1129, 0, 0, 0, 0, 0, 0, 1626, 819]], ![![0, 0, 1133, 0, 0, 0, 0, 0, 2, 2, 0], ![0, 0, 5, 0, 0, 0, 0, 0, 443, 649, 1128], ![0, 0, 819, 0, 0, 0, 0, 0, 1631, 566, 819]], ![![0, 0, 1887, 0, 0, 0, 0, 0, 1885, 816, 0], ![0, 0, 5, 0, 0, 0, 0, 0, 1764, 1761, 818], ![0, 0, 5, 0, 0, 0, 0, 0, 256, 563, 1129]], ![![4, 6, 0, 0, 0, 0, 0, 0, 0, 6, 1133], ![818, 1491, 0, 0, 0, 0, 0, 0, 0, 1491, 823], ![1129, 1388, 0, 0, 0, 0, 0, 0, 0, 1631, 1129]]]]

private theorem mask_zero (r : Fin 11 → ℕ) : maskImage r 0 = 0 := by simp [maskImage]

private theorem hom_mask (f : ℕ → ℕ) (h0 : f 0 = 0)
    (hf : ∀ a b, f (a ^^^ b) = f a ^^^ f b) (r : Fin 11 → ℕ) (m : ℕ) :
    f (maskImage r m) = maskImage (fun i => f (r i)) m := by
  have hfold (xs : List ℕ) : f (xs.foldr Nat.xor 0) = (xs.map f).foldr Nat.xor 0 := by
    induction xs with
    | nil => exact h0
    | cons a xs ih => simp only [List.foldr_cons,List.map_cons,Nat.xor_eq,hf,ih]
  simp only [maskImage]
  rw [hfold,List.map_ofFn]
  congr 1
  congr 1
  funext i
  dsimp only [Function.comp_def]
  split <;> simp_all

private theorem xor_hom_ext (f g : ℕ → ℕ) (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hf : ∀ a b, f (a ^^^ b) = f a ^^^ f b)
    (hg : ∀ a b, g (a ^^^ b) = g a ^^^ g b)
    (hb : ∀ i : Fin 11, f (2^i.val) = g (2^i.val)) (m : Fin 2048) : f m.val = g m.val := by
  have hid : ∀ m : Fin 2048, maskImage (fun i : Fin 11 => 2^i.val) m.val = m.val := by decide +kernel
  rw [← hid m,hom_mask f hf0 hf,hom_mask g hg0 hg]
  congr 1
  funext i
  exact hb i

private theorem mask_lt (r : Fin 11 → ℕ) (n : ℕ) (hr : ∀ i, r i < 2^n) (m : ℕ) :
    maskImage r m < 2^n := by
  have hfold (xs : List ℕ) (hs : ∀ a ∈ xs, a < 2^n) : xs.foldr Nat.xor 0 < 2^n := by
    induction xs with
    | nil => exact pow_pos (by decide) _
    | cons a xs ih =>
      exact Nat.xor_lt_two_pow (hs a (by simp)) (ih (fun b hb => hs b (by simp [hb])))
  apply hfold
  intro a ha
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
  split
  · exact hr i
  · exact pow_pos (by decide) _

private def remainder (r : Fin 2) (j : Fin 4) (m : ℕ) : ℕ :=
  m ^^^ maskImage (decodeRows r j) (maskImage (codeRows r j) m)

private theorem reconstruction_basis : ∀ (r : Fin 2) (j : Fin 4) (t : Fin 3) (k : Fin 11),
    maskImage (rows r (t.castLE (by decide))) (remainder r j (2^k.val)) ^^^ remainder r j (2^k.val) =
      maskImage (betaRows r j t) (maskImage (rows r j) (2^k.val) ^^^ 2^k.val) := by decide +kernel

private theorem reconstruction (r : Fin 2) (j : Fin 4) (t : Fin 3) (m : Fin 2048) :
    maskImage (rows r (t.castLE (by decide))) (remainder r j m.val) ^^^ remainder r j m.val =
      maskImage (betaRows r j t) (maskImage (rows r j) m.val ^^^ m.val) := by
  refine xor_hom_ext
    (fun n => maskImage (rows r (t.castLE (by decide))) (remainder r j n) ^^^ remainder r j n)
    (fun n => maskImage (betaRows r j t) (maskImage (rows r j) n ^^^ n)) ?_ ?_ ?_ ?_ ?_ m
  · simp only [remainder,mask_zero,Nat.xor_self]
  · simp only [mask_zero,Nat.xor_self]
  · intro a b
    simp only [remainder,Janko4.TwoRank.Finite.maskImage_xor]
    ac_rfl
  · intro a b
    simp only [Janko4.TwoRank.Finite.maskImage_xor]
    ac_rfl
  · exact reconstruction_basis r j t

private theorem representative_decode : ∀ (r : Fin 2) (j : Fin 4) (k : Fin 8),
    (representative r j k).val = maskImage (decodeRows r j) k.val := by decide +kernel

private theorem code_bound : ∀ (r : Fin 2) (j : Fin 4) (i : Fin 11), codeRows r j i < 2^3 := by
  decide +kernel

private theorem coset_remainder (r : Fin 2) (j : Fin 4) (m : Fin 2048) :
    (xor m (representative r j (cosetIndex r j m))).val = remainder r j m.val := by
  change m.val ^^^ (representative r j (cosetIndex r j m)).val = _
  rw [representative_decode]
  change m.val ^^^ maskImage (decodeRows r j) (maskImage (codeRows r j) m.val % 8) = _
  have hlt : maskImage (codeRows r j) m.val < 8 := mask_lt _ 3 (code_bound r j) m.val
  rw [Nat.mod_eq_of_lt hlt]
  rfl

private theorem coset_fixed (r : Fin 2) (j : Fin 4) (m : Fin 2048)
    (hs : maskImage (rows r j) m.val = m.val) :
    fixedTest (r.castLE (by decide)) (xor m (representative r j (cosetIndex r j m))) := by
  intro t
  rw [coset_remainder]
  have ht : actionRows (r.castLE (by decide)) t = rows r (t.castLE (by decide)) := by
    fin_cases r <;> fin_cases t <;> rfl
  rw [ht]
  have hh := reconstruction r j t m
  rw [hs,Nat.xor_self,mask_zero] at hh
  simpa only [Nat.xor_assoc,Nat.xor_self,Nat.xor_zero,Nat.zero_xor] using
    congrArg (fun z => z ^^^ remainder r j m.val) hh

private theorem cast_unprimed (r : Fin 2) :
    unprimedRow (r.castLE (by decide)) = r.castLE (by decide) := by fin_cases r <;> rfl

private theorem fixed_action (r : Fin 2) (m : Fin 2048)
    (hm : fixedTest (r.castLE (by decide)) m) (j : Fin 4) :
    maskImage (rows r j) m.val = m.val := by
  rw [← action_eq]
  have he : starElement (correctedIndex r j) = pairRowGenerator (r.castLE (by decide)) j := by
    fin_cases r <;> fin_cases j <;> rfl
  rw [he]
  apply (fixedTest_iff_pairRow (r.castLE (by decide)) m).mp
    (by simpa only [cast_unprimed] using hm)
  exact pairRowGenerator_mem _ _

private theorem displacement_eq (rs : Fin 11 → ℕ) (m n : ℕ)
    (h : maskImage rs (m ^^^ n) = m ^^^ n) :
    maskImage rs m ^^^ m = maskImage rs n ^^^ n := by
  rw [Janko4.TwoRank.Finite.maskImage_xor] at h
  calc
    _ = (maskImage rs m ^^^ m) ^^^ (maskImage rs n ^^^ maskImage rs n) := by
      rw [Nat.xor_self,Nat.xor_zero]
    _ = (maskImage rs m ^^^ maskImage rs n) ^^^ (m ^^^ maskImage rs n) := by ac_rfl
    _ = (m ^^^ n) ^^^ (m ^^^ maskImage rs n) := by rw [h]
    _ = (m ^^^ m) ^^^ (maskImage rs n ^^^ n) := by ac_rfl
    _ = _ := by rw [Nat.xor_self,Nat.zero_xor]

private def commuteWords : Fin 2 → Fin 4 → Fin 4 → ℕ := ![![![18446744073709551615, 145702470557985, 4755801492135346305, 4938234448971309585], ![3458767812358569987, 18446744073709551615, 19140371435225105, 3512861310742367235], ![689050742987722761, 19140371435225105, 18446744073709551615, 1459492293735224385], ![4938234448971309585, 5787302130394727685, 1459492293735224385, 18446744073709551615]], ![![18446744073709551615, 145702470557985, 4755801492135346305, 4938234448971309585], ![3458767812358569987, 18446744073709551615, 2449958270874419217, 1297056483894165537], ![689050742987722761, 149606595856401, 18446744073709551615, 5766014897917808645], ![4938234448971309585, 6184752947205, 36592305322393665, 18446744073709551615]]]
private def compatible (r : Fin 2) (v : Fin 4 → Fin 8) : Prop :=
  ∀ i j, (commuteWords r i j).testBit (8 * (v i).val + (v j).val) = true

private theorem compatible_spec : ∀ (r : Fin 2) (i j : Fin 4) (a b : Fin 8),
    (commuteWords r i j).testBit (8 * a.val + b.val) = true ↔
      maskImage (rows r i) (representative r j b).val ^^^ (representative r j b).val =
        maskImage (rows r j) (representative r i a).val ^^^ (representative r i a).val := by
  decide +kernel

private theorem compatible_four_cases : ∀ (r : Fin 2) (a b c d : Fin 8),
    compatible r ![a,b,c,d] → ![a,b,c,d] = 0 ∨ ![a,b,c,d] = alternate r := by
  unfold compatible
  decide +kernel

private theorem compatible_cases (r : Fin 2) (v : Fin 4 → Fin 8) :
    compatible r v → v = 0 ∨ v = alternate r := by
  have hv : ![v 0,v 1,v 2,v 3] = v := by
    funext j
    fin_cases j <;> rfl
  simpa only [hv] using compatible_four_cases r (v 0) (v 1) (v 2) (v 3)

private theorem representative_zero : ∀ (r : Fin 2) (j : Fin 4),
    representative r j 0 = 0 := by decide +kernel

private def twistDisplacement (r : Fin 2) (j : Fin 4) : Fin 2048 :=
  xor (twist r) ⟨starMask (starElement (correctedIndex r j)) (twist r).val,starMask_lt _ _⟩

private theorem alternate_fixed : ∀ (r : Fin 2) (j : Fin 4),
    fixedTest (r.castLE (by decide)) (xor (representative r j (alternate r j)) (twistDisplacement r j)) := by
  decide +kernel

private theorem fixed_xor (r : Fin 4) (m n : Fin 2048)
    (hm : fixedTest r m) (hn : fixedTest r n) : fixedTest r (xor m n) := by
  intro j
  change maskImage (actionRows r j) (m.val ^^^ n.val) = m.val ^^^ n.val
  rw [Janko4.TwoRank.Finite.maskImage_xor,hm j,hn j]

/-- Every compatible four-tuple of involutive lift corrections becomes fixed
after conjugation by one of two explicitly specified kernel elements. -/
theorem correction (r : Fin 2) (m : Fin 4 → Fin 2048)
    (hs : ∀ j, maskImage (rows r j) (m j).val = (m j).val)
    (hc : ∀ i j, maskImage (rows r i) (m j).val ^^^ (m j).val =
      maskImage (rows r j) (m i).val ^^^ (m i).val) :
    ∃ k : Fin 2048, (k = 0 ∨ k = twist r) ∧ ∀ j,
      fixedTest (r.castLE (by decide))
        (xor (m j) (xor k ⟨starMask (starElement (correctedIndex r j)) k.val,starMask_lt _ _⟩)) := by
  let v : Fin 4 → Fin 8 := fun j => cosetIndex r j (m j)
  have hf (j : Fin 4) := coset_fixed r j (m j) (hs j)
  have hd (i j : Fin 4) : maskImage (rows r i) (m j).val ^^^ (m j).val =
      maskImage (rows r i) (representative r j (v j)).val ^^^ (representative r j (v j)).val :=
    displacement_eq _ _ _ (fixed_action r _ (hf j) i)
  have hcompat : compatible r v := by
    intro i j
    apply (compatible_spec r i j (v i) (v j)).mpr
    rw [← hd i j,← hd j i]
    exact hc i j
  rcases compatible_cases r v hcompat with hzero | halt
  · refine ⟨0,Or.inl rfl,?_⟩
    intro j
    have hv : representative r j (v j) = 0 := by rw [hzero]; exact representative_zero r j
    have hh := hf j
    change fixedTest (r.castLE (by decide)) (xor (m j) (representative r j (v j))) at hh
    rw [hv] at hh
    have hz : starMask (starElement (correctedIndex r j)) 0 = 0 := by
      rw [action_eq]
      simp [maskImage]
    simpa only [xor,Fin.val_zero,hz,Nat.xor_self,Nat.xor_zero] using hh
  · refine ⟨twist r,Or.inr rfl,?_⟩
    intro j
    have hh := hf j
    change fixedTest (r.castLE (by decide)) (xor (m j) (representative r j (v j))) at hh
    rw [halt] at hh
    have hsum := fixed_xor _ _ _ hh (alternate_fixed r j)
    have he : xor (xor (m j) (representative r j (alternate r j)))
        (xor (representative r j (alternate r j)) (twistDisplacement r j)) =
        xor (m j) (twistDisplacement r j) := by
      apply Fin.ext
      simp only [xor, Nat.xor_assoc, ← Nat.xor_assoc (representative r j (alternate r j)).val,
        Nat.xor_self,Nat.zero_xor]
    rw [he] at hsum
    exact hsum


private theorem compatible_three_cases : ∀ (a b c : Fin 8),
    (∀ i j : Fin 3, (commuteWords 1 i.succ j.succ).testBit
      (8 * (![a,b,c] i).val + (![a,b,c] j).val) = true) →
      ![a,b,c] = 0 ∨ ![a,b,c] = (fun j : Fin 3 => alternate 1 j.succ) := by
  decide +kernel

/-- The omitted-generator (d') row has the same two kernel correction
classes. The statement does not assume the missing lift exists. -/
theorem primed_correction (m : Fin 3 → Fin 2048)
    (hs : ∀ j, maskImage (rows 1 j.succ) (m j).val = (m j).val)
    (hc : ∀ i j, maskImage (rows 1 i.succ) (m j).val ^^^ (m j).val =
      maskImage (rows 1 j.succ) (m i).val ^^^ (m i).val) :
    ∃ k : Fin 2048, (k = 0 ∨ k = 16) ∧ ∀ j,
      fixedTest 1 (xor (m j)
        (xor k ⟨starMask (starElement (correctedIndex 1 j.succ)) k.val,starMask_lt _ _⟩)) := by
  let v : Fin 3 → Fin 8 := fun j => cosetIndex 1 j.succ (m j)
  have hf (j : Fin 3) := coset_fixed 1 j.succ (m j) (hs j)
  have hd (i j : Fin 3) : maskImage (rows 1 i.succ) (m j).val ^^^ (m j).val =
      maskImage (rows 1 i.succ) (representative 1 j.succ (v j)).val ^^^
        (representative 1 j.succ (v j)).val :=
    displacement_eq _ _ _ (fixed_action 1 _ (hf j) i.succ)
  have hcompat : ∀ i j : Fin 3, (commuteWords 1 i.succ j.succ).testBit
      (8 * (v i).val + (v j).val) = true := by
    intro i j
    apply (compatible_spec 1 i.succ j.succ (v i) (v j)).mpr
    rw [← hd i j,← hd j i]
    exact hc i j
  have hv : ![v 0,v 1,v 2] = v := by funext j; fin_cases j <;> rfl
  have hcases := compatible_three_cases (v 0) (v 1) (v 2)
  rw [hv] at hcases
  rcases hcases hcompat with hzero | halt
  · refine ⟨0,Or.inl rfl,?_⟩
    intro j
    have hh := hf j
    change fixedTest 1 (xor (m j) (representative 1 j.succ (v j))) at hh
    rw [hzero,Pi.zero_apply,representative_zero] at hh
    have hz : starMask (starElement (correctedIndex 1 j.succ)) 0 = 0 := by
      rw [action_eq]
      exact mask_zero _
    simpa only [xor,Fin.val_zero,hz,Nat.xor_self,Nat.xor_zero] using hh
  · refine ⟨twist 1,Or.inr rfl,?_⟩
    intro j
    have hh := hf j
    change fixedTest 1 (xor (m j) (representative 1 j.succ (v j))) at hh
    rw [halt] at hh
    have hsum := fixed_xor _ _ _ hh (alternate_fixed 1 j.succ)
    have he : xor (xor (m j) (representative 1 j.succ (alternate 1 j.succ)))
        (xor (representative 1 j.succ (alternate 1 j.succ)) (twistDisplacement 1 j.succ)) =
        xor (m j) (twistDisplacement 1 j.succ) := by
      apply Fin.ext
      simp only [xor,Nat.xor_assoc,← Nat.xor_assoc (representative 1 j.succ (alternate 1 j.succ)).val,
        Nat.xor_self,Nat.zero_xor]
    rw [he] at hsum
    exact hsum

end Janko4.LocalStructure.ElementaryEightGeometry.Sections
