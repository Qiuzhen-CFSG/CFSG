module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions.Images
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Finite.Linear

/-!
# Exhaustive native displacement geometry in the two image positions

The eleven action rows determine each displacement map. Annihilating linear
forms exclude every image coordinate except three in each position. Each
remaining displacement has thirty-two explicit coordinates. In the first
position distinct displacement spaces intersect only in the native pair;
in the second position all three spaces coincide. The permitted image
coordinates form two actual elementary four-groups in the original Mathieu
image, not group-family tags.

The certificates use the existing ATLAS star action. Reconstruction and
annihilation are checked on eleven basis vectors and extended by linearity,
avoiding repeated exhaustive evaluation of all eleven-bit inputs.
Source: Kleidman--Wilson (1988), Section 2.1, p.489. These are necessary
actual-lift restrictions, with no assertion of full centralizer placement.
-/

set_option Elab.async false
public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions
open Cardinality KernelCount QuotientCount.Image
open Simplicity.Max1Fusion Simplicity.Max1Fusion.QuotientInvolutions
open NativePair NativePair.Stabilizer LinearFive InvolutionCentralizers.Second
open M22Images.KernelAction InvolutionCentralizers.Second.FiveAction
namespace DisplacementActions
private def rows : Fin 2 → Fin 16 → Fin 11 → ℕ := ![![![1,2,4,8,16,32,64,128,256,512,1024],![313,1491,1261,112,336,280,64,135,256,1961,1151],![2,1,4,1467,1440,1418,256,946,64,857,1640],![1491,313,1261,298,1248,91,256,949,64,1776,766],![1637,445,2015,898,1214,1795,64,135,256,50,1738],![1882,1131,822,1021,1534,1596,64,128,256,1435,1714],![445,1637,2015,170,78,1394,256,949,64,43,569],![1131,1882,822,1084,270,164,256,946,64,1410,1704],![523,1761,1261,637,1158,1732,71,135,263,1686,667],![819,816,4,517,1478,2044,71,128,263,831,740],![1761,523,1261,1998,1503,1927,263,949,71,806,243],![816,819,4,863,1183,598,263,946,71,1679,1125],![1128,1881,822,503,47,480,71,128,263,1187,81],![1367,655,2015,392,367,223,71,135,263,266,41],![1881,1128,822,735,54,1912,263,946,71,83,1186],![655,1367,2015,1609,374,686,263,949,71,1530,51]],![![1,2,4,8,16,32,64,128,256,512,1024],![1,2,1261,302,1503,382,1527,945,1207,806,766],![313,1491,4,342,1183,70,1527,1887,1207,1679,1640],![313,1491,1261,112,336,280,64,135,256,1961,1151],![2,1,4,1467,1440,1418,256,946,64,857,1640],![2,1,1261,116,1158,1236,1207,131,1527,1686,1151],![1491,313,4,1253,1478,261,1207,1133,1527,831,1024],![1491,313,1261,298,1248,91,256,949,64,1776,766],![523,1761,4,1970,1440,883,281,1887,89,857,1125],![523,1761,1261,637,1158,1732,71,135,263,1686,667],![819,816,4,517,1478,2044,71,128,263,831,740],![819,816,1261,1994,1248,587,281,945,89,1776,243],![1761,523,4,1768,16,560,89,1133,281,512,740],![1761,523,1261,1998,1503,1927,263,949,71,806,243],![816,819,4,863,1183,598,263,946,71,1679,1125],![816,819,1261,633,336,2017,89,131,281,1961,667]]]

private theorem rows_spec : ∀ (r : Fin 2) (i : Fin 16) (j : Fin 11),
    rows r i j = pairLabel ((element (blockIndex (r.castLE (by decide)) i)).val (basisPair j).1)
      ((element (blockIndex (r.castLE (by decide)) i)).val (basisPair j).2) := by decide +kernel

private theorem action_eq (r : Fin 2) (i : Fin 16) (m : ℕ) :
    SylowCore.starMask (element (blockIndex (r.castLE (by decide)) i)) m = maskImage (rows r i) m := by
  unfold SylowCore.starMask
  congr 1
  exact (funext (rows_spec r i)).symm

@[expose] def pureIndex : Fin 2 → Fin 3 → Fin 96 := ![![12,64,88],![12,57,79]]
private def goodCoordinate : Fin 2 → Fin 3 → Fin 16 := ![![2,12,14],![4,11,15]]

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


private def annihilator : Fin 2 → Fin 16 → Fin 11 → ℕ := ![![![1,0,0,0,0,0,0,0,0,0,0],![0,1,1,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0],![1,1,1,0,1,1,0,0,0,0,0],![1,0,1,1,0,0,1,0,1,0,0],![1,1,0,0,0,0,1,1,1,0,0],![0,1,0,0,1,1,0,0,0,0,0],![1,0,0,0,0,0,0,0,0,0,0],![0,1,1,1,0,0,1,0,0,0,0],![1,0,1,0,0,0,1,0,0,0,0],![0,0,1,0,0,1,1,0,0,0,0],![0,0,1,1,0,0,1,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0],![1,1,0,1,0,0,1,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0],![1,0,0,0,0,1,1,0,0,0,0]],![![1,0,0,0,0,0,0,0,0,0,0],![0,1,1,0,0,0,0,0,0,0,0],![0,1,1,0,0,0,0,0,0,0,0],![0,1,1,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0],![0,0,1,0,1,0,0,0,0,0,0],![1,0,0,0,0,1,0,0,0,0,0],![1,1,1,0,1,1,0,0,0,0,0],![1,1,1,1,0,0,0,0,0,0,0],![0,1,1,1,0,0,1,0,0,0,0],![1,0,1,0,0,0,1,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0],![0,1,0,0,0,0,0,0,0,0,0],![0,0,1,0,0,1,1,0,0,0,0],![0,0,1,1,0,0,1,0,0,0,0],![0,0,0,0,0,0,0,0,0,0,0]]]

private theorem annihilator_basis : ∀ (r : Fin 2) (i : Fin 16) (j : Fin 11),
    maskImage (annihilator r i) (maskImage (rows r i) (2^j.val) ^^^ 2^j.val) = 0 := by
  decide +kernel

private theorem annihilator_zero (r : Fin 2) (i : Fin 16) (m : Fin 2048) :
    maskImage (annihilator r i) (maskImage (rows r i) m.val ^^^ m.val) = 0 := by
  refine xor_hom_ext (fun n => maskImage (annihilator r i)
    (maskImage (rows r i) n ^^^ n)) (fun _ => 0) ?_ ?_ ?_ ?_ ?_ m
  · simp only [mask_zero,Nat.xor_self]
  · rfl
  · intro a b
    simp only [Janko4.TwoRank.Finite.maskImage_xor]
    ac_rfl
  · intro a b
    exact (Nat.xor_self 0).symm
  · exact annihilator_basis r i

private theorem sieve_small : ∀ (r : Fin 2) (i : Fin 16),
    maskImage (annihilator r i) 818 = 0 →
    maskImage (annihilator r i) 1449 = 0 →
    ∃ j : Fin 3, i = goodCoordinate r j := by decide +kernel

private theorem sieve (r : Fin 2) (i : Fin 16)
    (h0 : ∃ n : Fin 2048, maskImage (rows r i) n.val ^^^ n.val = 818)
    (h1 : ∃ n : Fin 2048, maskImage (rows r i) n.val ^^^ n.val = 1449) :
    ∃ j : Fin 3, i = goodCoordinate r j := by
  obtain ⟨m,hm⟩ := h0
  obtain ⟨n,hn⟩ := h1
  apply sieve_small r i
  · simpa only [hm] using annihilator_zero r i m
  · simpa only [hn] using annihilator_zero r i n

theorem image_selection (r : Fin 2) (i : Fin 16)
    (h0 : ∃ n : Fin 2048, SylowCore.starMask
      (element (blockIndex (r.castLE (by decide)) i)) n.val ^^^ n.val = 818)
    (h1 : ∃ n : Fin 2048, SylowCore.starMask
      (element (blockIndex (r.castLE (by decide)) i)) n.val ^^^ n.val = 1449) :
    ∃ j : Fin 3, blockIndex (r.castLE (by decide)) i = pureIndex r j := by
  obtain ⟨m,hm⟩ := h0
  obtain ⟨n,hn⟩ := h1
  rw [action_eq] at hm hn
  obtain ⟨j,rfl⟩ := sieve r i ⟨m,hm⟩ ⟨n,hn⟩
  refine ⟨j,?_⟩
  have hh : ∀ (r : Fin 2) (j : Fin 3),
      blockIndex (r.castLE (by decide)) (goodCoordinate r j) = pureIndex r j := by decide +kernel
  exact hh r j

/-- The three displacement spaces in each certified image position. -/
@[expose] def displacementMask : Fin 2 → Fin 3 → Fin 32 → ℕ := ![![![0,3,25,26,320,323,345,346,616,619,625,626,808,811,817,818,1257,1258,1264,1267,1449,1450,1456,1459,1665,1666,1688,1691,1985,1986,2008,2011],![0,7,56,63,448,455,504,511,714,717,754,757,778,781,818,821,1105,1110,1129,1134,1425,1430,1449,1454,1691,1692,1699,1700,1883,1884,1891,1892],![0,38,132,162,327,353,451,485,595,629,727,753,788,818,912,950,1100,1130,1224,1262,1291,1325,1423,1449,1567,1593,1691,1725,1880,1918,2012,2042]],![![0,3,25,26,320,323,345,346,616,619,625,626,808,811,817,818,1257,1258,1264,1267,1449,1450,1456,1459,1665,1666,1688,1691,1985,1986,2008,2011],![0,3,25,26,320,323,345,346,616,619,625,626,808,811,817,818,1257,1258,1264,1267,1449,1450,1456,1459,1665,1666,1688,1691,1985,1986,2008,2011],![0,3,25,26,320,323,345,346,616,619,625,626,808,811,817,818,1257,1258,1264,1267,1449,1450,1456,1459,1665,1666,1688,1691,1985,1986,2008,2011]]]
private def selectedRows : Fin 2 → Fin 3 → Fin 11 → ℕ := ![![![2,1,4,1467,1440,1418,256,946,64,857,1640],![1128,1881,822,503,47,480,71,128,263,1187,81],![1881,1128,822,735,54,1912,263,946,71,83,1186]],![![2,1,4,1467,1440,1418,256,946,64,857,1640],![819,816,1261,1994,1248,587,281,945,89,1776,243],![816,819,1261,633,336,2017,89,131,281,1961,667]]]
private theorem selected_rows_spec : ∀ (r : Fin 2) (i : Fin 3) (j : Fin 11),
    selectedRows r i j = pairLabel ((element (pureIndex r i)).val (basisPair j).1)
      ((element (pureIndex r i)).val (basisPair j).2) := by decide +kernel

private theorem selected_action (r : Fin 2) (i : Fin 3) (m : ℕ) :
    SylowCore.starMask (element (pureIndex r i)) m = maskImage (selectedRows r i) m := by
  unfold SylowCore.starMask
  congr 1
  exact (funext (selected_rows_spec r i)).symm

private def code : Fin 2 → Fin 3 → Fin 11 → ℕ := ![![![1,1,0,23,22,21,4,15,4,6,8],![18,28,14,7,3,4,1,0,1,26,16],![28,17,13,10,1,28,4,13,4,8,3]],![![1,1,0,23,22,21,4,15,4,6,8],![15,15,16,29,18,9,6,14,6,18,19],![14,14,16,10,4,28,2,1,2,20,27]]]
private def decode : Fin 2 → Fin 3 → Fin 11 → ℕ := ![![![3,25,320,616,1257,0,0,0,0,0,0],![7,56,448,714,1105,0,0,0,0,0,0],![38,132,327,595,1100,0,0,0,0,0,0]],![![3,25,320,616,1257,0,0,0,0,0,0],![3,25,320,616,1257,0,0,0,0,0,0],![3,25,320,616,1257,0,0,0,0,0,0]]]
private theorem displacement_basis : ∀ (r : Fin 2) (i : Fin 3) (j : Fin 11),
    maskImage (selectedRows r i) (2^j.val) ^^^ 2^j.val =
      maskImage (decode r i) (maskImage (code r i) (2^j.val)) := by decide +kernel
private theorem code_lt : ∀ (r : Fin 2) (i : Fin 3) (j : Fin 11), code r i j < 2^5 := by decide +kernel
private theorem decode_table : ∀ (r : Fin 2) (i : Fin 3) (j : Fin 32),
    maskImage (decode r i) j.val = displacementMask r i j := by decide +kernel

private theorem displacement_cover (r : Fin 2) (i : Fin 3) (n : Fin 2048) :
    ∃ j : Fin 32, maskImage (selectedRows r i) n.val ^^^ n.val = displacementMask r i j := by
  have h : maskImage (selectedRows r i) n.val ^^^ n.val =
      maskImage (decode r i) (maskImage (code r i) n.val) := by
    refine xor_hom_ext (fun m => maskImage (selectedRows r i) m ^^^ m)
      (fun m => maskImage (decode r i) (maskImage (code r i) m)) ?_ ?_ ?_ ?_ ?_ n
    · simp only [mask_zero,Nat.xor_self]
    · simp only [mask_zero]
    · intro a b
      simp only [Janko4.TwoRank.Finite.maskImage_xor]
      ac_rfl
    · intro a b
      simp only [Janko4.TwoRank.Finite.maskImage_xor]
    · exact displacement_basis r i
  let j : Fin 32 := ⟨maskImage (code r i) n.val,mask_lt _ 5 (code_lt r i) _⟩
  exact ⟨j,h.trans (decode_table r i j)⟩

/-- Every displacement is one of the thirty-two displayed masks. -/
theorem displacement_coordinates (r : Fin 2) (i : Fin 3) (n : Fin 2048) :
    ∃ j : Fin 32, SylowCore.starMask (element (pureIndex r i)) n.val ^^^ n.val =
      displacementMask r i j := by
  rw [selected_action]
  exact displacement_cover r i n

/-- Distinct exceptional-position displacements meet in exactly the native
pair's four coordinates. The reverse inclusion is certified separately. -/
theorem exceptional_intersection : ∀ (i j : Fin 3) (k l : Fin 32),
    i ≠ j → displacementMask 0 i k = displacementMask 0 j l →
      displacementMask 0 i k = 0 ∨ displacementMask 0 i k = 818 ∨
      displacementMask 0 i k = 1449 ∨ displacementMask 0 i k = 1691 := by decide +kernel

/-- In the common position all three displacements are the same space. -/
theorem common_displacement (i : Fin 3) : displacementMask 1 i = displacementMask 0 0 := by
  revert i
  decide +kernel

/-- Each displayed displacement has order thirty-two in binary coordinates. -/
theorem displacement_injective : ∀ (r : Fin 2) (i : Fin 3),
    Function.Injective (displacementMask r i) := by decide +kernel

/-- The two order-four subgroups left by the actual-lift restriction. -/
@[expose] def pureBlock (r : Fin 2) : Subgroup StarGroup :=
  closure (Set.range (fun j : Fin 2 => element (pureIndex r j.castSucc)))

private def fourIndex : Fin 2 → Fin 4 → Fin 96 := ![![0,12,64,88],![0,12,57,79]]

private theorem pure_span : ∀ (r : Fin 2) (i : Fin 4),
    binaryProduct (fun j : Fin 2 => element (pureIndex r j.castSucc))
      (fun j => i.val.testBit j.val) = element (fourIndex r i) := by
  intro r i
  apply Subtype.ext
  revert r i
  decide +kernel
private theorem pure_square : ∀ (r : Fin 2) (j : Fin 2),
    element (pureIndex r j.castSucc) * element (pureIndex r j.castSucc) = 1 := by
  intro r j
  apply Subtype.ext
  revert r j
  decide +kernel
private theorem pure_commute : ∀ (r : Fin 2) (i j : Fin 2),
    Commute (element (pureIndex r i.castSucc)) (element (pureIndex r j.castSucc)) := by
  intro r i j
  apply Subtype.ext
  revert r i j
  decide +kernel

private theorem pure_coordinates (r : Fin 2) (p : StarGroup) :
    p ∈ pureBlock r ↔ ∃ i : Fin 4, element (fourIndex r i) = p := by
  constructor
  · intro hp
    obtain ⟨v,rfl⟩ := (mem_closure_iff_binaryProduct _ (pure_square r) (pure_commute r) p).mp hp
    have hh : ∀ v : Fin 2 → Bool, ∃ i : Fin 4, (fun j : Fin 2 => i.val.testBit j.val) = v := by decide +kernel
    obtain ⟨i,rfl⟩ := hh v
    exact ⟨i,(pure_span r i).symm⟩
  · rintro ⟨i,rfl⟩
    rw [← pure_span]
    exact binaryProduct_mem _ _ _ (fun j => subset_closure ⟨j,rfl⟩)

theorem pureIndex_mem (r : Fin 2) (i : Fin 3) : element (pureIndex r i) ∈ pureBlock r := by
  apply (pure_coordinates r _).mpr
  refine ⟨i.succ,?_⟩
  congr 1
  have hh : ∀ (r : Fin 2) (i : Fin 3), fourIndex r i.succ = pureIndex r i := by decide +kernel
  exact hh r i

theorem pureBlock_card (r : Fin 2) : Nat.card (pureBlock r) = 4 := by
  let f : Fin 4 → pureBlock r := fun i => ⟨element (fourIndex r i),(pure_coordinates _ _).mpr ⟨i,rfl⟩⟩
  have hj : Function.Injective (fourIndex r) := by revert r; decide +kernel
  have hi : Function.Injective f := fun _ _ h => hj (element_injective (congrArg Subtype.val h))
  have hs : Function.Surjective f := by
    intro p
    obtain ⟨i,hi⟩ := (pure_coordinates r p.val).mp p.property
    exact ⟨i,Subtype.ext hi⟩
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hi,hs⟩),Nat.card_fin]

end DisplacementActions
end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions
