module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.M22Images.KernelAction

/-!
# The orthogonal kernel of the sextet lift

The thirty non-octad four-groups in the native sextet E16 have fixed kernel
spaces of dimension five. Linear reconstruction, checked on eleven basis
vectors, expresses each fixed mask as an even subset of the fixed tetrad,
or as its sum with a swapped pair. The actual residual character excludes
the latter masks for a zero-form elementary lift. Its kernel intersection
therefore lies in the explicitly embedded group of order eight.

Only the literal non-octad pair indices and E8 mask coordinates expose their
bodies, for the exhaustive image calculation and native subgroup embedding.
The reconstruction matrices remain private. Source: Kleidman--Wilson,
The Maximal Subgroups of J4 (1988), Proposition 2.2.2(iii), pp.490--491.
-/

public noncomputable section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.M22Images.SextetKernel
open Cardinality.QuotientCount.Image Sporadic.Mathieu M23Geometry FusionCertificate ElementarySylow
private def starTable : Fin 16 → Fin 24 → Fin 24 := ![![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23],![0,3,15,1,23,5,21,7,8,12,19,17,9,13,14,2,18,11,16,10,20,6,22,4],![0,16,12,18,21,5,23,7,8,15,11,10,2,13,14,9,1,19,3,17,20,4,22,6],![0,18,9,16,6,5,4,7,8,2,17,19,15,13,14,12,3,10,1,11,20,23,22,21],![7,18,12,16,23,5,21,0,8,15,10,11,2,13,14,9,3,17,1,19,22,6,20,4],![7,16,9,18,4,5,6,0,8,2,19,17,15,13,14,12,1,11,3,10,22,21,20,23],![7,3,2,1,6,5,4,0,8,9,11,10,12,13,14,15,18,19,16,17,22,23,20,21],![7,1,15,3,21,5,23,0,8,12,17,19,9,13,14,2,16,10,18,11,22,4,20,6],![22,3,9,1,21,5,23,20,8,2,10,11,15,13,14,12,18,17,16,19,7,4,0,6],![22,1,12,3,6,5,4,20,8,15,19,17,2,13,14,9,16,11,18,10,7,23,0,21],![22,18,15,16,4,5,6,20,8,12,11,10,9,13,14,2,3,19,1,17,7,21,0,23],![22,16,2,18,23,5,21,20,8,9,17,19,12,13,14,15,1,10,3,11,7,6,0,4],![20,16,15,18,6,5,4,22,8,12,10,11,9,13,14,2,1,17,3,19,0,23,7,21],![20,18,2,16,21,5,23,22,8,9,19,17,12,13,14,15,3,11,1,10,0,4,7,6],![20,1,9,3,23,5,21,22,8,2,11,10,15,13,14,12,16,19,18,17,0,6,7,4],![20,3,12,1,4,5,6,22,8,15,17,19,2,13,14,9,18,10,16,11,0,21,7,23]]
private theorem starTable_spec : ∀ (i : Fin 16) (x : Fin 24),
  StarOrderCertificate.relabel.symm (CommonFour.extendPoint (pointTable (candidateIndex 0 i)) (StarOrderCertificate.relabel x)) = starTable i x := by decide +kernel
private def rows : Fin 16 → Fin 11 → ℕ := ![![1,2,4,8,16,32,64,128,256,512,1024],![30,1020,1838,1645,702,367,750,1099,256,1333,2017],![1058,1912,1553,1874,841,32,598,1484,256,54,1881],![1394,1158,116,120,168,367,439,263,256,1795,1527],![1341,1576,1838,1570,841,32,598,1212,256,89,1625],![1133,1494,4,71,168,367,439,312,256,1571,1271],![81,29,116,55,16,32,64,191,256,623,1280],![78,995,1553,1821,702,367,750,1339,256,1045,1761],![2019,165,1553,480,168,32,439,464,79,1349,522],![2044,532,116,1738,841,367,598,1307,79,831,164],![655,2015,4,1722,702,32,750,1491,79,1596,28],![991,1390,1838,223,16,367,64,280,79,70,1021],![735,1679,116,1994,702,32,750,1187,79,1820,83],![911,1086,1553,224,16,367,64,295,79,41,946],![1788,186,1838,479,168,32,439,495,79,1125,581],![1763,523,4,1978,841,367,598,1131,79,848,235]]
private theorem rows_spec : ∀ (i : Fin 16) (j : Fin 11),
  pairLabel (starTable i (basisPair j).1) (starTable i (basisPair j).2) = rows i j := by decide +kernel
@[expose] def nonOctadPair : Fin 30 → Fin 2 → Fin 16 := ![![1,4],![1,6],![1,8],![1,10],![1,12],![1,14],![2,4],![2,5],![2,8],![2,9],![2,12],![2,13],![3,4],![3,5],![3,8],![3,9],![3,12],![3,13],![4,9],![4,10],![4,11],![5,8],![5,9],![5,11],![6,8],![6,9],![6,10],![7,8],![7,10],![7,11]]
@[expose] def goodMask : Fin 8 → ℕ := ![0,135,633,766,945,822,456,335]
private def badPoints : Fin 30 → Fin 3 → Fin 2 → Fin 24 := ![![![0,7],![4,23],![10,19]],![![0,7],![1,3],![2,15]],![![0,22],![1,3],![10,19]],![![0,22],![2,15],![4,23]],![![0,20],![2,15],![10,19]],![![0,20],![1,3],![4,23]],![![0,7],![2,12],![10,11]],![![0,7],![1,16],![4,21]],![![0,22],![4,21],![10,11]],![![0,22],![1,16],![2,12]],![![0,20],![1,16],![10,11]],![![0,20],![2,12],![4,21]],![![0,7],![1,18],![10,17]],![![0,7],![2,9],![4,6]],![![0,22],![2,9],![10,17]],![![0,22],![1,18],![4,6]],![![0,20],![4,6],![10,17]],![![0,20],![1,18],![2,9]],![![1,18],![2,12],![10,19]],![![1,18],![4,23],![10,11]],![![2,12],![4,23],![10,17]],![![2,9],![4,21],![10,19]],![![1,16],![4,6],![10,19]],![![1,16],![2,9],![4,23]],![![1,3],![2,9],![10,11]],![![1,3],![2,12],![4,6]],![![2,15],![4,6],![10,11]],![![1,3],![4,21],![10,17]],![![1,18],![2,15],![4,21]],![![1,16],![2,15],![10,17]]]
private def swapIndex : Fin 30 → Fin 3 → Fin 16 := ![![4,1,1],![6,1,1],![8,1,1],![10,1,1],![12,1,1],![14,1,1],![4,2,2],![5,2,2],![8,2,2],![9,2,2],![12,2,2],![13,2,2],![4,3,3],![5,3,3],![8,3,3],![9,3,3],![12,3,3],![13,3,3],![4,4,9],![4,4,10],![4,4,11],![5,8,5],![5,9,5],![5,5,11],![6,8,6],![6,9,6],![10,6,6],![8,7,7],![10,7,7],![11,7,7]]
private def badMask : Fin 30 → Fin 3 → ℕ := ![![79,1834,1236],![79,31,993],![2045,31,1236],![2045,993,1834],![1789,993,1236],![1789,31,1834],![79,534,32],![79,1059,1557],![2045,1557,32],![2045,1059,534],![1789,1059,32],![1789,534,1557],![79,1395,1467],![79,184,112],![2045,184,1467],![2045,1395,112],![1789,112,1467],![1789,1395,184],![1395,534,1236],![1395,1834,32],![534,1834,1467],![184,1557,1236],![1059,112,1236],![1059,184,1834],![31,184,32],![31,534,112],![993,112,32],![31,1557,1467],![1395,993,1557],![1059,993,1467]]
private theorem badMask_spec : ∀ (k : Fin 30) (i : Fin 3), badMask k i = pairLabel (badPoints k i 0) (badPoints k i 1) := by decide +kernel
private theorem swap_spec : ∀ (k : Fin 30) (i : Fin 3),
  badPoints k i 0 ≠ badPoints k i 1 ∧
  (swapIndex k i = nonOctadPair k 0 ∨ swapIndex k i = nonOctadPair k 1) ∧
  starTable (swapIndex k i) (badPoints k i 0) = badPoints k i 1 ∧
  starTable (swapIndex k i) (badPoints k i 1) = badPoints k i 0 := by decide +kernel
private def codeRows : Fin 30 → Fin 11 → ℕ := ![![0,0,0,0,0,0,8,1,15,10,21],![0,0,0,0,16,0,8,1,15,26,0],![0,0,0,0,16,0,0,1,7,18,12],![0,0,0,0,0,0,20,1,19,22,24],![0,0,0,0,0,0,20,1,19,22,11],![0,0,0,0,16,0,0,1,7,18,11],![0,0,0,0,0,26,8,1,15,16,0],![0,0,0,0,0,0,8,1,15,10,16],![0,0,0,0,0,30,0,1,7,28,12],![0,0,0,0,0,0,28,1,27,30,16],![0,0,0,0,0,27,0,1,7,25,11],![0,0,0,0,0,0,18,1,21,16,11],![0,0,0,0,0,0,8,1,15,10,23],![0,0,0,0,0,17,8,1,15,27,0],![0,0,0,0,0,17,0,1,7,19,12],![0,0,0,0,0,0,27,1,28,25,23],![0,0,0,0,0,0,16,1,23,18,11],![0,0,0,0,0,28,0,1,7,30,11],![0,0,0,0,0,0,18,1,21,16,15],![0,0,0,0,0,26,0,1,7,24,21],![0,0,0,0,0,0,10,1,13,8,21],![0,0,0,0,0,9,0,1,7,11,27],![0,0,0,0,0,0,16,1,23,18,8],![0,0,0,0,0,17,0,1,7,19,25],![0,0,0,0,8,25,0,1,7,19,0],![0,0,0,0,8,0,18,1,21,24,0],![0,0,0,0,0,28,12,1,11,18,0],![0,0,0,0,8,0,0,1,7,10,18],![0,0,0,0,0,0,20,1,19,22,15],![0,0,0,0,0,0,20,1,19,22,8]]
private def decodeRows : Fin 30 → Fin 11 → ℕ := ![![135,633,945,79,1834,0,0,0,0,0,0],![135,633,945,79,31,0,0,0,0,0,0],![135,633,945,2045,31,0,0,0,0,0,0],![135,633,945,2045,993,0,0,0,0,0,0],![135,633,945,1789,993,0,0,0,0,0,0],![135,633,945,1789,31,0,0,0,0,0,0],![135,633,945,79,534,0,0,0,0,0,0],![135,633,945,79,1059,0,0,0,0,0,0],![135,633,945,2045,1557,0,0,0,0,0,0],![135,633,945,2045,1059,0,0,0,0,0,0],![135,633,945,1789,1059,0,0,0,0,0,0],![135,633,945,1789,534,0,0,0,0,0,0],![135,633,945,79,1395,0,0,0,0,0,0],![135,633,945,79,184,0,0,0,0,0,0],![135,633,945,2045,184,0,0,0,0,0,0],![135,633,945,2045,1395,0,0,0,0,0,0],![135,633,945,1789,112,0,0,0,0,0,0],![135,633,945,1789,1395,0,0,0,0,0,0],![135,633,945,1395,534,0,0,0,0,0,0],![135,633,945,1395,1834,0,0,0,0,0,0],![135,633,945,534,1834,0,0,0,0,0,0],![135,633,945,184,1557,0,0,0,0,0,0],![135,633,945,1059,112,0,0,0,0,0,0],![135,633,945,1059,184,0,0,0,0,0,0],![135,633,945,31,184,0,0,0,0,0,0],![135,633,945,31,534,0,0,0,0,0,0],![135,633,945,993,112,0,0,0,0,0,0],![135,633,945,31,1557,0,0,0,0,0,0],![135,633,945,1395,993,0,0,0,0,0,0],![135,633,945,1059,993,0,0,0,0,0,0]]
private def alphaRows : Fin 30 → Fin 11 → ℕ := ![![0,0,0,0,0,0,0,0,32,0,42],![0,0,0,0,0,0,0,0,32,15,0],![0,0,0,0,0,0,0,0,32,0,101],![0,0,0,0,0,0,0,0,32,0,36],![0,0,0,0,0,0,0,0,32,0,53],![0,0,0,0,45,0,0,0,32,0,0],![0,0,0,0,0,10,0,0,1052,0,0],![0,0,0,0,0,0,0,0,63,0,4],![0,0,0,0,0,69,0,0,31,0,0],![0,0,0,0,0,0,0,0,31,0,50],![0,0,0,0,0,69,0,0,80,0,0],![0,0,0,0,0,0,0,0,63,47,0],![0,0,0,0,0,0,0,0,32,0,10],![0,0,0,0,0,0,4,0,1048,0,0],![0,0,0,0,0,0,0,0,31,0,69],![0,0,0,0,0,0,0,0,31,0,45],![0,0,0,0,0,0,0,0,32,0,53],![0,0,0,0,0,0,0,16,80,0,0],![0,0,0,0,0,0,0,0,31,0,45],![0,0,0,0,0,0,0,0,80,0,84],![0,0,0,0,0,0,0,0,63,47,0],![0,0,0,0,0,0,0,0,31,0,90],![0,0,0,0,0,0,0,0,31,0,50],![0,0,0,0,0,0,0,16,80,0,0],![0,0,0,0,0,69,0,0,1100,0,0],![0,0,0,0,45,0,0,0,1059,0,0],![0,0,0,0,0,0,4,0,1048,0,0],![0,0,0,0,0,0,0,0,32,0,69],![0,0,0,0,0,0,0,0,32,0,4],![0,0,0,0,0,0,0,0,63,16,0]]
private def betaRows : Fin 30 → Fin 11 → ℕ := ![![0,0,0,0,0,0,51,0,44,15,45],![0,0,0,0,45,42,44,0,1071,0,0],![0,0,0,0,45,0,0,34,79,0,108],![0,0,0,0,0,17,0,0,31,1,60],![0,0,0,0,0,0,17,0,14,16,50],![0,0,0,0,0,72,0,71,79,0,35],![0,0,0,0,0,0,19,0,1040,15,1051],![0,0,0,0,0,0,51,47,19,0,54],![0,0,0,0,87,0,0,88,79,0,83],![0,0,0,0,0,0,54,0,22,47,60],![0,0,0,0,0,0,4,0,75,64,87],![0,0,0,0,0,0,0,24,32,57,18],![0,0,0,0,0,0,51,0,12,47,39],![0,0,0,0,0,0,12,16,1039,0,1041],![0,0,0,0,87,0,0,71,79,0,83],![0,0,0,0,0,0,4,0,59,47,35],![0,0,0,0,0,0,4,0,59,16,39],![0,0,0,0,0,0,0,8,79,22,18],![0,0,0,0,0,0,54,0,22,47,60],![0,0,0,0,0,69,0,0,79,5,28],![0,0,0,0,0,0,0,39,32,57,13],![0,0,0,0,87,0,0,71,79,0,83],![0,0,0,0,0,0,4,0,59,47,35],![0,0,0,0,0,0,0,8,79,70,13],![0,0,0,0,13,0,0,2,79,0,76],![0,0,0,0,0,0,41,0,9,47,35],![0,0,0,0,0,21,0,0,31,5,24],![0,0,0,0,45,0,0,34,79,0,108],![0,0,0,0,0,17,0,0,31,1,60],![0,0,0,0,0,0,0,39,31,57,50]]
private theorem mask_zero (r : Fin 11 → ℕ) : maskImage r 0 = 0 := by
  simp [maskImage]

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

private def reconstruction (k : Fin 30) (m : ℕ) : ℕ :=
  maskImage (decodeRows k) (maskImage (codeRows k) m) ^^^
    (maskImage (alphaRows k) (maskImage (rows (nonOctadPair k 0)) m ^^^ m) ^^^
      maskImage (betaRows k) (maskImage (rows (nonOctadPair k 1)) m ^^^ m))

private theorem reconstruction_basis : ∀ (k : Fin 30) (i : Fin 11),
    reconstruction k (2^i.val) = 2^i.val := by decide +kernel

private theorem reconstruction_eq (k : Fin 30) (m : Fin 2048) : reconstruction k m.val = m.val := by
  apply xor_hom_ext (reconstruction k) id
  · simp only [reconstruction,mask_zero,Nat.xor_self]
  · rfl
  · intro a b
    simp only [reconstruction,ElementaryBound.maskImage_xor]
    ac_rfl
  · intros; rfl
  · exact reconstruction_basis k

private theorem decode_cases : ∀ (k : Fin 30) (v : Fin 32),
    (∃ j : Fin 8, maskImage (decodeRows k) v.val = goodMask j) ∨
    ∃ (i : Fin 3) (j : Fin 8), maskImage (decodeRows k) v.val = Nat.xor (badMask k i) (goodMask j) := by
  decide +kernel

/-- The fixed-space calculation is certified on eleven basis vectors.
The remaining check has only 32 decoded vectors for each four-group. -/
private theorem fixed_masks (k : Fin 30) (m : Fin 2048)
    (ha : maskImage (rows (nonOctadPair k 0)) m.val = m.val)
    (hb : maskImage (rows (nonOctadPair k 1)) m.val = m.val) :
    (∃ j : Fin 8, m.val = goodMask j) ∨
    ∃ (i : Fin 3) (j : Fin 8), m.val = Nat.xor (badMask k i) (goodMask j) := by
  have he := reconstruction_eq k m
  simp only [reconstruction,ha,hb,Nat.xor_self,mask_zero,Nat.xor_zero] at he
  have hcode : ∀ (k : Fin 30) (i : Fin 11), codeRows k i < 2^5 := by decide +kernel
  have hv := mask_lt (codeRows k) 5 (hcode k) m.val
  have hc := decode_cases k ⟨maskImage (codeRows k) m.val,hv⟩
  dsimp only at hc
  rwa [he] at hc
open Subgroup Theory.GroupTheory MathieuCode
open Cardinality KernelCount Simplicity.Max1Fusion.KernelOrbits
open LinearFive InvolutionCentralizers.Second LargeCenterRadicals.OuterHalf
open scoped IsMulCommutative
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel basis

@[expose] def imageGroup : Subgroup M24 := (candidate 0).map pointEmbedding
@[expose] def imageElement (i : Fin 16) : M24 := pointEmbedding (sylowElement (candidateIndex 0 i))

theorem imageElement_mem (i : Fin 16) : imageElement i ∈ imageGroup :=
  mem_map_of_mem pointEmbedding (show sylowElement (candidateIndex 0 i) ∈ candidate 0 from ⟨i,rfl⟩)

private theorem star_points (x : M) (i : Fin 16) (hx : projection x = imageElement i)
    (j : Fin 24) : (starHom x).val j = starTable i j :=
  (KernelAction.star_points x _ hx j).trans (starTable_spec i j)

private theorem kernel_fixed (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (x : M) (hx : (x : Model) ∈ X) (i : Fin 16) (hpi : projection x = imageElement i)
    (m : Fin 2048) (hmX : (kernelValue m.val : Model) ∈ X) :
    maskImage (rows i) m.val = m.val := by
  have hc : Commute (kernelValue m.val) x := by
    apply Subtype.ext
    exact (X.le_centralizer hx) _ hmX
  have hrow : (fun j => pairLabel ((starHom x).val (basisPair j).1)
    ((starHom x).val (basisPair j).2)) = rows i := by
    funext j
    rw [star_points x _ hpi,star_points x _ hpi,rows_spec]
  have he : kernelValue (maskImage (rows i) m.val) = kernelValue m.val := by
    rw [← hrow,← KernelAction.kernel_conjugation,← hc.eq,mul_assoc,mul_inv_cancel,mul_one]
  apply kernelValue_injective ?_ m.isLt he
  rw [← hrow]
  exact SylowCore.Transport.starMask_lt (starHom x) m.val

private theorem good_inner (x : M) (hx2 : orderOf (x : Model) = 2)
    (i : Fin 16) (hpi : projection x = imageElement i) (j : Fin 8) :
    InnerRelated (x : Model) (kernelValue (goodMask j) : Model) := by
  let H := (solvableResidual (centralizer ({(x : Model)} : Set Model))).map
    (centralizer ({(x : Model)} : Set Model)).subtype
  have hp (a b : Fin 24) (hab : a ≠ b)
      (ha : starTable i a = a) (hb : starTable i b = b) :
      (kernelValue (pairLabel a b) : Model) ∈ H := by
    have ht := KernelAction.inner_of_star_fixed x a b hab
      ((star_points x i hpi a).trans ha) ((star_points x i hpi b).trans hb)
    have hc : Commute (kernelValue (pairLabel a b) : Model) (x : Model) :=
      (mem_centralizer_singleton_iff.mp (map_subtype_le _ ht)).symm
    exact (innerRelated_symm _ _ (KernelAction.pair_order a b hab) hx2 hc).mp ht
  have hf : ∀ i : Fin 16, starTable i 5 = 5 ∧ starTable i 8 = 8 ∧
      starTable i 13 = 13 ∧ starTable i 14 = 14 := by decide +kernel
  have ha : (kernelValue 135 : Model) ∈ H := hp 5 8 (by decide) (hf i).1 (hf i).2.1
  have hb : (kernelValue 633 : Model) ∈ H := hp 5 13 (by decide) (hf i).1 (hf i).2.2.1
  have hc : (kernelValue 945 : Model) ∈ H := hp 5 14 (by decide) (hf i).1 (hf i).2.2.2
  have hm (a b : ℕ) (ha : (kernelValue a : Model) ∈ H)
      (hb : (kernelValue b : Model) ∈ H) : (kernelValue (Nat.xor a b) : Model) ∈ H := by
    rw [kernelValue_xor]
    exact H.mul_mem ha hb
  change (kernelValue (goodMask j) : Model) ∈ H
  fin_cases j
  · change (kernelValue 0 : Model) ∈ H
    rw [kernelValue_zero]
    exact H.one_mem
  · exact ha
  · exact hb
  · exact hm 135 633 ha hb
  · exact hc
  · exact hm 135 945 ha hc
  · exact hm 633 945 hb hc
  · exact hm 135 (Nat.xor 633 945) ha (hm 633 945 hb hc)

/-- The explicit E8 of even subsets of the sextet's fixed tetrad. -/
@[expose] def kernelEight : Subgroup Model where
  carrier := Set.range (fun i : Fin 8 => (kernelValue (goodMask i) : Model))
  one_mem' := ⟨0,by
    change (kernelValue 0 : Model) = 1
    rw [kernelValue_zero]
    rfl⟩
  mul_mem' := by
    rintro _ _ ⟨i,rfl⟩ ⟨j,rfl⟩
    refine ⟨i ^^^ j,?_⟩
    have hg : ∀ i j : Fin 8, goodMask (i ^^^ j) = Nat.xor (goodMask i) (goodMask j) := by decide +kernel
    change (kernelValue (goodMask (i ^^^ j)) : Model) =
      (kernelValue (goodMask i) : Model) * (kernelValue (goodMask j) : Model)
    rw [hg,kernelValue_xor]
    rfl
  inv_mem' := by
    rintro _ ⟨i,rfl⟩
    refine ⟨i,?_⟩
    apply eq_inv_iff_mul_eq_one.mpr
    change ((kernelValue (goodMask i) * kernelValue (goodMask i) : M) : Model) = 1
    rw [← kernelValue_xor]
    change (kernelValue (goodMask i ^^^ goodMask i) : Model) = 1
    rw [Nat.xor_self,kernelValue_zero]
    rfl

theorem kernelEight_le_kernel : kernelEight ≤ E := by
  rintro _ ⟨i,rfl⟩
  exact kernelValue_mem_E _

theorem kernelEight_card : Nat.card kernelEight = 8 := by
  let f : Fin 8 → kernelEight := fun i => ⟨_,i,rfl⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j he
      have hlt : ∀ i : Fin 8, goodMask i < 2048 := by decide +kernel
      have hinj : Function.Injective goodMask := by decide +kernel
      exact hinj (kernelValue_injective (hlt i) (hlt j)
        (Subtype.ext (congrArg (fun x : kernelEight => (x : Model)) he)))
    · rintro ⟨x,i,rfl⟩
      exact ⟨i,rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf).symm).trans (Nat.card_fin 8)

/-- A non-octad four-group in the sextet image forces the original kernel
intersection into the explicit E8. No assumption that this E8 lies in X is used. -/
theorem kernel_intersection_le (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (k : Fin 30)
    (himage : ∀ d : Fin 2, imageElement (nonOctadPair k d) ∈ (X.subgroupOf M).map projection)
    (hzero : intrinsicElementaryForm X = 0) : X ⊓ E ≤ kernelEight := by
  intro z hz
  obtain ⟨v,hv,rfl⟩ := hz.2
  obtain ⟨m,hm⟩ := maskValue_surjective matrixA_mul_self matrixB_pow_four ⟨v,hv⟩
  have he : kernelValue m.val = v := congrArg Subtype.val hm
  have hmX : (kernelValue m.val : Model) ∈ X := he.symm ▸ hz.1
  have hfixed (d : Fin 2) : maskImage (rows (nonOctadPair k d)) m.val = m.val := by
    obtain ⟨x,hx,hpi⟩ := himage d
    exact kernel_fixed X x hx _ hpi m hmX
  obtain ⟨j,hj⟩ | ⟨i,j,hbad⟩ := fixed_masks k m (hfixed 0) (hfixed 1)
  · exact ⟨j,congrArg (fun x : M => (x : Model)) ((congrArg kernelValue hj).symm.trans he)⟩
  obtain ⟨hne,hswap,ha,hb⟩ := swap_spec k i
  have hix : imageElement (swapIndex k i) ∈ (X.subgroupOf M).map projection := by
    rcases hswap with h | h <;> rw [h]
    · exact himage 0
    · exact himage 1
  obtain ⟨x,hx,hpi⟩ := hix
  have hx1 : (x : Model) ≠ 1 := by
    intro h
    have hxM : x = 1 := Subtype.ext h
    have hstar := star_points x _ hpi (badPoints k i 0)
    rw [hxM,map_one] at hstar
    exact hne (hstar.trans ha)
  have hx2 : orderOf (x : Model) = 2 :=
    (Nat.prime_two.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) (x : Model) (show (x : Model) ∈ X from hx)))).resolve_left
      (by simpa using hx1)
  have hxinner := zero_form_le_involution_residual X hzero _ hx hx1 hmX
  have hgood := good_inner x hx2 _ hpi j
  let H := (solvableResidual (centralizer ({(x : Model)} : Set Model))).map
    (centralizer ({(x : Model)} : Set Model)).subtype
  have hpair : InnerRelated (x : Model) (kernelValue (badMask k i) : Model) := by
    have hp := H.mul_mem hxinner hgood
    change ((kernelValue m.val * kernelValue (goodMask j) : M) : Model) ∈ H at hp
    rw [← kernelValue_xor,hbad] at hp
    change (kernelValue ((badMask k i ^^^ goodMask j) ^^^ goodMask j) : Model) ∈ H at hp
    rw [Nat.xor_assoc,Nat.xor_self,Nat.xor_zero] at hp
    exact hp
  have hc : Commute (x : Model) (kernelValue (badMask k i) : Model) :=
    (mem_centralizer_singleton_iff.mp (map_subtype_le _ hpair)).symm
  have hreverse := (innerRelated_symm _ _ hx2 (by rw [badMask_spec]; exact KernelAction.pair_order _ _ hne) hc).mp hpair
  exact (LinearFive.Geometry.not_inner_of_star_swap x _ _ hne
    ((star_points x _ hpi _).trans ha) ((star_points x _ hpi _).trans hb) (by simpa only [badMask_spec] using hreverse)).elim

theorem kernel_intersection_card_le (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (k : Fin 30)
    (himage : ∀ d : Fin 2, imageElement (nonOctadPair k d) ∈ (X.subgroupOf M).map projection)
    (hzero : intrinsicElementaryForm X = 0) : Nat.card (X ⊓ E : Subgroup Model) ≤ 8 := by
  rw [← kernelEight_card]
  exact card_le_of_le (kernel_intersection_le X k himage hzero)

end Janko4.LocalStructure.ElementaryNormalizerCover.M22Images.SextetKernel
