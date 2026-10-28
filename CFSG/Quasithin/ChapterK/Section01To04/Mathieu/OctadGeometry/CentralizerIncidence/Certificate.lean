module

public import CFSG.Quasithin.ChapterK.Section01To04.Mathieu.OctadGeometry.Reduction
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.QuotientConstruction.AffineLifts.CodePreservation

/-!
# A native sixteen-element displacement centralizer

The listed permutations preserve the twelve Golay rows and fix every displacement
of the marked octad involution. Their distinctness, fixed octads and conjugation
witnesses are small kernel-checked calculations. Exhaustion uses H.16.2(6)'s
order statement in the parent module; no centralizer classification is encoded
as an unchecked table. The untrusted search is retained in `source/generate.py`.

Source: Aschbacher--Smith, K.4.3, printed pp.458--459, using H.16.2(6).
-/

public section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterK.Mathieu.OctadGeometry.CentralizerIncidence.Certificate

@[expose] def point : Fin 16 → Fin 24 → Fin 24 := ![![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23],![0,1,2,3,4,5,7,6,23,12,18,11,9,22,20,19,21,17,10,15,14,16,13,8],![1,0,5,4,3,2,6,7,8,12,18,17,9,22,14,19,16,11,10,15,20,21,13,23],![1,0,5,4,3,2,7,6,23,9,10,17,12,13,20,15,21,11,18,19,14,16,22,8],![2,5,0,17,11,1,6,7,8,9,10,4,12,22,20,19,21,3,18,15,14,16,13,23],![2,5,0,17,11,1,7,6,23,12,18,4,9,13,14,15,16,3,10,19,20,21,22,8],![3,4,17,0,1,11,6,7,23,12,10,5,9,22,20,15,16,2,18,19,14,21,13,8],![3,4,17,0,1,11,7,6,8,9,18,5,12,13,14,19,21,2,10,15,20,16,22,23],![4,3,11,1,0,17,6,7,23,9,18,2,12,13,20,19,16,5,10,15,14,21,22,8],![4,3,11,1,0,17,7,6,8,12,10,2,9,22,14,15,21,5,18,19,20,16,13,23],![5,2,1,11,17,0,6,7,8,12,18,3,9,13,20,15,21,4,10,19,14,16,22,23],![5,2,1,11,17,0,7,6,23,9,10,3,12,22,14,19,16,4,18,15,20,21,13,8],![11,17,4,5,2,3,6,7,23,9,18,0,12,22,14,15,21,1,10,19,20,16,13,8],![11,17,4,5,2,3,7,6,8,12,10,0,9,13,20,19,16,1,18,15,14,21,22,23],![17,11,3,2,5,4,6,7,23,12,10,1,9,13,14,19,21,0,18,15,20,16,22,8],![17,11,3,2,5,4,7,6,8,9,18,1,12,22,20,15,16,0,10,19,14,21,13,23]]

@[expose] def perm (n : Fin 16) : Equiv.Perm (Fin 24) where
  toFun := point n
  invFun := point n
  left_inv := by revert n; decide +kernel
  right_inv := by revert n; decide +kernel

private def messages : Fin 16 → Fin 12 → Fin 4096 := ![![1,2,4,8,16,32,64,128,256,512,1024,2048],![769,2306,2820,2056,528,288,2944,2880,256,512,3584,2048],![1538,3073,3616,3088,1544,1028,2624,2688,256,512,3584,2048],![1282,1281,1312,1040,1032,1284,384,320,256,512,1024,2048],![12,2088,2057,2056,1032,10,2112,2176,256,512,2072,2048],![780,296,777,8,1544,266,896,832,256,512,536,2048],![780,2324,2820,2053,518,1284,2880,2944,256,512,2596,2048],![12,20,4,5,6,1028,128,64,256,512,36,2048],![304,296,1312,34,33,288,320,384,256,512,36,2048],![560,2088,3616,2082,545,32,2688,2624,256,512,2596,2048],![560,20,530,1040,528,17,576,640,256,512,536,2048],![304,2324,2322,3088,16,273,2432,2368,256,512,2072,2048],![1282,2306,2322,2082,6,266,2368,2432,256,512,2051,2048],![1538,2,530,34,518,10,640,576,256,512,515,2048],![769,1281,777,5,545,273,832,896,256,512,515,2048],![1,3073,2057,2053,33,17,2176,2112,256,512,2051,2048]]

private theorem rows : ∀ n j,
    m24PermuteMask (perm n) (m24GolayRow j) = m24GolayCode (messages n j) := by
  decide +kernel

/-- Sixteen actual Witt-design automorphisms. -/
noncomputable def element (n : Fin 16) : M24 :=
  ⟨perm n, PairOvergroups.QuotientConstruction.AffineLiftConstruction.mem_M24_of_rows _
    (fun j => ⟨messages n j, rows n j⟩)⟩

theorem element_injective : Function.Injective element := by
  intro n m h
  have hc : ∀ n m : Fin 16,
      point n 0 = point m 0 → point n 6 = point m 6 → n = m := by
    decide +kernel
  exact hc n m (congrArg (fun g : M24 => g.val 0) h)
    (congrArg (fun g : M24 => g.val 6) h)

theorem element_zero : element 0 = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro i
  revert i
  decide +kernel

theorem element_one : element 1 = M24InvolutionCentralizers.involution2A := by
  apply Subtype.ext
  apply Equiv.ext
  intro i
  revert i
  decide +kernel

private theorem fixes_displacement_rows : ∀ (n : Fin 16) (j : Fin 12) (i : Fin 24),
    row j ((perm 1) ((perm n) i)) - row j ((perm n) i) =
      row j ((perm 1) i) - row j i := by
  decide +kernel

/-- The certificate fixes the literal displacement in the Golay space. -/
theorem fixes_golay_displacement (n : Fin 16) (v : golay) :
    golayRepresentation (element n) (golayRepresentation (element 1) v - v) =
      golayRepresentation (element 1) v - v := by
  apply Subtype.ext
  change fullRepresentation (element n) (fullRepresentation (element 1) v.val - v.val) =
    fullRepresentation (element 1) v.val - v.val
  generalize hw : v.val = w
  have hv : w ∈ golay := hw ▸ v.property
  clear hw v
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨j,rfl⟩ := hv
      funext i
      exact fixes_displacement_rows n j i
  | zero => simp only [map_zero, sub_zero]
  | add x y hx hy hx' hy' =>
      simp only [map_add, add_sub_add_comm, hx', hy']
  | smul c x hx hx' =>
      simp only [map_smul, ← smul_sub, hx']

/-- The same statement on the literal code quotient. -/
theorem fixes_code_displacement (n : Fin 16) (v : Code) :
    codeRepresentation (element n) (displacement codeRepresentation (element 1) v) =
      displacement codeRepresentation (element 1) v := by
  obtain ⟨w,rfl⟩ := codeLine.mkQ_surjective v
  change codeRepresentation (element n)
    (codeRepresentation (element 1) (codeLine.mkQ w) - codeLine.mkQ w) = _
  rw [codeRepresentation_mk, ← map_sub, codeRepresentation_mk, fixes_golay_displacement]
  rfl

private def fixedMessage : Fin 16 → Fin 4096 := ![0,1087,448,2560,960,2048,192,2816,2752,256,2496,512,704,2304,2240,768]

/-- Every nonidentity element has a genuine fixed octad. -/
theorem fixed_octad (n : Fin 16) (hn : n ≠ 0) :
    ∃ O : Octad, ∀ i : Fin 24, element n • i = i ↔ i ∈ O.val := by
  have hc : ∀ n : Fin 16, n ≠ 0 → (m24GolayWord (fixedMessage n)).card = 8 := by
    decide +kernel
  refine ⟨⟨m24GolayWord (fixedMessage n),
    m24GolayWord_mem_blocks_of_card_eq_eight _ (hc n hn)⟩, ?_⟩
  have hf : ∀ (n : Fin 16), n ≠ 0 → ∀ i : Fin 24,
      point n i = i ↔ i ∈ m24GolayWord (fixedMessage n) := by
    decide +kernel
  exact hf n hn

/-- Outside the marked cyclic subgroup, no octad coordinate is fixed. -/
theorem point_stabilizer (n : Fin 16) (i : Fin 24)
    (hz : element 1 • i = i) (hn : element n • i = i) : n = 0 ∨ n = 1 := by
  have hc : ∀ (n : Fin 16) (i : Fin 24),
      point 1 i = i → point n i = i → n = 0 ∨ n = 1 := by
    decide +kernel
  exact hc n i hz hn

private def conjugatorPerm (n : Fin 16) : Equiv.Perm (Fin 24) where
  toFun := (![![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23],![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23],![11,17,2,1,0,5,23,8,14,10,15,4,18,22,6,12,21,3,19,9,7,16,13,20],![4,3,0,17,11,1,12,9,22,6,16,2,7,23,19,14,10,5,21,20,15,18,8,13],![2,0,11,5,1,4,6,7,12,22,16,3,13,15,10,20,23,17,21,14,18,8,19,9],![2,0,17,11,4,3,19,15,21,6,10,1,7,9,13,23,20,5,18,8,22,14,12,16],![4,1,17,0,3,2,15,19,7,22,8,11,13,12,16,14,18,5,23,20,21,10,9,6],![11,5,4,3,0,1,23,8,12,18,7,2,10,21,20,15,13,17,6,19,14,22,16,9],![5,17,4,3,1,0,7,6,22,10,14,11,18,8,21,15,12,2,20,19,16,9,23,13],![5,17,1,4,0,3,20,14,19,21,13,2,16,12,23,7,10,11,22,6,8,18,9,15],![17,4,3,1,2,11,15,19,22,21,20,0,16,10,8,9,7,5,14,12,23,6,18,13],![0,5,1,17,4,2,14,20,21,23,6,3,8,15,9,13,10,11,7,22,12,18,19,16],![11,0,3,1,17,5,19,15,6,13,23,4,22,10,20,21,9,2,8,16,14,12,18,7],![1,17,2,0,11,4,16,21,18,9,14,3,12,19,13,6,8,5,20,7,22,23,15,10],![5,4,3,0,17,2,14,20,6,19,12,1,15,23,22,21,18,11,9,16,13,10,8,7],![11,1,4,3,2,5,8,23,12,18,6,0,10,14,16,13,15,17,7,22,21,19,20,9]]) n
  invFun := (![![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23],![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23],![4,3,2,17,11,5,14,20,7,19,9,0,15,22,8,10,21,1,12,18,23,16,13,6],![2,5,11,1,0,17,9,12,22,7,16,4,6,23,15,20,10,3,21,14,19,18,8,13],![1,4,0,11,5,3,6,7,21,23,14,2,8,12,19,13,10,17,20,22,15,18,9,16],![1,11,0,5,4,17,9,12,19,13,10,3,22,14,21,7,23,2,18,6,16,8,20,15],![3,1,5,4,0,17,23,8,10,22,21,11,13,12,15,6,14,2,16,7,19,20,9,18],![4,5,11,3,2,1,18,10,7,23,12,0,8,16,20,15,22,17,9,19,14,13,21,6],![5,4,17,3,2,0,7,6,13,21,9,11,16,23,10,15,20,1,12,19,18,14,8,22],![4,2,11,5,3,0,19,15,20,22,16,17,13,10,7,23,12,1,21,8,6,9,18,14],![11,3,4,2,1,17,21,16,14,15,13,5,19,23,18,6,12,0,22,7,10,9,8,20],![0,2,5,11,4,1,10,18,12,14,16,17,20,15,6,13,23,3,21,22,7,8,19,9],![1,3,17,2,11,5,8,23,18,16,13,0,21,9,20,7,19,4,22,6,14,15,12,10],![3,0,2,11,5,17,15,19,16,9,23,4,12,14,10,22,6,1,8,13,18,7,20,21],![3,11,5,2,1,0,8,23,22,18,21,17,10,20,6,12,19,4,16,9,7,15,14,13],![11,1,4,3,2,5,10,18,6,23,12,0,8,15,13,16,14,17,9,21,22,20,19,7]]) n
  left_inv := by revert n; decide +kernel
  right_inv := by revert n; decide +kernel

private def fusionMessages : Fin 16 → Fin 12 → Fin 4096 := ![![1,2,4,8,16,32,64,128,256,512,1024,2048],![1,2,4,8,16,32,64,128,256,512,1024,2048],![1224,2568,2124,2698,585,616,2688,2432,704,192,2072,2752],![2224,2344,2465,288,1184,2082,2432,2944,2048,192,420,256],![2820,769,3584,32,2050,784,2880,2688,512,2304,2312,256],![2212,289,2208,1312,2480,2344,384,128,2304,2240,162,2816],![2160,866,2912,801,2344,100,2624,2880,448,2304,3616,512],![1536,672,720,2248,2177,2626,576,2944,704,2240,2116,2048],![2596,2564,2068,12,6,2565,2688,2112,2048,512,1540,768],![1440,3776,3586,3920,3265,1096,832,2944,2496,2304,1668,960],![2912,2672,2344,162,932,3552,2112,2688,2816,448,737,960],![3841,3168,1986,1216,3920,1668,384,2368,2752,960,3464,2560],![1156,133,396,774,516,932,384,640,448,2816,788,512],![2146,224,2084,417,3552,2480,128,320,2240,2816,360,2496],![3232,1424,1928,3841,1024,1668,2944,2432,2752,2560,1794,2304],![3584,2626,720,200,2116,672,896,2624,2752,192,2177,2048]]

private theorem fusion_rows : ∀ n j,
    m24PermuteMask (conjugatorPerm n) (m24GolayRow j) =
      m24GolayCode (fusionMessages n j) := by
  decide +kernel

/-- A native conjugator from element 2 to each element outside the marked line. -/
noncomputable def conjugator (n : Fin 16) : M24 :=
  ⟨conjugatorPerm n,
    PairOvergroups.QuotientConstruction.AffineLiftConstruction.mem_M24_of_rows _
      (fun j => ⟨fusionMessages n j, fusion_rows n j⟩)⟩

theorem conjugator_centralizes (n : Fin 16) :
    MulAut.conj (conjugator n) (element 1) = element 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro i
  change conjugatorPerm n (perm 1 ((conjugatorPerm n).symm i)) = perm 1 i
  revert n i
  decide +kernel

theorem conjugator_fuses (n : Fin 16) (h0 : n ≠ 0) (h1 : n ≠ 1) :
    MulAut.conj (conjugator n) (element 2) = element n := by
  apply Subtype.ext
  apply Equiv.ext
  intro i
  change conjugatorPerm n (perm 2 ((conjugatorPerm n).symm i)) = perm n i
  have hc : ∀ n : Fin 16, n ≠ 0 → n ≠ 1 → ∀ i : Fin 24,
      conjugatorPerm n (perm 2 ((conjugatorPerm n).symm i)) = perm n i := by
    decide +kernel
  exact hc n h0 h1 i

end CFSG.Quasithin.ChapterK.Mathieu.OctadGeometry.CentralizerIncidence.Certificate
