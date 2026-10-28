module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.Native.HexadCoordinates
import all Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.Native.HexadCoordinates
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.Native.HexadRealization
public import Theory.SpecificGroups.Thompson.Model.GeneratorCertificates.BinaryMatrix

/-!
# Fixed-space bounds for subgroups of the native hexad two-core

Enumerate the sixteen translations by short words in the four already
certified generators. Packed binary row identities give eight recovery
coordinates for the fixed space of every nonidentity translation. For
two distinct nonidentity translations, a second recovery identity puts
every common fixed vector in the known six-dimensional fixed space.
The arithmetic checker proves each packed identity equals ordinary matrix
multiplication; no unchecked finite computation is used.

The original cover map identifies these translations with the whole full
hexad two-core. Conjugation by the same native matrix transports both
bounds to every design hexad, retaining the original binary column action.
The source consumer is HexadCentralizers, on the literal Q/Z marking.

The private `import all` of HexadCoordinates is an intentional internal
certificate split: its unexposed matrix bodies are needed only for the
private numerical bridge. The earlier public boundary remains unchanged.

Source: Aschbacher–Segev, The uniqueness of groups of type J4,
Invent. Math. 105 (1991), proof of (4.6), p.598, DOI 10.1007/BF01232280.
The native generator words and matrix attribution are inherited from
HexadCoordinates and M22James; see LICENSES/ATLAS.txt.
-/

@[expose] public noncomputable section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.NativeHexadBounds
open Subgroup Sporadic.Mathieu M22TripleCover NativeHexadCoordinates
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Thompson.BinaryMatrix
open scoped BigOperators Matrix

private def rect (m n : ℕ) (rows : Array ℕ) : Matrix (Fin m) (Fin n) (ZMod 2) :=
  fun i j => bit (getElem! rows i.val) j.val

private theorem rect_mul (m n k : ℕ) (a b c : Array ℕ)
    (hc : ∀ i : Fin m, rowProduct (getElem! a i.val) b n = (getElem! c i.val)) :
    rect m n a * rect n k b = rect m k c := by
  ext i j
  change (∑ t : Fin n, bit (getElem! a i.val) t.val * bit (getElem! b t.val) j.val) = bit (getElem! c i.val) j.val
  rw [Fin.sum_univ_eq_sum_range (fun t => bit (getElem! a i.val) t * bit (getElem! b t) j.val),
    ← bit_rowProduct, hc i]

private theorem rect_sum_mul_one (a b c d : Array ℕ)
    (hc : ∀ i : Fin 12, rowProduct (getElem! a i.val) b 8 ^^^ rowProduct (getElem! c i.val) d 12 = 2^i.val) :
    rect 12 8 a * rect 8 12 b + decode 12 c * decode 12 d = 1 := by
  ext i j
  change (∑ t : Fin 8, bit (getElem! a i.val) t.val * bit (getElem! b t.val) j.val) +
    (∑ t : Fin 12, bit (getElem! c i.val) t.val * bit (getElem! d t.val) j.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun t => bit (getElem! a i.val) t * bit (getElem! b t) j.val),
    Fin.sum_univ_eq_sum_range (fun t => bit (getElem! c i.val) t * bit (getElem! d t) j.val),
    ←bit_rowProduct,←bit_rowProduct,←bit_xor,hc i]
  simp [bit,Nat.testBit_two_pow,Matrix.one_apply,Fin.ext_iff]

private theorem decode_sum_mul (a b c d r : Array ℕ)
    (hc : ∀ i : Fin 12, rowProduct (getElem! a i.val) b 12 ^^^ rowProduct (getElem! c i.val) d 12 = (getElem! r i.val)) :
    decode 12 a * decode 12 b + decode 12 c * decode 12 d = decode 12 r := by
  ext i j
  change (∑ t : Fin 12, bit (getElem! a i.val) t.val * bit (getElem! b t.val) j.val) +
    (∑ t : Fin 12, bit (getElem! c i.val) t.val * bit (getElem! d t.val) j.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun t => bit (getElem! a i.val) t * bit (getElem! b t) j.val),
    Fin.sum_univ_eq_sum_range (fun t => bit (getElem! c i.val) t * bit (getElem! d t) j.val),
    ←bit_rowProduct,←bit_rowProduct,←bit_xor,hc i]
  rfl

private def rows : Fin 16 → Array ℕ := ![#[1,2,4,8,16,32,64,128,256,512,1024,2048],#[1207,837,1177,1214,3450,871,2460,2608,620,3036,1863,1345],#[3840,837,495,676,3517,3786,1073,2396,3245,1649,3127,1770],#[2998,2,1394,1554,215,3469,3565,1004,4033,4013,3952,2987],#[3200,1560,4034,1465,3197,3850,3265,2396,1117,3713,1863,3610],#[2102,1375,2911,271,279,3149,1309,1004,1841,1885,1024,859],#[897,1375,3625,1813,464,480,2224,128,2544,2800,3952,240],#[1847,1560,2740,931,3258,679,364,2608,2716,812,3127,3505],#[3776,3779,3781,3810,3197,3786,1309,2844,4033,1885,3355,1094],#[2678,3460,2648,2644,279,3469,3265,428,3245,3713,3676,2311],#[449,3460,3886,3150,464,32,364,704,620,812,1324,2732],#[1399,3779,2995,2296,3258,871,2224,2160,256,2800,1643,2029],#[577,2265,259,2899,16,480,2460,704,2716,3036,3676,604],#[1783,2974,1438,4069,3450,679,64,2160,2544,512,3355,3869],#[3392,2974,232,2559,3517,3850,3565,2844,1841,4013,1643,3254],#[2550,2265,1141,3401,215,3149,1073,428,1117,1649,1324,503]]

private def deltas : Fin 16 → Array ℕ := ![#[0,0,0,0,0,0,0,0,0,0,0,0],#[1206,839,1181,1206,3434,839,2524,2736,876,2524,839,3393],#[3841,839,491,684,3501,3818,1137,2524,3501,1137,2103,3818],#[2999,0,1398,1562,199,3501,3501,876,3777,3501,2928,939],#[3201,1562,4038,1457,3181,3882,3201,2524,1373,3201,839,1562],#[2103,1373,2907,263,263,3181,1373,876,1585,1373,0,2907],#[896,1373,3629,1821,448,448,2288,0,2288,2288,2928,2288],#[1846,1562,2736,939,3242,647,300,2736,2972,300,2103,1457],#[3777,3777,3777,3818,3181,3818,1373,2972,3777,1373,2331,3142],#[2679,3462,2652,2652,263,3501,3201,300,3501,3201,2652,263],#[448,3462,3882,3142,448,0,300,576,876,300,300,684],#[1398,3777,2999,2288,3242,839,2288,2288,0,2288,619,4077],#[576,2267,263,2907,0,448,2524,576,2972,2524,2652,2652],#[1782,2972,1434,4077,3434,647,0,2288,2288,0,2331,1821],#[3393,2972,236,2551,3501,3882,3501,2972,1585,3501,619,1206],#[2551,2267,1137,3393,199,3181,1137,300,1373,1137,300,2551]]

private def genRows : Fin 4 → Array ℕ := ![#[1207,837,1177,1214,3450,871,2460,2608,620,3036,1863,1345],#[2998,2,1394,1554,215,3469,3565,1004,4033,4013,3952,2987],#[1847,1560,2740,931,3258,679,364,2608,2716,812,3127,3505],#[2550,2265,1141,3401,215,3149,1073,428,1117,1649,1324,503]]

private def stepIndex : Fin 15 → Fin 4 := ![0,1,0,2,0,1,0,3,0,1,0,2,0,1,0]

private theorem rows_step : ∀ i : Fin 15, ∀ r : Fin 12,
    rowProduct (getElem! (rows ⟨i.val,by omega⟩) r.val) (genRows (stepIndex i)) 12 =
      getElem! (rows ⟨i.val+1,by omega⟩) r.val := by decide +kernel
private theorem generator_decode (i : Fin 4) : generatorMatrix i = decode 12 (genRows i) := by
  revert i; decide +kernel
private theorem deltas_decode (i : Fin 16) : decode 12 (deltas i) = decode 12 (rows i) - 1 := by
  revert i; decide +kernel
private def word : ℕ → M22TripleCover
  | 0 => 1
  | n+1 => word n * generator (stepIndex ⟨n % 15,Nat.mod_lt _ (by decide)⟩)
private theorem word_mem (n : ℕ) : word n ∈ translations := by
  induction n with
  | zero => exact one_mem _
  | succ n hn => exact translations.mul_mem hn (subset_closure ⟨_,rfl⟩)
private theorem word_matrix (n : ℕ) : ∀ hn : n<16,
    ((word n : Matrix12ˣ) : Matrix12) = decode 12 (rows ⟨n,hn⟩) := by
  induction n with
  | zero => intro hn; change 1 = decode 12 (rows 0); decide +kernel
  | succ n ih =>
    intro hn
    have hn15 : n<15 := by omega
    have he : (⟨n % 15,Nat.mod_lt n (by decide : 0<15)⟩ : Fin 15) = ⟨n,hn15⟩ :=
      Fin.ext (Nat.mod_eq_of_lt hn15)
    change ((word n : Matrix12ˣ) : Matrix12) *
      ((generator (stepIndex ⟨n%15,_⟩) : Matrix12ˣ) : Matrix12) = _
    rw [ih (by omega),generator_matrix,he,generator_decode]
    exact decode_mul 12 _ _ _ (rows_step ⟨n,hn15⟩)
private theorem row_injective : Function.Injective (fun i : Fin 16 => decode 12 (rows i) 0) := by
  decide +kernel
private theorem exists_word (g : M22TripleCover) (hg : g ∈ translations) :
    ∃ i : Fin 16, word i.val = g := by
  let f (i : Fin 16) : translations := ⟨word i.val,word_mem i.val⟩
  have hi : Function.Injective f := by
    intro i j hij
    apply row_injective
    have hh := congrArg (fun t : translations => ((t.val : Matrix12ˣ) : Matrix12)) hij
    change ((word i.val : Matrix12ˣ) : Matrix12) = ((word j.val : Matrix12ˣ) : Matrix12) at hh
    rw [word_matrix i.val i.isLt,word_matrix j.val j.isLt] at hh
    exact congrArg (fun M : Matrix12 => M 0) hh
  obtain ⟨i,hi⟩ := (hi.bijective_of_nat_card_le (by rw [Nat.card_fin,translations_card])).2 ⟨g,hg⟩
  exact ⟨i,congrArg Subtype.val hi⟩

private def singleInclusion : Fin 15 → Array ℕ := ![#[1,2,4,8,16,11,32,64,128,167,93,252],#[1,2,4,8,16,32,64,128,235,172,113,55],#[1,2,4,8,16,32,64,71,128,236,246,28],#[1,2,4,8,16,32,64,108,128,199,221,176],#[1,2,4,8,16,32,64,128,7,107,90,55],#[1,2,4,8,16,32,64,128,192,64,157,240],#[1,2,4,8,16,32,64,128,44,135,157,55],#[1,2,4,8,16,11,32,64,128,71,189,155],#[1,2,4,8,16,11,32,64,7,128,253,188],#[1,2,4,8,16,32,64,108,44,64,128,198],#[1,2,4,8,16,32,64,128,44,107,90,240],#[1,2,4,8,16,32,64,71,7,64,128,28],#[1,2,4,8,16,32,64,128,235,135,113,240],#[1,2,4,8,16,32,64,108,128,107,90,155],#[1,2,4,8,16,32,64,71,44,128,113,28]]

private def singleSelector : Fin 15 → Array ℕ := ![#[1,2,4,8,16,64,128,256],#[1,2,4,8,16,32,64,128],#[1,2,4,8,16,32,64,256],#[1,2,4,8,16,32,64,256],#[1,2,4,8,16,32,64,128],#[1,2,4,8,16,32,64,128],#[1,2,4,8,16,32,64,128],#[1,2,4,8,16,64,128,256],#[1,2,4,8,16,64,128,512],#[1,2,4,8,16,32,64,1024],#[1,2,4,8,16,32,64,128],#[1,2,4,8,16,32,64,1024],#[1,2,4,8,16,32,64,128],#[1,2,4,8,16,32,64,256],#[1,2,4,8,16,32,64,512]]

private def singleRepair : Fin 15 → Array ℕ := ![#[0,0,0,0,0,5,0,0,0,2,4,17],#[0,0,0,0,0,0,0,0,4,6,64,67],#[0,0,0,0,0,0,0,16,0,12,4,29],#[0,0,0,0,0,0,0,15,0,5,7,9],#[0,0,0,0,0,0,0,0,8,13,10,1],#[0,0,0,0,0,0,0,0,11,10,9,7],#[0,0,0,0,0,0,0,0,3,11,9,15],#[0,0,0,0,0,9,0,0,0,24,64,89],#[0,0,0,0,0,5,0,0,16,0,22,4],#[0,0,0,0,0,0,0,65,64,71,0,3],#[0,0,0,0,0,0,0,0,25,18,24,8],#[0,0,0,0,0,0,0,15,4,1,0,13],#[0,0,0,0,0,0,0,0,14,11,10,7],#[0,0,0,0,0,0,0,4,0,10,13,12],#[0,0,0,0,0,0,0,13,3,0,4,15]]

private theorem single_check : ∀ i : Fin 15, ∀ r : Fin 12,
    rowProduct (getElem! (singleInclusion i) r.val) (singleSelector i) 8 ^^^
      rowProduct (getElem! (singleRepair i) r.val) (deltas ⟨i.val+1,by omega⟩) 12 = 2^r.val := by
  decide +kernel
private theorem single_reconstruction (i : Fin 15) :
    rect 12 8 (singleInclusion i) * rect 8 12 (singleSelector i) +
      decode 12 (singleRepair i) * decode 12 (deltas ⟨i.val+1,by omega⟩) = 1 :=
  rect_sum_mul_one _ _ _ _ (single_check i)

private def pairLeft : Fin 15 → Fin 15 → Array ℕ := ![![#[0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,5,0,18,23,21,22,20],#[0,0,0,0,0,5,0,23,22,20,19,16],#[0,0,0,0,0,5,0,20,1,3,16,4],#[0,0,0,0,0,5,0,20,0,2,16,5],#[0,0,0,0,0,5,0,2,6,4,6,21],#[0,0,0,0,0,5,0,3,5,7,7,23],#[0,0,0,0,0,5,0,23,16,18,19,22],#[0,0,0,0,0,5,0,22,0,2,18,7],#[0,0,0,0,0,5,0,21,21,23,17,17],#[0,0,0,0,0,5,0,23,22,20,19,16],#[0,0,0,0,0,5,0,17,2,0,21,2],#[0,0,0,0,0,5,0,17,3,1,21,3],#[0,0,0,0,0,5,0,5,19,17,1,7],#[0,0,0,0,0,5,0,1,17,19,5,1]],![#[0,0,0,0,0,0,0,64,68,70,64,67],#[0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,5,0,65,64,66,69,70],#[0,0,0,0,0,68,0,3,67,65,4,7],#[0,0,0,0,0,65,0,68,1,3,1,2],#[0,0,0,0,0,66,0,2,68,70,2,1],#[0,0,0,0,0,69,0,70,7,5,5,6],#[0,0,0,0,0,5,0,68,69,71,69,70],#[0,0,0,0,0,7,0,66,65,67,71,68],#[0,0,0,0,0,4,0,4,4,6,68,71],#[0,0,0,0,0,5,0,65,64,66,69,70],#[0,0,0,0,0,65,0,71,2,0,1,2],#[0,0,0,0,0,70,0,7,69,71,6,5],#[0,0,0,0,0,71,0,64,3,1,7,4],#[0,0,0,0,0,71,0,4,71,69,7,4]],![#[0,0,0,0,0,12,0,16,20,20,28,29],#[0,0,0,0,0,12,0,16,21,21,29,29],#[0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,12,0,16,5,5,13,29],#[0,0,0,0,0,29,0,16,0,17,25,29],#[0,0,0,0,0,28,0,16,8,24,16,29],#[0,0,0,0,0,9,0,16,1,4,12,29],#[0,0,0,0,0,5,0,16,25,16,24,29],#[0,0,0,0,0,9,0,16,17,20,28,29],#[0,0,0,0,0,9,0,16,16,21,29,29],#[0,0,0,0,0,13,0,16,9,8,0,29],#[0,0,0,0,0,12,0,16,0,0,8,29],#[0,0,0,0,0,24,0,16,29,9,1,29],#[0,0,0,0,0,25,0,16,20,1,9,29],#[0,0,0,0,0,9,0,16,4,1,9,29]],![#[0,0,0,0,0,0,0,15,8,13,15,1],#[0,0,0,0,0,11,0,4,15,10,8,13],#[0,0,0,0,0,7,0,8,4,1,3,10],#[0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,5,0,10,9,12,14,5],#[0,0,0,0,0,10,0,5,11,14,12,8],#[0,0,0,0,0,3,0,12,1,4,6,11],#[0,0,0,0,0,0,0,15,4,1,3,13],#[0,0,0,0,0,12,0,3,1,4,6,4],#[0,0,0,0,0,14,0,1,1,4,6,6],#[0,0,0,0,0,7,0,8,4,1,3,10],#[0,0,0,0,0,9,0,6,5,0,2,5],#[0,0,0,0,0,8,0,7,3,6,4,2],#[0,0,0,0,0,13,0,2,3,6,4,7],#[0,0,0,0,0,6,0,9,6,3,1,9]],![#[0,0,0,0,0,5,0,15,8,8,10,4],#[0,0,0,0,0,5,0,13,8,8,10,4],#[0,0,0,0,0,2,0,6,8,15,10,3],#[0,0,0,0,0,7,0,12,8,10,10,6],#[0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,6,0,3,8,11,10,7],#[0,0,0,0,0,7,0,11,8,10,10,6],#[0,0,0,0,0,0,0,6,8,13,10,1],#[0,0,0,0,0,12,0,15,8,1,10,13],#[0,0,0,0,0,11,0,8,8,6,10,10],#[0,0,0,0,0,2,0,6,8,15,10,3],#[0,0,0,0,0,13,0,12,8,0,10,12],#[0,0,0,0,0,9,0,7,8,4,10,8],#[0,0,0,0,0,3,0,4,8,14,10,2],#[0,0,0,0,0,8,0,9,8,5,10,9]],![#[0,0,0,0,0,9,0,1,10,10,8,15],#[0,0,0,0,0,14,0,1,10,10,8,8],#[0,0,0,0,0,2,0,6,13,10,15,3],#[0,0,0,0,0,13,0,3,8,10,10,9],#[0,0,0,0,0,6,0,7,12,10,14,6],#[0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,8,0,3,8,10,10,12],#[0,0,0,0,0,0,0,4,15,10,13,3],#[0,0,0,0,0,5,0,13,6,10,4,15],#[0,0,0,0,0,5,0,15,4,10,6,13],#[0,0,0,0,0,2,0,6,13,10,15,3],#[0,0,0,0,0,7,0,11,0,10,2,11],#[0,0,0,0,0,3,0,5,14,10,12,1],#[0,0,0,0,0,9,0,12,7,10,5,2],#[0,0,0,0,0,7,0,12,7,10,5,12]],![#[0,0,0,0,0,9,0,1,10,10,8,6],#[0,0,0,0,0,11,0,3,8,8,10,4],#[0,0,0,0,0,7,0,10,4,1,3,8],#[0,0,0,0,0,6,0,14,5,5,7,9],#[0,0,0,0,0,13,0,7,14,12,14,2],#[0,0,0,0,0,8,0,2,11,9,11,7],#[0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,13,3,6,4,15],#[0,0,0,0,0,0,0,4,3,15,13,15],#[0,0,0,0,0,14,0,13,13,6,4,1],#[0,0,0,0,0,7,0,10,4,1,3,8],#[0,0,0,0,0,4,0,11,7,0,2,11],#[0,0,0,0,0,10,0,8,9,3,1,5],#[0,0,0,0,0,5,0,5,6,14,12,10],#[0,0,0,0,0,9,0,5,10,14,12,6]],![#[0,0,0,0,0,9,0,89,16,65,80,73],#[0,0,0,0,0,9,0,72,73,80,9,16],#[0,0,0,0,0,9,0,0,88,24,24,1],#[0,0,0,0,0,9,0,25,65,1,1,24],#[0,0,0,0,0,9,0,65,80,89,16,9],#[0,0,0,0,0,9,0,8,24,16,88,65],#[0,0,0,0,0,9,0,81,9,73,73,80],#[0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,9,0,72,0,80,64,89],#[0,0,0,0,0,9,0,9,9,17,73,80],#[0,0,0,0,0,9,0,16,64,8,0,25],#[0,0,0,0,0,9,0,24,65,0,1,24],#[0,0,0,0,0,9,0,64,81,88,17,8],#[0,0,0,0,0,9,0,9,25,17,89,64],#[0,0,0,0,0,9,0,80,9,72,73,80]],![#[0,0,0,0,0,5,0,7,16,19,2,23],#[0,0,0,0,0,5,0,18,16,16,20,20],#[0,0,0,0,0,5,0,17,16,18,21,22],#[0,0,0,0,0,5,0,22,16,2,2,6],#[0,0,0,0,0,5,0,7,16,1,16,5],#[0,0,0,0,0,5,0,6,16,22,6,18],#[0,0,0,0,0,5,0,3,16,22,3,18],#[0,0,0,0,0,5,0,23,16,18,19,22],#[0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,5,0,16,16,23,17,19],#[0,0,0,0,0,5,0,17,16,18,21,22],#[0,0,0,0,0,5,0,4,16,0,18,4],#[0,0,0,0,0,5,0,20,16,6,4,2],#[0,0,0,0,0,5,0,2,16,19,7,23],#[0,0,0,0,0,5,0,2,16,19,7,23]],![#[0,0,0,0,0,7,0,70,71,71,65,66],#[0,0,0,0,0,4,0,69,68,71,4,7],#[0,0,0,0,0,5,0,68,69,71,64,67],#[0,0,0,0,0,66,0,3,2,71,71,68],#[0,0,0,0,0,64,0,1,0,71,67,64],#[0,0,0,0,0,68,0,5,4,71,4,7],#[0,0,0,0,0,70,0,7,6,71,7,4],#[0,0,0,0,0,5,0,68,69,71,69,70],#[0,0,0,0,0,0,0,65,64,71,68,71],#[0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,5,0,68,69,71,64,67],#[0,0,0,0,0,64,0,1,0,71,2,1],#[0,0,0,0,0,69,0,4,5,71,6,5],#[0,0,0,0,0,67,0,2,3,71,69,70],#[0,0,0,0,0,67,0,2,3,71,65,66]],![#[0,0,0,0,0,0,0,24,25,18,24,16],#[0,0,0,0,0,2,0,25,27,16,24,19],#[0,0,0,0,0,10,0,0,19,24,24,2],#[0,0,0,0,0,16,0,1,9,2,24,25],#[0,0,0,0,0,1,0,8,24,19,24,1],#[0,0,0,0,0,1,0,11,24,19,24,2],#[0,0,0,0,0,19,0,24,10,1,24,3],#[0,0,0,0,0,2,0,16,27,16,24,26],#[0,0,0,0,0,0,0,26,25,18,24,18],#[0,0,0,0,0,2,0,27,27,16,24,17],#[0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,18,0,17,11,0,24,11],#[0,0,0,0,0,3,0,10,26,17,24,1],#[0,0,0,0,0,3,0,9,26,17,24,2],#[0,0,0,0,0,17,0,9,8,3,24,16]],![#[0,0,0,0,0,0,0,15,4,1,15,13],#[0,0,0,0,0,11,0,15,4,1,8,13],#[0,0,0,0,0,7,0,15,4,1,3,13],#[0,0,0,0,0,9,0,15,4,1,2,13],#[0,0,0,0,0,13,0,15,4,1,4,13],#[0,0,0,0,0,8,0,15,4,1,4,13],#[0,0,0,0,0,4,0,15,4,1,1,13],#[0,0,0,0,0,0,0,15,4,1,3,13],#[0,0,0,0,0,12,0,15,4,1,6,13],#[0,0,0,0,0,14,0,15,4,1,6,13],#[0,0,0,0,0,7,0,15,4,1,3,13],#[0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,5,0,15,4,1,11,13],#[0,0,0,0,0,15,0,15,4,1,9,13],#[0,0,0,0,0,6,0,15,4,1,6,13]],![#[0,0,0,0,0,5,0,10,1,1,15,8],#[0,0,0,0,0,5,0,13,6,6,15,15],#[0,0,0,0,0,2,0,6,10,13,8,3],#[0,0,0,0,0,8,0,9,15,2,2,6],#[0,0,0,0,0,9,0,7,0,12,3,9],#[0,0,0,0,0,1,0,4,11,15,11,2],#[0,0,0,0,0,15,0,14,15,5,5,6],#[0,0,0,0,0,0,0,6,8,13,10,1],#[0,0,0,0,0,12,0,15,13,4,6,4],#[0,0,0,0,0,14,0,13,13,6,4,4],#[0,0,0,0,0,2,0,6,10,13,8,3],#[0,0,0,0,0,7,0,11,2,0,13,11],#[0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,3,0,3,14,8,9,7],#[0,0,0,0,0,7,0,14,7,5,13,14]],![#[0,0,0,0,0,9,0,13,3,3,13,15],#[0,0,0,0,0,11,0,15,1,1,13,13],#[0,0,0,0,0,2,0,6,15,8,13,3],#[0,0,0,0,0,7,0,3,2,13,13,14],#[0,0,0,0,0,1,0,5,13,11,13,1],#[0,0,0,0,0,9,0,13,14,3,13,2],#[0,0,0,0,0,7,0,3,7,13,13,11],#[0,0,0,0,0,0,0,4,15,10,13,3],#[0,0,0,0,0,5,0,1,6,15,13,10],#[0,0,0,0,0,5,0,1,1,15,13,13],#[0,0,0,0,0,2,0,6,15,8,13,3],#[0,0,0,0,0,10,0,14,2,0,13,14],#[0,0,0,0,0,3,0,7,10,9,13,6],#[0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,13,0,9,5,7,13,9]],![#[0,0,0,0,0,9,0,13,10,10,13,15],#[0,0,0,0,0,11,0,13,8,8,15,15],#[0,0,0,0,0,7,0,13,4,1,3,15],#[0,0,0,0,0,6,0,13,5,2,2,15],#[0,0,0,0,0,15,0,13,12,3,11,15],#[0,0,0,0,0,5,0,13,6,11,1,15],#[0,0,0,0,0,9,0,13,10,14,13,15],#[0,0,0,0,0,0,0,13,3,6,4,15],#[0,0,0,0,0,0,0,13,3,15,4,15],#[0,0,0,0,0,14,0,13,13,6,10,15],#[0,0,0,0,0,7,0,13,4,1,3,15],#[0,0,0,0,0,3,0,13,0,0,7,15],#[0,0,0,0,0,8,0,13,11,9,12,15],#[0,0,0,0,0,13,0,13,14,12,9,15],#[0,0,0,0,0,0,0,0,0,0,0,0]]]

private def pairRight : Fin 15 → Fin 15 → Array ℕ := ![![#[0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,5,1,1,5,4],#[0,0,0,0,0,0,0,5,1,1,5,4],#[0,0,0,0,0,0,0,9,8,8,9,1],#[0,0,0,0,0,0,0,9,8,8,9,1],#[0,0,0,0,0,0,0,1,3,3,1,2],#[0,0,0,0,0,0,0,1,3,3,1,2],#[0,0,0,0,0,0,0,1,16,16,1,17],#[0,0,0,0,0,0,0,1,16,16,1,17],#[0,0,0,0,0,0,0,2,3,3,2,1],#[0,0,0,0,0,0,0,2,3,3,2,1],#[0,0,0,0,0,0,0,9,1,1,9,8],#[0,0,0,0,0,0,0,9,1,1,9,8],#[0,0,0,0,0,0,0,4,2,2,4,6],#[0,0,0,0,0,0,0,4,2,2,4,6]],![#[0,0,0,0,0,5,0,1,4,4,5,5],#[0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,5,0,1,4,4,5,5],#[0,0,0,0,0,8,0,1,9,9,8,8],#[0,0,0,0,0,4,0,2,6,6,4,4],#[0,0,0,0,0,8,0,1,9,9,8,8],#[0,0,0,0,0,4,0,2,6,6,4,4],#[0,0,0,0,0,1,0,64,65,65,1,1],#[0,0,0,0,0,2,0,3,1,1,2,2],#[0,0,0,0,0,1,0,64,65,65,1,1],#[0,0,0,0,0,2,0,3,1,1,2,2],#[0,0,0,0,0,8,0,9,1,1,8,8],#[0,0,0,0,0,1,0,3,2,2,1,1],#[0,0,0,0,0,8,0,9,1,1,8,8],#[0,0,0,0,0,1,0,3,2,2,1,1]],![#[0,0,0,0,0,2,0,0,1,3,3,0],#[0,0,0,0,0,2,0,0,1,3,3,0],#[0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,5,0,0,4,1,1,0],#[0,0,0,0,0,1,0,0,8,9,9,0],#[0,0,0,0,0,1,0,0,8,9,9,0],#[0,0,0,0,0,5,0,0,4,1,1,0],#[0,0,0,0,0,8,0,0,16,24,24,0],#[0,0,0,0,0,2,0,0,1,3,3,0],#[0,0,0,0,0,2,0,0,1,3,3,0],#[0,0,0,0,0,8,0,0,16,24,24,0],#[0,0,0,0,0,5,0,0,4,1,1,0],#[0,0,0,0,0,1,0,0,9,8,8,0],#[0,0,0,0,0,1,0,0,9,8,8,0],#[0,0,0,0,0,5,0,0,4,1,1,0]],![#[0,0,0,0,0,5,0,5,1,1,1,4],#[0,0,0,0,0,1,0,1,4,4,4,5],#[0,0,0,0,0,4,0,4,5,5,5,1],#[0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,5,0,5,1,1,1,4],#[0,0,0,0,0,1,0,1,4,4,4,5],#[0,0,0,0,0,4,0,4,5,5,5,1],#[0,0,0,0,0,9,0,9,1,1,1,8],#[0,0,0,0,0,4,0,4,2,2,2,6],#[0,0,0,0,0,3,0,3,2,2,2,1],#[0,0,0,0,0,1,0,1,2,2,2,3],#[0,0,0,0,0,9,0,9,1,1,1,8],#[0,0,0,0,0,4,0,4,2,2,2,6],#[0,0,0,0,0,3,0,3,2,2,2,1],#[0,0,0,0,0,1,0,1,2,2,2,3]],![#[0,0,0,0,0,2,0,3,0,2,0,2],#[0,0,0,0,0,2,0,6,0,2,0,2],#[0,0,0,0,0,4,0,5,0,4,0,4],#[0,0,0,0,0,2,0,3,0,2,0,2],#[0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,4,0,5,0,4,0,4],#[0,0,0,0,0,2,0,6,0,2,0,2],#[0,0,0,0,0,9,0,1,0,9,0,9],#[0,0,0,0,0,1,0,3,0,1,0,1],#[0,0,0,0,0,3,0,1,0,3,0,3],#[0,0,0,0,0,1,0,2,0,1,0,1],#[0,0,0,0,0,1,0,3,0,1,0,1],#[0,0,0,0,0,9,0,1,0,9,0,9],#[0,0,0,0,0,1,0,2,0,1,0,1],#[0,0,0,0,0,3,0,1,0,3,0,3]],![#[0,0,0,0,0,1,0,2,2,0,2,3],#[0,0,0,0,0,3,0,2,2,0,2,1],#[0,0,0,0,0,4,0,1,1,0,1,5],#[0,0,0,0,0,3,0,2,2,0,2,1],#[0,0,0,0,0,4,0,1,1,0,1,5],#[0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,1,0,2,2,0,2,3],#[0,0,0,0,0,9,0,8,8,0,8,1],#[0,0,0,0,0,2,0,1,1,0,1,3],#[0,0,0,0,0,2,0,4,4,0,4,6],#[0,0,0,0,0,1,0,3,3,0,3,2],#[0,0,0,0,0,2,0,4,4,0,4,6],#[0,0,0,0,0,1,0,3,3,0,3,2],#[0,0,0,0,0,9,0,8,8,0,8,1],#[0,0,0,0,0,2,0,1,1,0,1,3]],![#[0,0,0,0,0,1,0,3,1,3,3,1],#[0,0,0,0,0,6,0,4,6,4,4,6],#[0,0,0,0,0,1,0,4,1,4,4,1],#[0,0,0,0,0,1,0,4,1,4,4,1],#[0,0,0,0,0,6,0,4,6,4,4,6],#[0,0,0,0,0,1,0,3,1,3,3,1],#[0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,9,0,8,9,8,8,9],#[0,0,0,0,0,5,0,1,5,1,1,5],#[0,0,0,0,0,4,0,5,4,5,5,4],#[0,0,0,0,0,3,0,1,3,1,1,3],#[0,0,0,0,0,3,0,1,3,1,1,3],#[0,0,0,0,0,4,0,5,4,5,5,4],#[0,0,0,0,0,5,0,1,5,1,1,5],#[0,0,0,0,0,9,0,8,9,8,8,9]],![#[0,0,0,0,0,0,0,17,16,17,16,16],#[0,0,0,0,0,0,0,65,64,65,64,64],#[0,0,0,0,0,0,0,16,24,16,24,24],#[0,0,0,0,0,0,0,1,3,1,3,3],#[0,0,0,0,0,0,0,4,1,4,1,1],#[0,0,0,0,0,0,0,4,1,4,1,1],#[0,0,0,0,0,0,0,1,3,1,3,3],#[0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,17,16,17,16,16],#[0,0,0,0,0,0,0,65,64,65,64,64],#[0,0,0,0,0,0,0,16,24,16,24,24],#[0,0,0,0,0,0,0,1,3,1,3,3],#[0,0,0,0,0,0,0,4,1,4,1,1],#[0,0,0,0,0,0,0,4,1,4,1,1],#[0,0,0,0,0,0,0,1,3,1,3,3]],![#[0,0,0,0,0,0,0,16,0,1,17,1],#[0,0,0,0,0,0,0,3,0,2,1,2],#[0,0,0,0,0,0,0,1,0,5,4,5],#[0,0,0,0,0,0,0,2,0,4,6,4],#[0,0,0,0,0,0,0,3,0,1,2,1],#[0,0,0,0,0,0,0,8,0,9,1,9],#[0,0,0,0,0,0,0,1,0,9,8,9],#[0,0,0,0,0,0,0,16,0,1,17,1],#[0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,1,0,5,4,5],#[0,0,0,0,0,0,0,3,0,2,1,2],#[0,0,0,0,0,0,0,3,0,1,2,1],#[0,0,0,0,0,0,0,2,0,4,6,4],#[0,0,0,0,0,0,0,1,0,9,8,9],#[0,0,0,0,0,0,0,8,0,9,1,9]],![#[0,0,0,0,0,2,0,2,2,0,1,1],#[0,0,0,0,0,1,0,1,1,0,65,65],#[0,0,0,0,0,5,0,5,5,0,4,4],#[0,0,0,0,0,1,0,1,1,0,2,2],#[0,0,0,0,0,8,0,8,8,0,9,9],#[0,0,0,0,0,4,0,4,4,0,6,6],#[0,0,0,0,0,8,0,8,8,0,1,1],#[0,0,0,0,0,1,0,1,1,0,65,65],#[0,0,0,0,0,5,0,5,5,0,4,4],#[0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,2,0,2,2,0,1,1],#[0,0,0,0,0,4,0,4,4,0,6,6],#[0,0,0,0,0,8,0,8,8,0,1,1],#[0,0,0,0,0,1,0,1,1,0,2,2],#[0,0,0,0,0,8,0,8,8,0,9,9]],![#[0,0,0,0,0,5,0,4,5,5,0,1],#[0,0,0,0,0,5,0,4,5,5,0,1],#[0,0,0,0,0,8,0,16,8,8,0,24],#[0,0,0,0,0,1,0,8,1,1,0,9],#[0,0,0,0,0,2,0,1,2,2,0,3],#[0,0,0,0,0,2,0,1,2,2,0,3],#[0,0,0,0,0,1,0,9,1,1,0,8],#[0,0,0,0,0,8,0,16,8,8,0,24],#[0,0,0,0,0,5,0,4,5,5,0,1],#[0,0,0,0,0,5,0,4,5,5,0,1],#[0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,1,0,9,1,1,0,8],#[0,0,0,0,0,2,0,1,2,2,0,3],#[0,0,0,0,0,2,0,1,2,2,0,3],#[0,0,0,0,0,1,0,8,1,1,0,9]],![#[0,0,0,0,0,5,0,0,0,0,4,0],#[0,0,0,0,0,4,0,0,0,0,1,0],#[0,0,0,0,0,1,0,0,0,0,5,0],#[0,0,0,0,0,9,0,0,0,0,1,0],#[0,0,0,0,0,1,0,0,0,0,2,0],#[0,0,0,0,0,6,0,0,0,0,2,0],#[0,0,0,0,0,3,0,0,0,0,2,0],#[0,0,0,0,0,9,0,0,0,0,1,0],#[0,0,0,0,0,1,0,0,0,0,2,0],#[0,0,0,0,0,6,0,0,0,0,2,0],#[0,0,0,0,0,3,0,0,0,0,2,0],#[0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,5,0,0,0,0,4,0],#[0,0,0,0,0,4,0,0,0,0,1,0],#[0,0,0,0,0,1,0,0,0,0,5,0]],![#[0,0,0,0,0,2,0,1,3,1,2,3],#[0,0,0,0,0,2,0,3,1,3,2,1],#[0,0,0,0,0,1,0,5,4,5,1,4],#[0,0,0,0,0,4,0,6,2,6,4,2],#[0,0,0,0,0,9,0,1,8,1,9,8],#[0,0,0,0,0,3,0,2,1,2,3,1],#[0,0,0,0,0,1,0,3,2,3,1,2],#[0,0,0,0,0,9,0,1,8,1,9,8],#[0,0,0,0,0,4,0,6,2,6,4,2],#[0,0,0,0,0,1,0,3,2,3,1,2],#[0,0,0,0,0,3,0,2,1,2,3,1],#[0,0,0,0,0,2,0,1,3,1,2,3],#[0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,1,0,5,4,5,1,4],#[0,0,0,0,0,2,0,3,1,3,2,1]],![#[0,0,0,0,0,4,0,4,6,4,0,6],#[0,0,0,0,0,1,0,1,3,1,0,3],#[0,0,0,0,0,1,0,1,5,1,0,5],#[0,0,0,0,0,2,0,2,3,2,0,3],#[0,0,0,0,0,3,0,3,2,3,0,2],#[0,0,0,0,0,9,0,9,1,9,0,1],#[0,0,0,0,0,2,0,2,1,2,0,1],#[0,0,0,0,0,9,0,9,1,9,0,1],#[0,0,0,0,0,2,0,2,1,2,0,1],#[0,0,0,0,0,2,0,2,3,2,0,3],#[0,0,0,0,0,3,0,3,2,3,0,2],#[0,0,0,0,0,1,0,1,3,1,0,3],#[0,0,0,0,0,1,0,1,5,1,0,5],#[0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,4,0,4,6,4,0,6]],![#[0,0,0,0,0,4,0,0,4,6,4,0],#[0,0,0,0,0,3,0,0,3,1,3,0],#[0,0,0,0,0,4,0,0,4,1,4,0],#[0,0,0,0,0,1,0,0,1,3,1,0],#[0,0,0,0,0,1,0,0,1,5,1,0],#[0,0,0,0,0,5,0,0,5,4,5,0],#[0,0,0,0,0,9,0,0,9,8,9,0],#[0,0,0,0,0,9,0,0,9,8,9,0],#[0,0,0,0,0,5,0,0,5,4,5,0],#[0,0,0,0,0,1,0,0,1,5,1,0],#[0,0,0,0,0,1,0,0,1,3,1,0],#[0,0,0,0,0,4,0,0,4,1,4,0],#[0,0,0,0,0,3,0,0,3,1,3,0],#[0,0,0,0,0,4,0,0,4,6,4,0],#[0,0,0,0,0,0,0,0,0,0,0,0]]]

private def projectionRows : Array ℕ := #[1,2,4,8,16,11,64,71,7,64,90,28]

private def residualRows : Array ℕ := #[0,0,0,0,0,43,0,199,263,576,1114,2076]

private theorem pair_check : ∀ i j : Fin 15, i ≠ j → ∀ r : Fin 12,
    rowProduct (getElem! (pairLeft i j) r.val) (deltas ⟨i.val+1,by omega⟩) 12 ^^^
      rowProduct (getElem! (pairRight i j) r.val) (deltas ⟨j.val+1,by omega⟩) 12 =
        getElem! residualRows r.val := by decide +kernel
private theorem pair_reconstruction (i j : Fin 15) (hij : i ≠ j) :
    decode 12 (pairLeft i j) * decode 12 (deltas ⟨i.val+1,by omega⟩) +
      decode 12 (pairRight i j) * decode 12 (deltas ⟨j.val+1,by omega⟩) =
        1 - decode 12 projectionRows := by
  rw [decode_sum_mul _ _ _ _ residualRows (pair_check i j hij)]
  decide +kernel
private theorem projection_fixed (k : Fin 4) :
    generatorMatrix k * decode 12 projectionRows = decode 12 projectionRows := by
  revert k; decide +kernel

/-- The fixed subspace of one literal translation, in the original binary action. -/
def elementFixedSpace (g : M22TripleCover) : Submodule (ZMod 2) BinarySpace :=
  LinearMap.ker (binaryRepresentation g - LinearMap.id)

private theorem elementFixedSpace_mem (g : M22TripleCover) (v : BinarySpace) :
    v ∈ elementFixedSpace g ↔ binaryRepresentation g v=v := by
  simp only [elementFixedSpace,LinearMap.mem_ker,LinearMap.sub_apply,LinearMap.id_apply,sub_eq_zero]

/-- A nonidentity hexad translation has at most 256 fixed vectors. -/
theorem elementFixedSpace_card_le (g : M22TripleCover) (hg : g ∈ translations) (hne : g ≠ 1) :
    Nat.card (elementFixedSpace g) ≤ 256 := by
  obtain ⟨i,rfl⟩ := exists_word g hg
  have hi : i.val ≠ 0 := by intro he; exact hne (he ▸ rfl)
  let j : Fin 15 := ⟨i.val-1,by omega⟩
  have he : (⟨j.val+1,by omega⟩ : Fin 16)=i := Fin.ext (by dsimp [j]; omega)
  let f (v : elementFixedSpace (word i.val)) : Fin 8 → ZMod 2 :=
    rect 8 12 (singleSelector j) *ᵥ v.val
  have recover (v : elementFixedSpace (word i.val)) :
      rect 12 8 (singleInclusion j) *ᵥ f v = v.val := by
    have hv := (elementFixedSpace_mem _ _).mp v.property
    rw [binaryRepresentation_apply,word_matrix i.val i.isLt] at hv
    have hd : decode 12 (deltas i) *ᵥ v.val = 0 := by
      rw [deltas_decode,Matrix.sub_mulVec,Matrix.one_mulVec,hv,sub_self]
    have hh := congrArg (fun M : Matrix12 => M *ᵥ v.val) (single_reconstruction j)
    rw [he] at hh
    simpa only [Matrix.add_mulVec,←Matrix.mulVec_mulVec,hd,Matrix.mulVec_zero,
      add_zero,Matrix.one_mulVec] using hh
  have hinj : Function.Injective f := by
    intro v w heq
    apply Subtype.ext
    rw [←recover v,←recover w,heq]
  have hc := Nat.card_le_card_of_injective f hinj
  norm_num only [Nat.card_fun,Nat.card_fin,Nat.card_zmod] at hc
  exact hc

/-- Two distinct nonidentity translations already cut out the whole hexad fixed space. -/
theorem fixed_of_two (g k : M22TripleCover) (hg : g ∈ translations) (hk : k ∈ translations)
    (hg1 : g ≠ 1) (hk1 : k ≠ 1) (hgk : g ≠ k)
    (v : BinarySpace) (hgv : binaryRepresentation g v=v) (hkv : binaryRepresentation k v=v) :
    v ∈ fixedSpace := by
  obtain ⟨i,rfl⟩ := exists_word g hg
  obtain ⟨j,rfl⟩ := exists_word k hk
  have hi : i.val ≠ 0 := by intro he; exact hg1 (he ▸ rfl)
  have hj : j.val ≠ 0 := by intro he; exact hk1 (he ▸ rfl)
  let a : Fin 15 := ⟨i.val-1,by omega⟩
  let b : Fin 15 := ⟨j.val-1,by omega⟩
  have hai : (⟨a.val+1,by omega⟩ : Fin 16)=i := Fin.ext (by dsimp [a]; omega)
  have hbj : (⟨b.val+1,by omega⟩ : Fin 16)=j := Fin.ext (by dsimp [b]; omega)
  have hab : a ≠ b := by
    intro he
    have h := congrArg Fin.val he
    have hij : i=j := Fin.ext (by dsimp [a,b] at h; omega)
    exact hgk (hij ▸ rfl)
  have hdi : decode 12 (deltas i) *ᵥ v=0 := by
    rw [binaryRepresentation_apply,word_matrix i.val i.isLt] at hgv
    rw [deltas_decode,Matrix.sub_mulVec,Matrix.one_mulVec,hgv,sub_self]
  have hdj : decode 12 (deltas j) *ᵥ v=0 := by
    rw [binaryRepresentation_apply,word_matrix j.val j.isLt] at hkv
    rw [deltas_decode,Matrix.sub_mulVec,Matrix.one_mulVec,hkv,sub_self]
  have hh := congrArg (fun M : Matrix12 => M *ᵥ v) (pair_reconstruction a b hab)
  rw [hai,hbj] at hh
  simp only [Matrix.add_mulVec,←Matrix.mulVec_mulVec,hdi,hdj,Matrix.mulVec_zero,add_zero,
    Matrix.sub_mulVec,Matrix.one_mulVec] at hh
  have hv : decode 12 projectionRows *ᵥ v=v := (sub_eq_zero.mp hh.symm).symm
  intro t
  calc
    generatorMatrix t *ᵥ v = generatorMatrix t *ᵥ (decode 12 projectionRows *ᵥ v) := by rw [hv]
    _ = decode 12 projectionRows *ᵥ v := by rw [Matrix.mulVec_mulVec,projection_fixed]
    _ = v := hv
end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.NativeHexadBounds


namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open Subgroup Sporadic.Mathieu M22TripleCover M22TripleCover.Ambient
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Janko4.InvolutionCentralizers.First.QuotientExtension
open NativeHexadCoordinates InvariantPoint
open scoped Pointwise

/-- The fixed space of a full native actor. -/
def nativeHexadElementFixed (g : actionGroup) : Submodule (ZMod 2) BinarySpace :=
  LinearMap.ker (binaryAction g - LinearMap.id)

theorem nativeHexadElementFixed_mem (g : actionGroup) (v : BinarySpace) :
    v ∈ nativeHexadElementFixed g ↔ binaryAction g v=v := by
  simp only [nativeHexadElementFixed,LinearMap.mem_ker,LinearMap.sub_apply,LinearMap.id_apply,sub_eq_zero]

private theorem action_inverse (a : actionGroup) (v : BinarySpace) :
    binaryAction a (binaryAction a⁻¹ v)=v := by
  rw [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one]
  rfl

private theorem conjugate_fixed (a g : actionGroup) (v : BinarySpace)
    (hv : binaryAction (a*g*a⁻¹) v=v) :
    binaryAction g (binaryAction a⁻¹ v)=binaryAction a⁻¹ v := by
  have hh := congrArg (binaryAction a⁻¹) hv
  rw [←Module.End.mul_apply,←map_mul] at hh
  simpa only [inv_mul_cancel_left,mul_assoc,map_mul,Module.End.mul_apply] using hh

private theorem exists_translation {B : Finset (Fin 22)} (a : M22TripleCover)
    (ha : pointAction (coverInclusion a) • m22Hexad123=B)
    (g : actionGroup) (hg : g ∈ (nativeHexadStabilizer B).pCoreIn 2) :
    ∃ t ∈ translations, coverInclusion a * coverInclusion t * (coverInclusion a)⁻¹=g := by
  have hh := nativeHexadTwoCore_map_conj (coverInclusion a) m22Hexad123
  rw [ha,←NativeHexadRealization.translations_eq_twoCore,map_map] at hh
  exact hh.ge hg

/-- Every nonidentity actor in the whole native hexad two-core fixes at most 256 vectors. -/
theorem nativeHexadElementFixed_card_le {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (g : actionGroup) (hg : g ∈ (nativeHexadStabilizer B).pCoreIn 2) (hg1 : g ≠ 1) :
    Nat.card (nativeHexadElementFixed g) ≤ 256 := by
  obtain ⟨a,ha⟩ := nativeHexad_transporter hB
  obtain ⟨t,ht,rfl⟩ := exists_translation a ha g hg
  have ht1 : t ≠ 1 := by intro he; apply hg1; rw [he,map_one,mul_one,mul_inv_cancel]
  let f (v : nativeHexadElementFixed (coverInclusion a * coverInclusion t * (coverInclusion a)⁻¹)) :
      NativeHexadBounds.elementFixedSpace t := ⟨binaryAction (coverInclusion a)⁻¹ v.val,by
    have hv := conjugate_fixed (coverInclusion a) (coverInclusion t) v.val
      ((nativeHexadElementFixed_mem _ _).mp v.property)
    change binaryRepresentation t (binaryAction (coverInclusion a)⁻¹ v.val) -
      binaryAction (coverInclusion a)⁻¹ v.val=0
    rw [←VectorOrbits.binaryAction_cover, hv,sub_self]⟩
  have hf : Function.Injective f := by
    intro v w he
    apply Subtype.ext
    have hh := congrArg (fun u : NativeHexadBounds.elementFixedSpace t =>
      binaryAction (coverInclusion a) u.val) he
    simpa only [f,action_inverse] using hh
  exact (Nat.card_le_card_of_injective f hf).trans
    (NativeHexadBounds.elementFixedSpace_card_le t ht ht1)

/-- Two distinct nonidentity full two-core actors have the entire hexad fixed space as common fixed space. -/
theorem nativeHexadFixedSpace_of_two {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (g k : actionGroup) (hg : g ∈ (nativeHexadStabilizer B).pCoreIn 2)
    (hk : k ∈ (nativeHexadStabilizer B).pCoreIn 2)
    (hg1 : g ≠ 1) (hk1 : k ≠ 1) (hgk : g ≠ k)
    (v : BinarySpace) (hgv : binaryAction g v=v) (hkv : binaryAction k v=v) :
    v ∈ nativeHexadFixedSpace B := by
  obtain ⟨a,ha⟩ := nativeHexad_transporter hB
  obtain ⟨t,ht,rfl⟩ := exists_translation a ha g hg
  obtain ⟨u,hu,rfl⟩ := exists_translation a ha k hk
  have ht1 : t ≠ 1 := by intro he; apply hg1; rw [he,map_one,mul_one,mul_inv_cancel]
  have hu1 : u ≠ 1 := by intro he; apply hk1; rw [he,map_one,mul_one,mul_inv_cancel]
  have htu : t ≠ u := fun he => hgk (he ▸ rfl)
  have htv := conjugate_fixed (coverInclusion a) (coverInclusion t) v hgv
  have huv := conjugate_fixed (coverInclusion a) (coverInclusion u) v hkv
  rw [VectorOrbits.binaryAction_cover] at htv huv
  have hv := NativeHexadBounds.fixed_of_two t u ht hu ht1 hu1 htu
    (binaryAction (coverInclusion a)⁻¹ v) htv huv
  rw [←NativeHexadRealization.fixedSpace_eq] at hv
  have hh := nativeHexadFixedSpace_transport (coverInclusion a) m22Hexad123 _ hv
  rwa [ha,action_inverse] at hh
/-- A subgroup of the whole native hexad two-core with more than two elements has the same fixed space. -/
theorem nativeHexadFixedSpace_of_large_subgroup {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (D : Subgroup actionGroup) (hD : D ≤ (nativeHexadStabilizer B).pCoreIn 2)
    (hc : 2 < Nat.card D) (v : BinarySpace) (hv : ∀ d ∈ D, binaryAction d v=v) :
    v ∈ nativeHexadFixedSpace B := by
  classical
  let : Fintype D := Fintype.ofFinite D
  obtain ⟨g,hg⟩ := Fintype.exists_ne_of_one_lt_card
    (show 1 < Fintype.card D by rw [←Nat.card_eq_fintype_card]; omega) (1 : D)
  have hsmall : ({1,g} : Finset D).card < (Finset.univ : Finset D).card := by
    have hb : ({1,g} : Finset D).card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
    rw [Finset.card_univ,←Nat.card_eq_fintype_card]
    omega
  obtain ⟨k,_,hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall
  have hk1 : k ≠ 1 := by intro he; exact hk (Finset.mem_insert.mpr (Or.inl he))
  have hkg : k ≠ g := by intro he; exact hk (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr he)))
  exact nativeHexadFixedSpace_of_two hB g.val k.val (hD g.property) (hD k.property)
    (fun he => hg (Subtype.ext he)) (fun he => hk1 (Subtype.ext he))
    (fun he => hkg (Subtype.ext he.symm)) v (hv _ g.property) (hv _ k.property)
end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
