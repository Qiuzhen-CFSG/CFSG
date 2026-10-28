module

public import Theory.Representation.HigmanSims.Twenty.Marked

/-!
# Checked lift identities for the HS comparison

The twenty ATLAS-compatible lift rows and the all-one row are independent,
as certified by a 21-column minor and its right inverse. Pullback by the
literal inverse ATLAS generators has the stated action on these rows.
These identities use no assertion about the graph used to discover them.

Source: ATLAS HSG1-p100B0 and HSG1-f2r20B0; candidate data and provenance
in `../source/README.md` and `../source/comparison.json`.
-/

@[expose] public section
namespace Sporadic.LeechRelated.HS.Twenty.Comparison
open scoped BigOperators Matrix
open Thompson.BinaryMatrix

private def checkFin {n : ℕ} (f : Fin n → Bool) : Bool :=
  (List.range n).all (fun i => if h : i < n then f ⟨i, h⟩ else true)

private theorem allFin {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    (h : checkFin (fun i => decide (P i)) = true) : ∀ i, P i := by
  intro i
  have hi := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  simpa only [dif_pos i.isLt, decide_eq_true_eq] using hi

def liftRows : Array ℕ := #[1136493975753506083926175612517, 757167536655620411908553086178, 822333313485570301799864733138, 631080992016669636897861399892, 1139855559681423044331968267739, 814958803305101796760356006970, 485971370704335211887853462251, 262246861182738602304065065973, 918454361582002501704566409870, 545239007268541225887180448210, 125785284550161567000828251274, 1087375590856054926076727531801, 30050016297924958217903599860, 177934340152998201731084686104, 363814290195608035679770087861, 1265142778919677952843306373048, 1215030913999444091234814275354, 94609176117251882974484674852, 1052941829384287716538972253472, 264051202405273271979863804718, 1267650600228229401496703205375]

def lifts : Matrix (Fin 21) (Fin 100) (ZMod 2) :=
  fun i j => bit liftRows[i.val]! j.val

def pivots : Fin 21 → Fin 100 :=
  fun i => ⟨(#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21] : Array ℕ)[i.val]! % 100, Nat.mod_lt _ (by decide)⟩

private def pivotRows : Array ℕ := #[2063973, 431330, 527826, 390484, 656859, 142394, 1991403, 873461, 1804942, 1237458, 1248394, 1055001, 1896692, 758552, 1151413, 1707960, 274202, 309540, 142624, 887598, 2097151]

private def pivotInvRows : Array ℕ := #[1375182, 727796, 1658415, 1464494, 1354900, 89953, 382211, 1105595, 913134, 1634900, 1450824, 144595, 1634310, 1847731, 1967223, 319130, 1586450, 38823, 1430620, 1262761, 77263]

private theorem pivot_decode : lifts.submatrix id pivots = decode 21 pivotRows := by
  decide +kernel

private theorem pivot_inverse : lifts.submatrix id pivots * decode 21 pivotInvRows = 1 := by
  rw [pivot_decode]
  apply decode_mul_one
  decide +kernel

theorem lifts_injective : Function.Injective lifts.vecMulLinear := by
  intro x y h
  have hp : x ᵥ* lifts.submatrix id pivots = y ᵥ* lifts.submatrix id pivots := by
    funext j
    exact congrFun h (pivots j)
  have hi := congrArg (fun v => v ᵥ* decode 21 pivotInvRows) hp
  simpa only [Matrix.vecMul_vecMul, pivot_inverse, Matrix.vecMul_one] using hi

theorem lifts_independent : LinearIndependent (ZMod 2) lifts.row :=
  (Matrix.vecMul_injective_iff (M := lifts)).mp lifts_injective

theorem lifts_last : lifts (Fin.last 20) = fun _ => 1 := by
  decide +kernel

private def tableA (i : Fin 100) : Fin 100 :=
  ⟨(3838723257997737152524899170929934947202430479706805946343499194866484018493252410823467695167791695081756400242119444822672887673306494670569625348565932927976040876586221373003419306020058828375383269105214395 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem tableA_eq : tableA = HS.generatorA := by
  funext i
  exact (allFin (fun j => tableA j = HS.generatorA j) (by decide +kernel)) i

private def pulledRowsA : Array ℕ := #[510483063572608989588150119197, 131156624474723317570527592858, 1139855559681423044331968267739, 781679229523894189608849743124, 822333313485570301799864733138, 349196238646226899792136795505, 636569608211559764598841805483, 180275009372174475419975673574, 452691796923127604736347198405, 1089716260075231199765618519271, 363814290195608035679770087861, 1005403739045490799192638139402, 1209435757119371102683334851721, 722411592959688175609522757165, 125785284550161567000828251274, 711968608139858780617097912316, 195459432488156733757043410808, 1193763091156759684627098429449, 508416564480845759871214610772, 263941159425674461920823444296, 1267650600228229401496703205375]

def extendedRowsA : Array ℕ := #[1048578, 1048577, 16, 1048640, 4, 1048832, 1048584, 1050624, 1048608, 1056768, 16384, 1048704, 1070388, 1049088, 1024, 41495, 67735, 1261334, 1328416, 605750, 1048576]

def extendedA : Matrix (Fin 21) (Fin 21) (ZMod 2) := decode 21 extendedRowsA

theorem pull_lifts_a :
    (fun i j => lifts i (HS.generatorA j)) = extendedA * lifts := by
  have hp : ∀ i : Fin 21, ∀ j : Fin 100,
      bit liftRows[i.val]! (tableA j).val = bit pulledRowsA[i.val]! j.val := by
    decide +kernel
  have hm : ∀ i : Fin 21,
      rowProduct extendedRowsA[i.val]! liftRows 21 = pulledRowsA[i.val]! := by
    decide +kernel
  ext i j
  rw [← tableA_eq]
  change bit liftRows[i.val]! (tableA j).val =
    ∑ k : Fin 21, bit extendedRowsA[i.val]! k.val * bit liftRows[k.val]! j.val
  rw [Fin.sum_univ_eq_sum_range (fun k =>
    bit extendedRowsA[i.val]! k * bit liftRows[k]! j.val), ← bit_rowProduct, hm, hp]

theorem extendedA_top :
    extendedA.submatrix Fin.castSucc Fin.castSucc = aMatrix := by
  decide +kernel

private def tableB (i : Fin 100) : Fin 100 :=
  ⟨(1584088533044622539624716012360915100311113938083754946662587072801676726706164344372852891441442777957300990173557581617101002762039959730741693432191260900145476108926406488416286385789713123784992907581461166 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem tableB_eq : tableB = HS.generatorB := by
  funext i
  exact (allFin (fun j => tableB j = HS.generatorB j) (by decide +kernel)) i

private def pulledRowsB : Array ℕ := #[445317286742659099696838472237, 636569608211559764598841805483, 814958803305101796760356006970, 262246861182738602304065065973, 266203146118898169941089978787, 545239007268541225887180448210, 125785284550161567000828251274, 1184598568443227542815116463892, 30050016297924958217903599860, 588743429549901527765567947168, 2507821308551448653396832327, 1215030913999444091234814275354, 1173041424110977518522218530523, 214708770843941684957730951903, 264051202405273271979863804718, 264090924184018856036745460073, 933730447697759058879392788664, 390341704772667387397135939113, 447142792360832184401605472690, 693568682251339698984262253582, 1267650600228229401496703205375]

def extendedRowsB : Array ℕ := #[1048580, 1048584, 32, 128, 181, 512, 1024, 1049106, 4096, 1049125, 1081344, 65536, 1179648, 1310720, 524288, 336017, 216518, 938386, 191412, 714779, 1048576]

def extendedB : Matrix (Fin 21) (Fin 21) (ZMod 2) := decode 21 extendedRowsB

theorem pull_lifts_b :
    (fun i j => lifts i (HS.generatorB j)) = extendedB * lifts := by
  have hp : ∀ i : Fin 21, ∀ j : Fin 100,
      bit liftRows[i.val]! (tableB j).val = bit pulledRowsB[i.val]! j.val := by
    decide +kernel
  have hm : ∀ i : Fin 21,
      rowProduct extendedRowsB[i.val]! liftRows 21 = pulledRowsB[i.val]! := by
    decide +kernel
  ext i j
  rw [← tableB_eq]
  change bit liftRows[i.val]! (tableB j).val =
    ∑ k : Fin 21, bit extendedRowsB[i.val]! k.val * bit liftRows[k.val]! j.val
  rw [Fin.sum_univ_eq_sum_range (fun k =>
    bit extendedRowsB[i.val]! k * bit liftRows[k]! j.val), ← bit_rowProduct, hm, hp]

theorem extendedB_top :
    extendedB.submatrix Fin.castSucc Fin.castSucc = bMatrix := by
  decide +kernel

end Sporadic.LeechRelated.HS.Twenty.Comparison
