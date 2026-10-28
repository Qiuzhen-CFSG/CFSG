module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness.Calibration.Arithmetic

/-!
# Sound row-based calibration certificates

The ambient form is checked by packed upper-triangle slices, a zero diagonal,
and symmetry. Sequential XOR products then compute the first 56 transported
rows. The final tests read all selected upper entries and every mixed entry.
These Boolean tests imply the unchanged `Calibration` contract.

Source: `../../source/README.md` and the two enclosing source descriptions.
The literal `topColumns` is proved equal to the actual adapted transpose rows.
-/

@[expose] public section
namespace Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness.CalibrationProof
open Coordinates GeneratorCertificates
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates
open LinearMembership FiniteAlgebra

def topColumns : Vector ℕ 56 := ⟨#[3824690266246331066892070875819768,4322447451596705379448573341302731,4385764471760031253324242545676121,1317401710680839717783834227253783,243863764823993738375629132190670,3426386148003598003950138940067139,1256552336998551619415681600883595,2105452220279034821000874489985746,4866475358535012974804560050507382,539402814366151860496702054930501,1698818343964591067974471106683631,4924842612250112420094850040637521,2980220337552622463764080301401671,2943211541774629226394832399528321,4040837349671752757492439697511508,1717635849537985443889629518489443,1268059120391916299135911076050271,1108716700486700507357624808381289,1895918477255597517308660121924082,1579070908557938722410635695450179,3843985813321468109689578414692791,2922380451488112247094361963603547,1501691482739802478489232187967498,3227722958098730794502888610781146,601292760429643509707691933146308,4025945030549175072818991851270603,4487689073965534983463359720707225,3056819453020398733030967619185187,804290226362701785618512712504171,1349516414323835963488147939483417,2597118653363837323212229659924752,3591666896476278199286886942401173,2620021868496710595220745676051430,189385749873103439254496370866467,4678722160720404998058350207365350,1886348489161472377194262151531886,4767047145431281123326744683429831,402637314796318085043770901912954,5172485936496158591346581409120779,1293331900776774701879724120217259,3288171867551513974617728125809271,2789136495852503355611436895321605,1606159905212880067269252479578462,4253500551798606224279055014243475,2757331652453088630310254089115600,4607344961116664708071954388271758,2626294986360808389553689287116263,4883743579600552769511800898958115,4721039082899318536957631447284400,4644285345197419168271196665608587,2265103088141658312896961339255888,2754247354173393673337105390113823,4759096582612750366863054333781044,1806533798730719510056345884899479,2484315614695389101096673282012918,1898204497659704399057551737654819], rfl⟩

theorem topTranspose_eq_columns : topTranspose = topColumns := by
  apply Vector.ext
  intro a ha
  change topTranspose.get ⟨a, ha⟩ = topColumns.get ⟨a, ha⟩
  simp only [topTranspose, get_ofFn]
  exact (by decide +kernel : ∀ a : Fin 56,
    adaptedTransposeRows.get (Fin.castAdd 56 a) = topColumns.get a) ⟨a, ha⟩

def allIndexed {α : Type} (p : ℕ → α → Bool) : ℕ → List α → Bool
  | _, [] => true
  | j, c :: cs => p j c && allIndexed p (j+1) cs

def symmetricFrom : ℕ → List ℕ → Bool
  | _, [] => true
  | a, x :: xs => allIndexed (fun b y => x.testBit b == y.testBit a) (a+1) xs &&
      symmetricFrom (a+1) xs

def ambientTest (word : ℕ) (xs : Vector ℕ 112) : Bool :=
  symmetricFrom 0 xs.toList &&
  allIndexed (fun a row => !(row.testBit a) &&
    (row >>> (a+1) == (word >>> (a*(223-a)/2)) % 2^(111-a))) 0 xs.toList

def productTest {m n : ℕ} (xs : Vector ℕ m) (ys : Vector ℕ n) (zs : Vector ℕ m) : Bool :=
  xs.toList.map (fun row => scan row ys.toList) == zs.toList

def upperTest (i : ℕ) (top : Vector ℕ 56) : Bool :=
  (evaluationRows.toList.zip upperPositions.toList).all (fun (row,p) =>
    row.testBit i == (top.get p.1).testBit p.2.val)

def mixedTest (word : ℕ) (top : Vector ℕ 56) : Bool :=
  allIndexed (fun a row => (word >>> (56*a)) % 2^56 == row >>> 56) 0 top.toList


private theorem get_eq_index {α : Type} {n : ℕ} (v : Vector α n) (i : Fin n) :
    v.get i = v[i.val] := by
  unfold Vector.get
  exact Vector.getElem_toArray _

private theorem allIndexed_spec {α : Type} (p : ℕ → α → Bool) (xs : List α)
    (j : ℕ) (h : allIndexed p j xs = true) :
    ∀ i (hi : i < xs.length), p (j+i) xs[i] = true := by
  induction xs generalizing j with
  | nil => simp
  | cons x xs ih =>
    simp only [allIndexed, Bool.and_eq_true] at h
    intro i hi
    cases i with
    | zero => simpa using h.1
    | succ i => simpa [Nat.add_assoc, Nat.add_comm 1] using ih (j+1) h.2 i (by simpa using hi)

private theorem symmetricFrom_spec (a : ℕ) (xs : List ℕ)
    (h : symmetricFrom a xs = true) :
    ∀ i (hi : i < xs.length) j (hj : j < xs.length),
      xs[i].testBit (a+j) = xs[j].testBit (a+i) := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [symmetricFrom, Bool.and_eq_true] at h
    intro i hi j hj
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        have he := allIndexed_spec _ _ _ h.1 j (by simpa using hj)
        simpa [Nat.add_assoc, Nat.add_comm 1] using he
    | succ i =>
      cases j with
      | zero =>
        have he := allIndexed_spec _ _ _ h.1 i (by simpa using hi)
        simp only [beq_iff_eq] at he
        simpa [Nat.add_assoc, Nat.add_comm 1] using he.symm
      | succ j =>
        simpa [Nat.add_assoc, Nat.add_comm 1] using
          ih (a+1) h.2 i (by simpa using hi) j (by simpa using hj)

theorem ambientTest_sound (word : ℕ) (xs : Vector ℕ 112) (h : ambientTest word xs = true) :
    ∀ a b : Fin 112, (xs.get a).testBit b.val =
    if a < b then word.testBit (exteriorIndex a b)
    else if b < a then word.testBit (exteriorIndex b a) else false := by
  simp only [ambientTest, Bool.and_eq_true] at h
  have hup (a b : Fin 112) (hab : a < b) :
      (xs.get a).testBit b.val = word.testBit (exteriorIndex a b) := by
    have ha := allIndexed_spec _ _ _ h.2 a.val (by simp)
    simp only [Nat.zero_add, Bool.and_eq_true, beq_iff_eq,
      Vector.getElem_toList, ← get_eq_index] at ha
    have he := congrArg (fun x : ℕ => x.testBit (b.val-a.val-1)) ha.2
    have hi : b.val-a.val-1 < 111-a.val := by omega
    have hb : a.val+1+(b.val-a.val-1) = b.val := by omega
    simpa only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, hi, decide_true,
      Bool.true_and, hb, exteriorIndex] using he
  intro a b
  by_cases hab : a < b
  · simpa only [hab, if_pos] using hup a b hab
  · by_cases hba : b < a
    · have hs := symmetricFrom_spec 0 xs.toList h.1 a.val (by simp) b.val (by simp)
      simp only [Nat.zero_add, Vector.getElem_toList, ← get_eq_index] at hs
      simpa only [hab, hba, if_pos, if_false] using hs.trans (hup b a hba)
    · have he : b = a := by omega
      subst b
      have ha := allIndexed_spec _ _ _ h.2 a.val (by simp)
      simp only [Bool.and_eq_true] at ha
      simpa only [Nat.zero_add, Bool.not_eq_true',
        Vector.getElem_toList, ← get_eq_index, lt_self_iff_false, if_false] using ha.1

theorem productTest_sound {m n : ℕ} (xs : Vector ℕ m) (ys : Vector ℕ n)
    (zs : Vector ℕ m) (h : productTest xs ys zs = true) :
    ∀ a, scan (xs.get a) ys.toList = zs.get a := by
  simp only [productTest, beq_iff_eq] at h
  intro a
  have he := congrArg (fun l : List ℕ => l[a.val]?) h
  simpa only [List.getElem?_map, Vector.getElem?_toList,
    Vector.getElem?_eq_getElem a.isLt, Option.map_some, Option.some.injEq,
    ← get_eq_index] using he

attribute [local irreducible] evaluationRows upperPositions originalMixedWords exteriorFormRows

theorem upperTest_sound (i : ℕ) (top : Vector ℕ 56) (h : upperTest i top = true) :
    ∀ t : Fin 595, (evaluationRows.get t).testBit i =
      (top.get (upperPositions.get t).1).testBit (upperPositions.get t).2.val := by
  intro t
  have ht : t.val < (evaluationRows.toList.zip upperPositions.toList).length := by simp
  have he := (List.all_eq_true.mp h) _ (List.getElem_mem ht)
  simpa only [List.getElem_zip, Vector.getElem_toList, ← get_eq_index, beq_iff_eq] using he

theorem mixedTest_sound (word : ℕ) (top : Vector ℕ 56) (h : mixedTest word top = true) :
    ∀ a b : Fin 56, word.testBit (56*a.val+b.val) = (top.get a).testBit (56+b.val) := by
  intro a b
  have ha := allIndexed_spec _ _ _ h a.val (by simp)
  simp only [Nat.zero_add, beq_iff_eq, Vector.getElem_toList, ← get_eq_index] at ha
  have hb := congrArg (fun x : ℕ => x.testBit b.val) ha
  simpa only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
    b.isLt, decide_true, Bool.true_and] using hb

theorem calibration_of_tests (i : Fin 1221) (word mixed : ℕ)
    (ambient : Vector ℕ 112) (left top : Vector ℕ 56)
    (hw : exteriorFormRows.get i = word) (hm : originalMixedWords.get i = mixed)
    (ha : ambientTest word ambient = true)
    (hl : productTest topColumns ambient left = true)
    (ht : productTest left adaptedRows top = true)
    (hu : upperTest i.val top = true)
    (hmix : mixedTest mixed top = true) : Calibration i := by
  apply calibration_of_checks i ambient left top
  exact ⟨hw.symm ▸ ambientTest_sound word ambient ha,
    (by rw [topTranspose_eq_columns]; exact productTest_sound _ _ _ hl), productTest_sound _ _ _ ht,
    upperTest_sound _ _ hu, hm.symm ▸ mixedTest_sound mixed top hmix⟩

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness.CalibrationProof
