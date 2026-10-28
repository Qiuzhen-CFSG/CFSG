module

public import Mathlib.Data.Nat.Bits
public import Init.Data.String.Lemmas.Iterate
import all Init.Data.String.Legacy
import all Init.Data.String.Slice
import all Init.Data.String.Search

/-!
# A character-list specification of the certificate decoder

For ASCII strings, the legacy `String.splitOn` recurrence agrees with a
structural comma splitter. The proof tracks the consumed prefix and current
field, and identifies raw character access and extraction with list operations.
The standard decimal parser agrees with list iteration and a decimal fold.

This supplies kernel-checkable decoding witnesses for `Certificate.relations`;
no stored string, numerical row, or word convention is changed. The proof deliberately imports the private implementations of these core
functions locally; clients use the proved specification. The algorithm
specifications are those of Lean's `Init.Data.String.Legacy` and
`Init.Data.String.Slice` (Lean 4.33.0).
-/

@[expose] public section
open String
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.MatrixCertificate.Decoding.Ascii

private theorem zero_raw : (0 : Pos.Raw) = ⟨0⟩ := Pos.Raw.ext Pos.Raw.byteIdx_zero

def IsAscii (cs : List Char) : Prop := ∀ c ∈ cs, c.utf8Size = 1

private theorem get_skip (pre cs : List Char) (n : Nat) (h : IsAscii pre) :
    Pos.Raw.utf8GetAux (pre ++ cs) ⟨n⟩ ⟨n + pre.length⟩ =
      Pos.Raw.utf8GetAux cs ⟨n + pre.length⟩ ⟨n + pre.length⟩ := by
  induction pre generalizing n with
  | nil => simp
  | cons c pre ih =>
    have hc := h c (by simp)
    have ht : IsAscii pre := fun x hx => h x (by simp [hx])
    have hn : (⟨n⟩ : Pos.Raw) ≠ ⟨n + (c :: pre).length⟩ := by
      intro he
      have he' := congrArg Pos.Raw.byteIdx he
      change n = n + (pre.length + 1) at he'
      omega
    simp only [List.cons_append, Pos.Raw.utf8GetAux, hn, ↓reduceIte]
    have hadd : (⟨n⟩ : Pos.Raw) + c = ⟨n + 1⟩ := by
      change Pos.Raw.mk (n + c.utf8Size) = _
      rw [hc]
    rw [hadd]
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (n + 1) ht

private theorem extract_skip (pre cs : List Char) (n e : Nat) (h : IsAscii pre) :
    Pos.Raw.extract.go₁ (pre ++ cs) ⟨n⟩ ⟨n + pre.length⟩ ⟨e⟩ =
      Pos.Raw.extract.go₂ cs ⟨n + pre.length⟩ ⟨e⟩ := by
  induction pre generalizing n with
  | nil => cases cs <;> simp [Pos.Raw.extract.go₁, Pos.Raw.extract.go₂]
  | cons c pre ih =>
    have hc := h c (by simp)
    have ht : IsAscii pre := fun x hx => h x (by simp [hx])
    have hn : (⟨n⟩ : Pos.Raw) ≠ ⟨n + (c :: pre).length⟩ := by
      intro he
      have he' := congrArg Pos.Raw.byteIdx he
      change n = n + (pre.length + 1) at he'
      omega
    simp only [List.cons_append, Pos.Raw.extract.go₁, hn, ↓reduceIte]
    have hadd : (⟨n⟩ : Pos.Raw) + c = ⟨n + 1⟩ := by
      change Pos.Raw.mk (n + c.utf8Size) = _
      rw [hc]
    rw [hadd]
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (n + 1) ht

private theorem extract_take (pre cs : List Char) (n : Nat) (h : IsAscii pre) :
    Pos.Raw.extract.go₂ (pre ++ cs) ⟨n⟩ ⟨n + pre.length⟩ = pre := by
  induction pre generalizing n with
  | nil => cases cs <;> simp [Pos.Raw.extract.go₂]
  | cons c pre ih =>
    have hc := h c (by simp)
    have ht : IsAscii pre := fun x hx => h x (by simp [hx])
    have hn : (⟨n⟩ : Pos.Raw) ≠ ⟨n + (c :: pre).length⟩ := by
      intro he
      have he' := congrArg Pos.Raw.byteIdx he
      change n = n + (pre.length + 1) at he'
      omega
    simp only [List.cons_append, Pos.Raw.extract.go₂, hn, ↓reduceIte, List.cons.injEq,
      true_and]
    have hadd : (⟨n⟩ : Pos.Raw) + c = ⟨n + 1⟩ := by
      change Pos.Raw.mk (n + c.utf8Size) = _
      rw [hc]
    rw [hadd]
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (n + 1) ht

private theorem size_eq_length (cs : List Char) (h : IsAscii cs) :
    (String.ofList cs).utf8ByteSize = cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have hc := h c (by simp)
    have ht : IsAscii cs := fun x hx => h x (by simp [hx])
    rw [show c :: cs = [c] ++ cs from rfl, String.ofList_append,
      String.utf8ByteSize_append]
    simp [ih ht, hc, Nat.add_comm]

private theorem ascii_append {a b : List Char} (ha : IsAscii a) (hb : IsAscii b) : IsAscii (a ++ b) := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact ha c hc
  · exact hb c hc

private theorem get_current (pre cs : List Char) (c : Char) (hpre : IsAscii pre) :
    (⟨pre.length⟩ : Pos.Raw).get (String.ofList (pre ++ c :: cs)) = c := by
  simp only [Pos.Raw.get, String.toList_ofList, zero_raw]
  have h := get_skip pre (c :: cs) 0 hpre
  simpa only [Nat.zero_add, Pos.Raw.utf8GetAux, ↓reduceIte] using h

private theorem extract_middle (pre mid post : List Char) (hp : IsAscii pre) (hm : IsAscii mid) :
    (⟨pre.length⟩ : Pos.Raw).extract (String.ofList (pre ++ mid ++ post))
      ⟨pre.length + mid.length⟩ = String.ofList mid := by
  rw [Pos.Raw.extract]
  split
  · rename_i he
    have hm0 : mid = [] := by
      apply List.length_eq_zero_iff.mp
      change pre.length ≥ pre.length + mid.length at he
      omega
    simp [hm0]
  · simp only [String.toList_ofList, List.append_assoc, zero_raw]
    have hs := extract_skip pre (mid ++ post) 0 (pre.length + mid.length) hp
    simp only [Nat.zero_add] at hs
    rw [hs, extract_take mid post pre.length hm]

private theorem atEnd_eq (s : String) (p : Pos.Raw) :
    p.atEnd s = decide (p.byteIdx ≥ s.utf8ByteSize) := by
  cases s; cases p; rfl

def chunks : List Char → List Char → List (List Char)
  | [], acc => [acc.reverse]
  | c :: cs, acc => if c == ',' then acc.reverse :: chunks cs [] else chunks cs (c :: acc)

private theorem split_spec (cs pre mid : List Char) (r : List String)
    (hp : IsAscii pre) (hm : IsAscii mid) (hc : IsAscii cs) :
    String.splitOnAux (String.ofList (pre ++ mid ++ cs)) ","
      ⟨pre.length⟩ ⟨pre.length + mid.length⟩ 0 r =
      r.reverse ++ (chunks cs mid.reverse).map String.ofList := by
  induction cs generalizing pre mid r with
  | nil =>
    rw [String.splitOnAux.eq_def]
    have hs := size_eq_length (pre ++ mid ++ []) (ascii_append (ascii_append hp hm) hc)
    have he : (⟨pre.length + mid.length⟩ : Pos.Raw).atEnd
        (String.ofList (pre ++ mid ++ [])) = true := by
      rw [atEnd_eq, hs]
      simp
    simp only [he, ↓reduceIte, extract_middle pre mid [] hp hm, List.reverse_cons,
      chunks, List.reverse_reverse, List.map_cons, List.map_nil]
  | cons c cs ih =>
    have hcc := hc c (by simp)
    have hcs : IsAscii cs := fun x hx => hc x (by simp [hx])
    have hs := size_eq_length (pre ++ mid ++ c :: cs) (ascii_append (ascii_append hp hm) hc)
    have he : (⟨pre.length + mid.length⟩ : Pos.Raw).atEnd
        (String.ofList (pre ++ mid ++ c :: cs)) = false := by
      rw [atEnd_eq, hs]
      simp
    have hg : (⟨pre.length + mid.length⟩ : Pos.Raw).get
        (String.ofList (pre ++ mid ++ c :: cs)) = c := by
      simpa only [List.length_append] using get_current (pre ++ mid) cs c (ascii_append hp hm)
    have hn : (⟨pre.length + mid.length⟩ : Pos.Raw).next
        (String.ofList (pre ++ mid ++ c :: cs)) = ⟨pre.length + mid.length + 1⟩ := by
      simp only [Pos.Raw.next, hg]
      change Pos.Raw.mk (pre.length + mid.length + c.utf8Size) = _
      rw [hcc]
    have hsg : (0 : Pos.Raw).get "," = ',' := by decide +kernel
    have hsn : (0 : Pos.Raw).next "," = ⟨1⟩ := by decide +kernel
    have hse : (⟨1⟩ : Pos.Raw).atEnd "," = true := by decide +kernel
    have hback : (⟨pre.length + mid.length + 1⟩ : Pos.Raw).unoffsetBy ⟨1⟩ =
        ⟨pre.length + mid.length⟩ := by
      apply Pos.Raw.ext
      simp [Pos.Raw.byteIdx_unoffsetBy]
    rw [String.splitOnAux.eq_def]
    simp only [he, Bool.false_eq_true, ↓reduceIte, hg, hsg]
    by_cases hcomma : c = ','
    · subst c
      simp only [BEq.rfl, ↓reduceIte, hn, hsn, hse, hback,
        extract_middle pre mid (',' :: cs) hp hm]
      have hp' : IsAscii (pre ++ mid ++ [',']) :=
        ascii_append (ascii_append hp hm) (by
          intro x hx
          have hx' : x = ',' := by simpa using hx
          simpa [hx'] using hcc)
      have hi := ih (pre ++ mid ++ [',']) [] (String.ofList mid :: r) hp'
        (by simp [IsAscii]) hcs
      simpa [chunks, List.append_assoc, List.reverse_cons, Nat.add_assoc] using hi
    · simp only [show (c == ',') = false from beq_eq_false_iff_ne.mpr hcomma,
        Bool.false_eq_true, ↓reduceIte, Pos.Raw.unoffsetBy_zero, hn]
      have hm' : IsAscii (mid ++ [c]) := ascii_append hm (by
        intro x hx
        have hx' : x = c := by simpa using hx
        simpa [hx'] using hcc)
      have hi := ih pre (mid ++ [c]) r hp hm' hcs
      simpa [chunks, hcomma, List.append_assoc, List.reverse_append, Nat.add_assoc] using hi

theorem splitOn_eq_chunks (s : String) (h : IsAscii s.toList) :
    s.splitOn "," = (chunks s.toList []).map String.ofList := by
  have hs := split_spec s.toList [] [] [] (by simp [IsAscii]) (by simp [IsAscii]) h
  simpa only [List.nil_append, List.length_nil, List.reverse_nil, Nat.zero_add,
    String.ofList_toList, ← zero_raw, String.splitOn,
    show ("," == "") = false from rfl, Bool.false_eq_true, ↓reduceIte] using hs

def isNatChars (cs : List Char) : Bool := Id.run do
  let mut lastWasDigit := false
  for c in cs do
    if c = '_' then
      if !lastWasDigit then
        return false
      lastWasDigit := false
    else if c.isDigit then
      lastWasDigit := true
    else
      return false
  return lastWasDigit

def natChars (cs : List Char) : Nat :=
  if isNatChars cs then
    cs.foldl (fun n c => if c = '_' then n else n * 10 + (c.toNat - '0'.toNat)) 0
  else 0

theorem toNat_eq_chars (s : String) : s.toNat! = natChars s.toList := by
  simp only [String.toNat!, String.Slice.toNat!, String.Slice.isNat, natChars,
    isNatChars, String.Slice.forIn_eq_forIn_toList, String.Slice.foldl_eq_foldl_toList,
    String.copy_toSlice]
  rfl

def decode (cs : List Char) : List Nat := (chunks cs []).map natChars

theorem decode_correct (s : String) (ns : List Nat)
    (h : s.toList.all (fun c => c.utf8Size == 1) = true ∧ decode s.toList = ns) :
    (s.splitOn ",").map String.toNat! = ns := by
  have ha : IsAscii s.toList := by
    intro c hc
    exact beq_iff_eq.mp ((List.all_eq_true.mp h.1) c hc)
  rw [splitOn_eq_chunks s ha, List.map_map]
  simpa only [decode, Function.comp_def, toNat_eq_chars, String.toList_ofList] using h.2

/-- Decode a supplied character list, preserving the standard string operations. -/
theorem decode_of_chars (cs : List Char) (ns : List Nat)
    (h : cs.all (fun c => c.utf8Size == 1) = true ∧ decode cs = ns) :
    ((String.ofList cs).splitOn ",").map String.toNat! = ns := by
  apply decode_correct
  simpa only [String.toList_ofList] using h

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.MatrixCertificate.Decoding.Ascii

