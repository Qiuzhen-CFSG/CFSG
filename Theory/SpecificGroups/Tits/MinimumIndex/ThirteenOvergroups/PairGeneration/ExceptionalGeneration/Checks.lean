module

public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.ExceptionalGeneration.Support

/-!
# Kernel checks for all 27 exceptional thirteen-pairs

Each pair of signed recovery words recovers the two targets of `Support`
after conjugation by an actual standard-generator word. These are literal
three-point equalities in the certified faithful permutation representation.

Source: the primary ATLAS Tits generators and max1, max2, max4 programs.
`source/witnesses.json` preserves untrusted GAP output; `source/generate.py`
reproduces this module. See `source/README.md` for attribution and conventions.
-/

namespace Tits.MinimumIndexThirteen.PairGeneration.ExceptionalGeneration
set_option Elab.async false

private def conjugator1 : Nat := 154041958151552792654108706073171371
private def first1 : List (Bool × Int) := [(true, -1), (false, 3), (true, 1)]
private def second1 : List (Bool × Int) := [(false, 1), (true, 2), (false, -1), (true, 1), (false, -1), (true, -1)]

set_option maxRecDepth 20000 in
private theorem checked1 :
    recoveryTest 1 conjugator1 0 false first1 = true ∧
    recoveryTest 1 conjugator1 0 true second1 = true := by
  decide +kernel

private def conjugator2 : Nat := 55221782609031918460951402
private def first2 : List (Bool × Int) := [(false, -2), (true, -3), (false, 1)]
private def second2 : List (Bool × Int) := [(false, 2), (true, 1), (false, -2), (true, -1), (false, -2), (true, 1)]

set_option maxRecDepth 20000 in
private theorem checked2 :
    recoveryTest 2 conjugator2 0 false first2 = true ∧
    recoveryTest 2 conjugator2 0 true second2 = true := by
  decide +kernel

private def conjugator3 : Nat := 12798120129463564742662933346846707968618952374191130929430832081644245
private def first3 : List (Bool × Int) := [(true, 1), (false, 1), (true, 2), (false, 1), (true, -1), (false, 1), (true, -2), (false, 2), (true, -1)]
private def second3 : List (Bool × Int) := [(true, 1), (false, 1), (true, 1), (false, 1), (true, -6)]

set_option maxRecDepth 20000 in
private theorem checked3 :
    recoveryTest 3 conjugator3 0 false first3 = true ∧
    recoveryTest 3 conjugator3 0 true second3 = true := by
  decide +kernel

private def conjugator4 : Nat := 7073856676663147769633790827
private def first4 : List (Bool × Int) := [(true, 2), (false, -2), (true, 1), (false, 2), (true, -1)]
private def second4 : List (Bool × Int) := [(true, -2), (false, -2), (true, -3), (false, -2)]

set_option maxRecDepth 20000 in
private theorem checked4 :
    recoveryTest 4 conjugator4 0 false first4 = true ∧
    recoveryTest 4 conjugator4 0 true second4 = true := by
  decide +kernel

private def conjugator5 : Nat := 428216787211249436154709
private def first5 : List (Bool × Int) := [(false, 1), (true, 2), (false, 2), (true, 1), (false, -1), (true, -1), (false, 1)]
private def second5 : List (Bool × Int) := [(false, 1), (true, -2), (false, -3), (true, 1)]

set_option maxRecDepth 20000 in
private theorem checked5 :
    recoveryTest 5 conjugator5 0 false first5 = true ∧
    recoveryTest 5 conjugator5 0 true second5 = true := by
  decide +kernel

private def conjugator18 : Nat := 152853249731062038225559582992213965438395944258500336041961792656746
private def first18 : List (Bool × Int) := [(false, -4), (true, 1), (false, 1), (true, 3), (false, 1)]
private def second18 : List (Bool × Int) := [(true, -1), (false, 1), (true, -2), (false, 1), (true, 1), (false, -2), (true, -1), (false, -2), (true, -1), (false, -1)]

set_option maxRecDepth 20000 in
private theorem checked18 :
    recoveryTest 18 conjugator18 2 false first18 = true ∧
    recoveryTest 18 conjugator18 2 true second18 = true := by
  decide +kernel

private def conjugator56 : Nat := 22740061325245143043692410836817723393042450581440781163
private def first56 : List (Bool × Int) := [(false, 3), (true, 3), (false, 1), (true, 1), (false, 1)]
private def second56 : List (Bool × Int) := [(false, 2), (true, -1), (false, 2), (true, 1), (false, -3), (true, 1), (false, -1), (true, -1), (false, -1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1)]

set_option maxRecDepth 20000 in
private theorem checked56 :
    recoveryTest 56 conjugator56 2 false first56 = true ∧
    recoveryTest 56 conjugator56 2 true second56 = true := by
  decide +kernel

private def conjugator239 : Nat := 5761565894932995549912122863323044679750637733934011728267108047836522
private def first239 : List (Bool × Int) := [(false, 4), (true, 2), (false, 1), (true, -1)]
private def second239 : List (Bool × Int) := [(true, 3), (false, -1), (true, 1), (false, 1), (true, 5), (false, 1), (true, -1)]

set_option maxRecDepth 20000 in
private theorem checked239 :
    recoveryTest 239 conjugator239 2 false first239 = true ∧
    recoveryTest 239 conjugator239 2 true second239 = true := by
  decide +kernel

private def conjugator520 : Nat := 46032654648656749542112526371590997454410577199560007723733
private def first520 : List (Bool × Int) := [(false, -4), (true, -1), (false, -1), (true, -1), (false, -1), (true, 1)]
private def second520 : List (Bool × Int) := [(false, -1), (true, -2), (false, -2), (true, 1), (false, -2)]

set_option maxRecDepth 20000 in
private theorem checked520 :
    recoveryTest 520 conjugator520 2 false first520 = true ∧
    recoveryTest 520 conjugator520 2 true second520 = true := by
  decide +kernel

private def conjugator715 : Nat := 2568480882014432533002397390459770506972372148235432888136255197130031584683
private def first715 : List (Bool × Int) := [(true, 2), (false, -3), (true, 1), (false, 2), (true, 2)]
private def second715 : List (Bool × Int) := [(true, 3), (false, -1), (true, -2), (false, -3), (true, 1), (false, 1), (true, 3)]

set_option maxRecDepth 20000 in
private theorem checked715 :
    recoveryTest 715 conjugator715 1 false first715 = true ∧
    recoveryTest 715 conjugator715 1 true second715 = true := by
  decide +kernel

private def conjugator726 : Nat := 3533514766890005236993665878
private def first726 : List (Bool × Int) := [(true, 6), (false, 2), (true, -1), (false, 1), (true, -1)]
private def second726 : List (Bool × Int) := [(false, -2), (true, 5), (false, -2), (true, 6), (false, 2), (true, 3), (false, -1)]

set_option maxRecDepth 20000 in
private theorem checked726 :
    recoveryTest 726 conjugator726 2 false first726 = true ∧
    recoveryTest 726 conjugator726 2 true second726 = true := by
  decide +kernel

private def conjugator937 : Nat := 9296220484623979934991172590443
private def first937 : List (Bool × Int) := [(true, -3), (false, 1), (true, -1)]
private def second937 : List (Bool × Int) := [(true, 2), (false, -5), (true, -3)]

set_option maxRecDepth 20000 in
private theorem checked937 :
    recoveryTest 937 conjugator937 2 false first937 = true ∧
    recoveryTest 937 conjugator937 2 true second937 = true := by
  decide +kernel

private def conjugator1003 : Nat := 86717938268810123858866120283990128539481488666037
private def first1003 : List (Bool × Int) := [(false, 6), (true, -1), (false, -1), (true, 1), (false, -3)]
private def second1003 : List (Bool × Int) := [(true, -1), (false, 1), (true, 2), (false, 2), (true, 1), (false, 1), (true, -1), (false, 6), (true, 1), (false, 1), (true, -2)]

set_option maxRecDepth 20000 in
private theorem checked1003 :
    recoveryTest 1003 conjugator1003 2 false first1003 = true ∧
    recoveryTest 1003 conjugator1003 2 true second1003 = true := by
  decide +kernel

private def conjugator1022 : Nat := 1232335665212425380334520735052248426
private def first1022 : List (Bool × Int) := [(true, -2), (false, -1), (true, -2), (false, -2), (true, -2), (false, 1), (true, 2), (false, -1)]
private def second1022 : List (Bool × Int) := [(true, -2), (false, -1), (true, -1), (false, -1), (true, -1), (false, 1)]

set_option maxRecDepth 20000 in
private theorem checked1022 :
    recoveryTest 1022 conjugator1022 2 false first1022 = true ∧
    recoveryTest 1022 conjugator1022 2 true second1022 = true := by
  decide +kernel

private def conjugator1441 : Nat := 36783633758976502494231483829
private def first1441 : List (Bool × Int) := [(true, -1), (false, 1), (true, 1), (false, -1), (true, -1), (false, -5), (true, 2), (false, -2), (true, -1)]
private def second1441 : List (Bool × Int) := [(true, -2), (false, 1), (true, -1), (false, -3)]

set_option maxRecDepth 20000 in
private theorem checked1441 :
    recoveryTest 1441 conjugator1441 2 false first1441 = true ∧
    recoveryTest 1441 conjugator1441 2 true second1441 = true := by
  decide +kernel

private def conjugator1449 : Nat := 36783633758976502494231483829
private def first1449 : List (Bool × Int) := [(true, -6), (false, -1), (true, -1), (false, -5), (true, -1), (false, -1)]
private def second1449 : List (Bool × Int) := [(false, -2), (true, 1), (false, -1), (true, 6), (false, -2), (true, -1), (false, -1), (true, -1), (false, -1), (true, -2), (false, -1)]

set_option maxRecDepth 20000 in
private theorem checked1449 :
    recoveryTest 1449 conjugator1449 2 false first1449 = true ∧
    recoveryTest 1449 conjugator1449 2 true second1449 = true := by
  decide +kernel

private def conjugator1633 : Nat := 2983748456912790132263514774996043225461595785248838227023275
private def first1633 : List (Bool × Int) := [(true, -1), (false, 2), (true, -2), (false, -2), (true, -2), (false, 4), (true, -1), (false, -2), (true, -4), (false, -1)]
private def second1633 : List (Bool × Int) := [(false, -1), (true, 1), (false, -1), (true, -3), (false, -5)]

set_option maxRecDepth 20000 in
private theorem checked1633 :
    recoveryTest 1633 conjugator1633 2 false first1633 = true ∧
    recoveryTest 1633 conjugator1633 2 true second1633 = true := by
  decide +kernel

private def conjugator1877 : Nat := 1060213412765517488533255694833353630119837386321237
private def first1877 : List (Bool × Int) := [(true, 1), (false, -1), (true, -1), (false, 2), (true, -3), (false, 3), (true, 1), (false, 1)]
private def second1877 : List (Bool × Int) := [(true, 2), (false, -1), (true, -1), (false, 1), (true, 2), (false, 4), (true, 1), (false, 1)]

set_option maxRecDepth 20000 in
private theorem checked1877 :
    recoveryTest 1877 conjugator1877 1 false first1877 = true ∧
    recoveryTest 1877 conjugator1877 1 true second1877 = true := by
  decide +kernel

private def conjugator1879 : Nat := 8688703204849541195362328750954
private def first1879 : List (Bool × Int) := [(true, -1), (false, 1), (true, -2), (false, 2), (true, -1), (false, 3)]
private def second1879 : List (Bool × Int) := [(false, -3), (true, -1), (false, 2), (true, 2)]

set_option maxRecDepth 20000 in
private theorem checked1879 :
    recoveryTest 1879 conjugator1879 2 false first1879 = true ∧
    recoveryTest 1879 conjugator1879 2 true second1879 = true := by
  decide +kernel

private def conjugator1997 : Nat := 339226161541236874083150784034592135756652129717
private def first1997 : List (Bool × Int) := [(false, -1), (true, 2), (false, 1), (true, -2), (false, 1), (true, 2), (false, -1), (true, 2), (false, 1), (true, 1), (false, 1), (true, 1), (false, -3)]
private def second1997 : List (Bool × Int) := [(false, 1), (true, 1), (false, -1), (true, -1), (false, 2), (true, 5)]

set_option maxRecDepth 20000 in
private theorem checked1997 :
    recoveryTest 1997 conjugator1997 2 false first1997 = true ∧
    recoveryTest 1997 conjugator1997 2 true second1997 = true := by
  decide +kernel

private def conjugator2218 : Nat := 2983748456912790132263514774996043225461595785248838227023275
private def first2218 : List (Bool × Int) := [(true, -3), (false, 2), (true, 1), (false, -4), (true, -2), (false, -2), (true, -3), (false, -2)]
private def second2218 : List (Bool × Int) := [(true, -1), (false, -2), (true, -1), (false, -1), (true, -1), (false, -2), (true, 3)]

set_option maxRecDepth 20000 in
private theorem checked2218 :
    recoveryTest 2218 conjugator2218 2 false first2218 = true ∧
    recoveryTest 2218 conjugator2218 2 true second2218 = true := by
  decide +kernel

private def conjugator2405 : Nat := 47271055114151544353487791607951255072241866221448624409597290
private def first2405 : List (Bool × Int) := [(true, -6), (false, -1), (true, -2), (false, -1), (true, -1), (false, -3)]
private def second2405 : List (Bool × Int) := [(false, 1), (true, -1), (false, -2), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1)]

set_option maxRecDepth 20000 in
private theorem checked2405 :
    recoveryTest 2405 conjugator2405 2 false first2405 = true ∧
    recoveryTest 2405 conjugator2405 2 true second2405 = true := by
  decide +kernel

private def conjugator2562 : Nat := 4562444141596910852745050399326146165414129847894751560783210
private def first2562 : List (Bool × Int) := [(false, -2), (true, 1), (false, -2), (true, 1), (false, -1), (true, -2)]
private def second2562 : List (Bool × Int) := [(false, 1), (true, -1), (false, -1), (true, 1), (false, -3)]

set_option maxRecDepth 20000 in
private theorem checked2562 :
    recoveryTest 2562 conjugator2562 1 false first2562 = true ∧
    recoveryTest 2562 conjugator2562 1 true second2562 = true := by
  decide +kernel

private def conjugator2662 : Nat := 1060213412765517488533255694833353630119837386321237
private def first2662 : List (Bool × Int) := [(true, -1), (false, 1), (true, -1), (false, 1), (true, 1)]
private def second2662 : List (Bool × Int) := [(true, -2), (false, 1)]

set_option maxRecDepth 20000 in
private theorem checked2662 :
    recoveryTest 2662 conjugator2662 1 false first2662 = true ∧
    recoveryTest 2662 conjugator2662 1 true second2662 = true := by
  decide +kernel

private def conjugator2701 : Nat := 8088786413311135092707575013111772778972687061
private def first2701 : List (Bool × Int) := [(true, 4), (false, 1), (true, -1), (false, -2), (true, -1), (false, 5), (true, 1), (false, 1), (true, -2), (false, -1)]
private def second2701 : List (Bool × Int) := [(true, -1), (false, 1), (true, 1), (false, -1), (true, -1), (false, -2)]

set_option maxRecDepth 20000 in
private theorem checked2701 :
    recoveryTest 2701 conjugator2701 2 false first2701 = true ∧
    recoveryTest 2701 conjugator2701 2 true second2701 = true := by
  decide +kernel

private def conjugator2733 : Nat := 7371206780386213791914715457084267
private def first2733 : List (Bool × Int) := [(true, 5), (false, 2), (true, -1), (false, -3), (true, -2)]
private def second2733 : List (Bool × Int) := [(true, 1), (false, -5), (true, -2)]

set_option maxRecDepth 20000 in
private theorem checked2733 :
    recoveryTest 2733 conjugator2733 2 false first2733 = true ∧
    recoveryTest 2733 conjugator2733 2 true second2733 = true := by
  decide +kernel

private def conjugator2935 : Nat := 67677696629176798294367188309
private def first2935 : List (Bool × Int) := [(true, 1), (false, -1), (true, -1), (false, -1), (true, 1), (false, 1), (true, 1), (false, -1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, -1), (true, -2), (false, 1)]
private def second2935 : List (Bool × Int) := [(false, 1), (true, 1), (false, -2), (true, -1), (false, -2), (true, 1), (false, 1), (true, -1), (false, -1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1)]

set_option maxRecDepth 20000 in
private theorem checked2935 :
    recoveryTest 2935 conjugator2935 1 false first2935 = true ∧
    recoveryTest 2935 conjugator2935 1 true second2935 = true := by
  decide +kernel

/-- Every entry in the unchanged exceptional list has two checked recovery words. -/
public theorem exceptional_recoveries (k : Fin 3010) (hk : k ∈ exceptionalIndices) :
    ∃ (i : Fin 3) (g : Nat) (wa wb : List (Bool × Int)),
      recoveryTest k g i false wa = true ∧ recoveryTest k g i true wb = true := by
  simp only [exceptionalIndices, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, conjugator1, first1, second1, checked1⟩
  · exact ⟨0, conjugator2, first2, second2, checked2⟩
  · exact ⟨0, conjugator3, first3, second3, checked3⟩
  · exact ⟨0, conjugator4, first4, second4, checked4⟩
  · exact ⟨0, conjugator5, first5, second5, checked5⟩
  · exact ⟨2, conjugator18, first18, second18, checked18⟩
  · exact ⟨2, conjugator56, first56, second56, checked56⟩
  · exact ⟨2, conjugator239, first239, second239, checked239⟩
  · exact ⟨2, conjugator520, first520, second520, checked520⟩
  · exact ⟨1, conjugator715, first715, second715, checked715⟩
  · exact ⟨2, conjugator726, first726, second726, checked726⟩
  · exact ⟨2, conjugator937, first937, second937, checked937⟩
  · exact ⟨2, conjugator1003, first1003, second1003, checked1003⟩
  · exact ⟨2, conjugator1022, first1022, second1022, checked1022⟩
  · exact ⟨2, conjugator1441, first1441, second1441, checked1441⟩
  · exact ⟨2, conjugator1449, first1449, second1449, checked1449⟩
  · exact ⟨2, conjugator1633, first1633, second1633, checked1633⟩
  · exact ⟨1, conjugator1877, first1877, second1877, checked1877⟩
  · exact ⟨2, conjugator1879, first1879, second1879, checked1879⟩
  · exact ⟨2, conjugator1997, first1997, second1997, checked1997⟩
  · exact ⟨2, conjugator2218, first2218, second2218, checked2218⟩
  · exact ⟨2, conjugator2405, first2405, second2405, checked2405⟩
  · exact ⟨1, conjugator2562, first2562, second2562, checked2562⟩
  · exact ⟨1, conjugator2662, first2662, second2662, checked2662⟩
  · exact ⟨2, conjugator2701, first2701, second2701, checked2701⟩
  · exact ⟨2, conjugator2733, first2733, second2733, checked2733⟩
  · exact ⟨1, conjugator2935, first2935, second2935, checked2935⟩

end Tits.MinimumIndexThirteen.PairGeneration.ExceptionalGeneration
