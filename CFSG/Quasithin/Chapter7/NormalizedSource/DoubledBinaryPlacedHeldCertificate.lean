module
public import Theory.SpecificGroups.Held.AutomorphismLocalPair.SeedIdentification

/-!
# The Held rank-six involution certificate

Every involution outside the two established rank-six subgroups of the literal
Held Sylow representative is conjugate to one of seven specified words. Each
of those words has fewer than 64 commuting involutions. The lists and conjugating
words are untrusted data; all equations are checked against the existing faithful
four-point permutation action. No subgroup normality or Sylow-placement premise
is supplied by this certificate.

DoubledBinaryPlacedHeld uses these checks to locate every elementary subgroup of
order 64 and exclude the binary-three placed component. Source: the concluding
local inspection in Aschbacher--Smith 4.4.3, printed pp.622--623, and the original
ATLAS Held words in Theory/SpecificGroups/Held/Model/Source and
LocalPairs/SylowGeometry/Calculations/Source. The reused carrier and tables retain
their attribution and license in LICENSES/ATLAS.txt.
-/

open Subgroup
open Held Held.LocalPairs.SylowGeometry.Calculations
open Held.TwoLocalCandidates.MaximalNormalizerCatalogue
open IntrinsicEnumeration ExtensionChecks
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlacedHeld
set_option maxRecDepth 4096
@[expose] public def reps : Fin 7 → Fin 1024 := ![2,6,16,34,77,162,210]
private def involutions : List (Fin 1024) := [0, 2, 3, 4, 6, 8, 12, 15, 16, 32, 34, 48, 52, 56, 60, 64, 77, 96, 99, 108, 111, 128, 129, 130, 144, 147, 148, 152, 156, 159, 160, 162, 164, 166, 168, 172, 176, 189, 194, 202, 208, 210, 225, 226, 240, 242, 243, 250, 252, 255, 256, 257, 258, 272, 275, 284, 287, 306, 320, 324, 328, 332, 349, 353, 354, 368, 370, 371, 372, 374, 376, 380, 383, 384, 386, 387, 394, 396, 399, 400, 429, 434, 442, 450, 464, 466, 468, 470, 472, 476, 480, 483, 484, 488, 492, 495, 512, 514, 515, 516, 518, 520, 524, 527, 528, 544, 546, 560, 564, 568, 572, 576, 589, 608, 611, 620, 623, 640, 641, 642, 656, 659, 660, 664, 668, 671, 672, 674, 676, 678, 680, 684, 688, 701, 706, 714, 720, 722, 737, 738, 752, 754, 755, 762, 764, 767, 768, 769, 770, 784, 787, 796, 799, 818, 832, 836, 840, 844, 861, 865, 866, 880, 882, 883, 884, 886, 888, 892, 895, 896, 898, 899, 906, 908, 911, 912, 941, 946, 954, 962, 976, 978, 980, 982, 984, 988, 992, 995, 996, 1000, 1004, 1007]
@[expose] public def centralMembers : Fin 7 → List (Fin 1024)
  | 0 => [0, 2, 4, 6, 32, 34, 128, 130, 160, 162, 164, 166, 208, 210, 240, 242, 256, 258, 368, 370, 372, 374, 384, 386, 464, 466, 468, 470, 512, 514, 516, 518, 544, 546, 640, 642, 672, 674, 676, 678, 720, 722, 752, 754, 768, 770, 880, 882, 884, 886, 896, 898, 976, 978, 980, 982]
  | 1 => [0, 2, 4, 6, 160, 162, 164, 166, 250, 252, 368, 370, 372, 374, 394, 396, 464, 466, 468, 470, 512, 514, 516, 518, 672, 674, 676, 678, 762, 764, 880, 882, 884, 886, 906, 908, 976, 978, 980, 982]
  | 2 => [0, 16, 32, 48, 128, 144, 160, 176, 194, 210, 226, 242, 256, 272, 354, 370, 384, 400, 450, 466, 512, 528, 544, 560, 640, 656, 672, 688, 706, 722, 738, 754, 768, 784, 866, 882, 896, 912, 962, 978]
  | 3 => [0, 2, 15, 32, 34, 77, 128, 130, 160, 162, 189, 208, 210, 240, 242, 255, 272, 287, 306, 320, 349, 354, 400, 429, 434, 450, 480, 495, 512, 514, 527, 544, 546, 589, 640, 642, 672, 674, 701, 720, 722, 752, 754, 767, 784, 799, 818, 832, 861, 866, 912, 941, 946, 962, 992, 1007]
  | 4 => [0, 15, 34, 60, 77, 189, 210, 225, 240, 255, 257, 272, 287, 306, 349, 429, 450, 476, 480, 495, 512, 527, 546, 572, 589, 701, 722, 737, 752, 767, 769, 784, 799, 818, 861, 941, 962, 988, 992, 1007]
  | 5 => [0, 2, 4, 6, 32, 34, 64, 96, 128, 130, 160, 162, 164, 166, 194, 226, 272, 306, 368, 370, 372, 374, 400, 434, 464, 466, 468, 470, 512, 514, 516, 518, 544, 546, 576, 608, 640, 642, 672, 674, 676, 678, 706, 738, 784, 818, 880, 882, 884, 886, 912, 946, 976, 978, 980, 982]
  | _ => [0, 2, 15, 16, 32, 34, 48, 77, 189, 194, 208, 210, 226, 240, 242, 255, 256, 258, 272, 287, 306, 349, 429, 450, 464, 466, 480, 495, 512, 514, 527, 528, 544, 546, 560, 589, 701, 706, 720, 722, 738, 752, 754, 767, 768, 770, 784, 799, 818, 861, 941, 962, 976, 978, 992, 1007]
private def lift : Fin 1024 → Fin 7 × Fin 1024
  | 2 => (0, 1014)
  | 6 => (1, 982)
  | 16 => (2, 1010)
  | 32 => (2, 954)
  | 34 => (3, 1021)
  | 64 => (2, 955)
  | 77 => (4, 1009)
  | 128 => (2, 958)
  | 129 => (4, 1015)
  | 130 => (3, 999)
  | 162 => (5, 1014)
  | 166 => (1, 1014)
  | 176 => (2, 1014)
  | 189 => (4, 1020)
  | 194 => (5, 999)
  | 202 => (1, 975)
  | 208 => (2, 1015)
  | 210 => (6, 1023)
  | 225 => (4, 999)
  | 226 => (6, 1018)
  | 242 => (0, 1007)
  | 250 => (1, 999)
  | 256 => (2, 959)
  | 257 => (4, 1014)
  | 258 => (6, 951)
  | 306 => (6, 1020)
  | 349 => (4, 1023)
  | 353 => (4, 1019)
  | 354 => (3, 1018)
  | 370 => (0, 1006)
  | 374 => (1, 1006)
  | 386 => (0, 1015)
  | 394 => (1, 991)
  | 400 => (2, 1009)
  | 429 => (4, 1021)
  | 434 => (5, 1023)
  | 442 => (1, 1015)
  | 450 => (3, 1020)
  | 466 => (5, 1022)
  | 470 => (1, 1022)
  | 514 => (0, 998)
  | 518 => (1, 998)
  | 528 => (2, 1008)
  | 544 => (2, 1018)
  | 546 => (3, 1023)
  | 576 => (2, 1019)
  | 589 => (4, 1022)
  | 640 => (2, 1022)
  | 641 => (4, 971)
  | 642 => (3, 1015)
  | 674 => (5, 998)
  | 678 => (1, 966)
  | 688 => (2, 1012)
  | 701 => (4, 994)
  | 706 => (5, 1015)
  | 714 => (1, 1023)
  | 720 => (2, 1013)
  | 722 => (6, 1021)
  | 737 => (4, 1018)
  | 738 => (6, 1019)
  | 754 => (0, 1023)
  | 762 => (1, 983)
  | 768 => (2, 1023)
  | 769 => (4, 970)
  | 770 => (6, 1015)
  | 818 => (6, 1022)
  | 861 => (4, 993)
  | 865 => (4, 998)
  | 866 => (3, 1019)
  | 882 => (0, 1022)
  | 886 => (1, 990)
  | 898 => (0, 999)
  | 906 => (1, 1007)
  | 912 => (2, 1011)
  | 941 => (4, 1010)
  | 946 => (5, 1007)
  | 954 => (1, 967)
  | 962 => (3, 1022)
  | 978 => (5, 1006)
  | 982 => (1, 974)
  | _ => (0,0)
private def coverCheck (n : Fin 1024) : Bool :=
  decide (n ∈ members (some 20) ∨ n ∈ members (some 21)) ||
  !squareAction n ||
  sameAction (normalFormAction n * normalFormAction (lift n).2)
    (normalFormAction (lift n).2 * normalFormAction (reps (lift n).1))
private def involutionCheck (n : Fin 1024) : Bool :=
  decide (n ∈ involutions) || !squareAction n
private def centralCheck (k : Fin 7) (n : Fin 1024) : Bool :=
  decide (n ∈ centralMembers k) ||
  !(sameAction (normalFormAction n * normalFormAction (reps k))
    (normalFormAction (reps k) * normalFormAction n))
private theorem cover_checks : ∀ n : Fin 1024, coverCheck n = true := by
  decide +kernel
private theorem involution_checks : ∀ n : Fin 1024, involutionCheck n = true := by
  decide +kernel
private theorem central_checks : ∀ k : Fin 7, involutions.all (centralCheck k) = true := by
  decide +kernel
private theorem small_card : ∀ k : Fin 7, (centralMembers k).toFinset.card < 64 := by
  decide +kernel
private theorem squareAction_true (n : Fin 1024) (hs : normalForm n ^ 2 = 1) :
    squareAction n = true := by
  have hh := same_eq_true.mpr (show normalForm n * normalForm n = 1 by
    simpa only [pow_two] using hs)
  simpa only [squareAction, sameAction, same, normalFormAction_eq, Subgroup.coe_mul,
    Subgroup.coe_one, map_mul, map_one] using hh

/-- Every involution outside the two rank-six rows is conjugate, inside the
literal Sylow representative, to one of seven specified small-centralizer words. -/
public theorem normalForm_cases (n : Fin 1024) (hs : normalForm n ^ 2 = 1) :
    normalForm n ∈ entry 20 ∨ normalForm n ∈ entry 21 ∨
      ∃ k : Fin 7, ∃ s : representative, normalForm n * s = s * normalForm (reps k) := by
  have hh := cover_checks n
  simp only [coverCheck, squareAction_true n hs, Bool.not_true, Bool.or_false,
    Bool.or_eq_true, decide_eq_true_eq] at hh
  rcases hh with (h | h) | h
  · exact Or.inl ((certified_members (some 20) _).mpr ⟨n,h,rfl⟩)
  · exact Or.inr (Or.inl ((certified_members (some 21) _).mpr ⟨n,h,rfl⟩))
  · refine Or.inr (Or.inr ⟨(lift n).1, normalForm (lift n).2, ?_⟩)
    apply same_eq_true.mp
    simpa only [sameAction, same, normalFormAction_eq, Subgroup.coe_mul, map_mul] using h

/-- Every involution centralizing a selected word occurs in its literal list. -/
public theorem centralizer_cover (k : Fin 7) (x : representative)
    (hs : x ^ 2 = 1) (hc : x * normalForm (reps k) = normalForm (reps k) * x) :
    ∃ n ∈ centralMembers k, normalForm n = x := by
  obtain ⟨n,rfl⟩ := normalForm_surjective x
  have hi := involution_checks n
  simp only [involutionCheck, squareAction_true n hs, Bool.not_true, Bool.or_false,
    decide_eq_true_eq] at hi
  have hh := List.all_eq_true.mp (central_checks k) n hi
  have he : sameAction (normalFormAction n * normalFormAction (reps k))
      (normalFormAction (reps k) * normalFormAction n) = true := by
    simpa only [sameAction, same, normalFormAction_eq, Subgroup.coe_mul, map_mul] using
      (same_eq_true.mpr hc)
  simp only [centralCheck, he, Bool.not_true, Bool.or_false, decide_eq_true_eq] at hh
  exact ⟨n,hh,rfl⟩

/-- Each of the seven centralizer lists has fewer than 64 entries. -/
public theorem centralMembers_card (k : Fin 7) : (centralMembers k).toFinset.card < 64 :=
  small_card k

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlacedHeld
