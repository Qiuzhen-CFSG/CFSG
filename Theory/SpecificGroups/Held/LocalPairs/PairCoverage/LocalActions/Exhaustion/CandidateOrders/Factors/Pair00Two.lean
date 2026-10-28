module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.Factors.Pair00TwoRelations
import Mathlib.Tactic.FinCases

/-!
# The order of a literal Held candidate

Collection gives the upper bound; distinct literal words give the lower bound.
The proposed data comes from the unchanged ATLAS degree-2058 carrier and
LocalActions/Candidates.lean. The Lean kernel checks every used identity.
See source/generate.py for reproduction; GAP output is not a premise.
-/

set_option maxRecDepth 16384
set_option Elab.async false

@[expose] public section
namespace Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate.Factors.Pair00Two
open Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate
open Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate.Factors

private theorem triangular_9 : triangular
    (([9] : List (Fin 10)).map (fun p => (pc p, relativeOrder p))) := by
  apply triangular_cons_words pc relativeOrder 9 [] (by decide)
    (powerWord 9) (conjugateWord 9) (power_9)
  · intro b hb
    exact False.elim (List.not_mem_nil hb)
  · decide +kernel
  · decide +kernel
  · trivial

private theorem triangular_8 : triangular
    (([8, 9] : List (Fin 10)).map (fun p => (pc p, relativeOrder p))) := by
  apply triangular_cons_words pc relativeOrder 8 [9] (by decide)
    (powerWord 8) (conjugateWord 8) (power_8)
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl
    · exact conj_8_9
  · decide +kernel
  · decide +kernel
  · exact triangular_9

private theorem triangular_7 : triangular
    (([7, 8, 9] : List (Fin 10)).map (fun p => (pc p, relativeOrder p))) := by
  apply triangular_cons_words pc relativeOrder 7 [8, 9] (by decide)
    (powerWord 7) (conjugateWord 7) (power_7)
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact conj_7_8
    · exact conj_7_9
  · decide +kernel
  · decide +kernel
  · exact triangular_8

private theorem triangular_6 : triangular
    (([6, 7, 8, 9] : List (Fin 10)).map (fun p => (pc p, relativeOrder p))) := by
  apply triangular_cons_words pc relativeOrder 6 [7, 8, 9] (by decide)
    (powerWord 6) (conjugateWord 6) (power_6)
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact conj_6_7
    · exact conj_6_8
    · exact conj_6_9
  · decide +kernel
  · decide +kernel
  · exact triangular_7

private theorem triangular_5 : triangular
    (([5, 6, 7, 8, 9] : List (Fin 10)).map (fun p => (pc p, relativeOrder p))) := by
  apply triangular_cons_words pc relativeOrder 5 [6, 7, 8, 9] (by decide)
    (powerWord 5) (conjugateWord 5) (power_5)
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact conj_5_6
    · exact conj_5_7
    · exact conj_5_8
    · exact conj_5_9
  · decide +kernel
  · decide +kernel
  · exact triangular_6

private theorem triangular_4 : triangular
    (([4, 5, 6, 7, 8, 9] : List (Fin 10)).map (fun p => (pc p, relativeOrder p))) := by
  apply triangular_cons_words pc relativeOrder 4 [5, 6, 7, 8, 9] (by decide)
    (powerWord 4) (conjugateWord 4) (power_4)
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact conj_4_5
    · exact conj_4_6
    · exact conj_4_7
    · exact conj_4_8
    · exact conj_4_9
  · decide +kernel
  · decide +kernel
  · exact triangular_5

private theorem triangular_3 : triangular
    (([3, 4, 5, 6, 7, 8, 9] : List (Fin 10)).map (fun p => (pc p, relativeOrder p))) := by
  apply triangular_cons_words pc relativeOrder 3 [4, 5, 6, 7, 8, 9] (by decide)
    (powerWord 3) (conjugateWord 3) (power_3)
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact conj_3_4
    · exact conj_3_5
    · exact conj_3_6
    · exact conj_3_7
    · exact conj_3_8
    · exact conj_3_9
  · decide +kernel
  · decide +kernel
  · exact triangular_4

private theorem triangular_2 : triangular
    (([2, 3, 4, 5, 6, 7, 8, 9] : List (Fin 10)).map (fun p => (pc p, relativeOrder p))) := by
  apply triangular_cons_words pc relativeOrder 2 [3, 4, 5, 6, 7, 8, 9] (by decide)
    (powerWord 2) (conjugateWord 2) (power_2)
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact conj_2_3
    · exact conj_2_4
    · exact conj_2_5
    · exact conj_2_6
    · exact conj_2_7
    · exact conj_2_8
    · exact conj_2_9
  · decide +kernel
  · decide +kernel
  · exact triangular_3

private theorem triangular_1 : triangular
    (([1, 2, 3, 4, 5, 6, 7, 8, 9] : List (Fin 10)).map (fun p => (pc p, relativeOrder p))) := by
  apply triangular_cons_words pc relativeOrder 1 [2, 3, 4, 5, 6, 7, 8, 9] (by decide)
    (powerWord 1) (conjugateWord 1) (power_1)
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact conj_1_2
    · exact conj_1_3
    · exact conj_1_4
    · exact conj_1_5
    · exact conj_1_6
    · exact conj_1_7
    · exact conj_1_8
    · exact conj_1_9
  · decide +kernel
  · decide +kernel
  · exact triangular_2

private theorem triangular_0 : triangular
    (([0, 1, 2, 3, 4, 5, 6, 7, 8, 9] : List (Fin 10)).map (fun p => (pc p, relativeOrder p))) := by
  apply triangular_cons_words pc relativeOrder 0 [1, 2, 3, 4, 5, 6, 7, 8, 9] (by decide)
    (powerWord 0) (conjugateWord 0) (power_0)
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact conj_0_1
    · exact conj_0_2
    · exact conj_0_3
    · exact conj_0_4
    · exact conj_0_5
    · exact conj_0_6
    · exact conj_0_7
    · exact conj_0_8
    · exact conj_0_9
  · decide +kernel
  · decide +kernel
  · exact triangular_1

theorem upper_bound : Nat.card (Subgroup.closure (Set.range input)) ≤ 1024 := by
  have hpc : Nat.card (Subgroup.closure (Set.range pc)) ≤ 1024 := by
    have h := card_le _ triangular_0
    have he : Prod.fst '' {x | x ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9] : List (Fin 10)).map
        (fun p => (pc p, relativeOrder p))} = Set.range pc := by
      ext x
      simp only [Set.mem_image, Set.mem_ofPred_eq, List.mem_map, Set.mem_range]
      constructor
      · rintro ⟨_, ⟨k, _, rfl⟩, rfl⟩
        exact ⟨k, rfl⟩
      · rintro ⟨k, rfl⟩
        refine ⟨(pc k, relativeOrder k), ⟨k, ?_, rfl⟩, rfl⟩
        fin_cases k <;> simp
    rw [he] at h
    exact h
  have hle : Subgroup.closure (Set.range input) ≤ Subgroup.closure (Set.range pc) := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨k,rfl⟩
    have hi : input k = ((inputWord k).map pc).prod := by
      fin_cases k
      · exact input_0
      · exact input_1
      · exact input_2
      · exact input_3
    rw [hi]
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp hx
    exact Subgroup.subset_closure (Set.mem_range_self t)
  exact (Subgroup.card_le_of_le hle).trans hpc

def radix : Fin 10 → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 8
  | 4 => 16
  | 5 => 32
  | 6 => 64
  | 7 => 128
  | 8 => 256
  | 9 => 512

def normalForm (v : Fin 1024) : He :=
  (List.ofFn (fun k : Fin 10 => pc k ^ (v.val / radix k % relativeOrder k))).prod

def normalTable (v : Fin 1024) : Equiv.Perm (Fin 2058) :=
  (List.ofFn (fun k : Fin 10 => pcTable k ^ (v.val / radix k % relativeOrder k))).prod

theorem normalTable_eq (v : Fin 1024) : normalTable v = representation (normalForm v) := by
  simp only [normalForm, normalTable, map_list_prod, List.map_ofFn, Function.comp_def, map_pow, ← pcTable_eq]

def decodeCode (x : ℕ) : ℕ :=
  (if x < 4160792496 then (if x < 1627181034 then (if x < 712031802 then (if x < 292775320 then (if x < 221019113 then (if x < 77037335 then (if x < 38654051 then (if x < 2853139 then (if x < 1858376 then (if x < 2934 then 0 else 256) else (if x < 1859250 then 512 else 768)) else (if x < 3935647 then (if x < 2853820 then 32 else 288) else (if x < 3936328 then 544 else 800))) else (if x < 40239076 then (if x < 39868636 then (if x < 38654378 then 653 else 909) else (if x < 39868796 then 621 else 877)) else (if x < 41720471 then (if x < 40239236 then 109 else 365) else (if x < 41720798 then 141 else 397)))) else (if x < 209037806 then (if x < 80171834 then (if x < 79089326 then (if x < 77037429 then 369 else 113) else (if x < 79089809 then 145 else 401)) else (if x < 80445383 then (if x < 80172317 then 657 else 913) else (if x < 80445477 then 881 else 625))) else (if x < 209565446 then (if x < 209309462 then (if x < 209038393 then 456 else 200) else (if x < 209310049 then 968 else 712)) else (if x < 209917364 then (if x < 209565466 then 1000 else 744) else (if x < 209917384 then 488 else 232))))) else (if x < 267608916 then (if x < 232947299 then (if x < 222271446 then (if x < 221292827 then (if x < 221020796 then 778 else 522) else (if x < 221294510 then 266 else 10)) else (if x < 222623364 then (if x < 222272204 then 42 else 298) else (if x < 222624122 then 554 else 810))) else (if x < 233999031 then (if x < 233725317 then (if x < 232947464 then 385 else 129) else (if x < 233725871 then 97 else 353)) else (if x < 234803615 then (if x < 233999585 then 609 else 865) else (if x < 234803780 then 897 else 641)))) else (if x < 281039457 then (if x < 268860442 then (if x < 267882630 then (if x < 267609327 then 650 else 906) else (if x < 267883041 then 138 else 394)) else (if x < 269212360 then (if x < 268860674 then 362 else 106) else (if x < 269212592 then 874 else 618))) else (if x < 281566780 then (if x < 281311113 then (if x < 281040231 then 136 else 392) else (if x < 281311887 then 648 else 904)) else (if x < 281918698 then (if x < 281566967 then 872 else 616) else (if x < 281918885 then 360 else 104)))))) else (if x < 513259622 then (if x < 432098741 then (if x < 330894532 then (if x < 294486476 then (if x < 294124268 then (if x < 292775901 then 574 else 830) else (if x < 294124973 then 542 else 798)) else (if x < 295841740 then (if x < 294487181 then 30 else 286) else (if x < 295842321 then 62 else 318))) else (if x < 332478827 then (if x < 332108387 then (if x < 330894692 then 589 else 845) else (if x < 332108714 then 685 else 941)) else (if x < 333960952 then (if x < 332479154 then 173 else 429) else (if x < 333961112 then 77 else 333)))) else (if x < 488234797 then (if x < 434086769 then (if x < 433890835 then (if x < 432099502 then 828 else 572) else (if x < 433891226 then 540 else 796)) else (if x < 434253043 then (if x < 434087530 then 316 else 60) else (if x < 434253434 then 28 else 284))) else (if x < 490840225 then (if x < 489310602 then (if x < 488235737 then 372 else 116) else (if x < 489311586 then 404 else 148)) else (if x < 491026974 then (if x < 490841165 then 884 else 628) else (if x < 491027958 then 916 else 660))))) else (if x < 648547157 then (if x < 530926262 then (if x < 513533336 then (if x < 513280160 then (if x < 513260965 then 336 else 80) else (if x < 513281557 then 432 else 176)) else (if x < 516688208 then (if x < 513534679 then 848 else 592) else (if x < 516689605 then 944 else 688))) else (if x < 531452318 then (if x < 531197918 then (if x < 530926282 then 264 else 8) else (if x < 531197938 then 776 else 520)) else (if x < 531804236 then (if x < 531452905 then 808 else 552) else (if x < 531804823 then 296 else 40)))) else (if x < 704736167 then (if x < 651361477 then (if x < 649706845 then (if x < 648547208 then 228 else 484) else (if x < 649706997 then 708 else 964)) else (if x < 651613577 then (if x < 651361629 then 196 else 452) else (if x < 651613628 then 740 else 996))) else (if x < 706421047 then (if x < 704766415 then (if x < 704736386 then 357 else 101) else (if x < 704766545 then 389 else 133)) else (if x < 706466945 then (if x < 706421177 then 901 else 645) else (if x < 706467164 then 869 else 613))))))) else (if x < 1380819853 then (if x < 1073212213 then (if x < 927547328 then (if x < 755560742 then (if x < 713318104 then (if x < 713046448 then (if x < 712032888 then 857 else 601) else (if x < 713047217 then 441 else 185)) else (if x < 715427502 then (if x < 713318873 then 953 else 697) else (if x < 715428588 then 345 else 89))) else (if x < 756015169 then (if x < 755644729 then (if x < 755561536 then 972 else 716) else (if x < 755645153 then 236 else 492)) else (if x < 757291520 then (if x < 756015593 then 748 else 1004) else (if x < 757292314 then 460 else 204)))) else (if x < 944577765 then (if x < 930397700 then (if x < 929403644 then (if x < 927548713 then 320 else 64) else (if x < 929405029 then 832 else 576)) else (if x < 931480208 then (if x < 930399055 then 416 else 160) else (if x < 931481563 then 928 else 672))) else (if x < 946565793 then (if x < 946183133 then (if x < 944578525 then 166 else 422) else (if x < 946183745 then 838 else 582)) else (if x < 947837765 then (if x < 946566553 then 678 else 934) else (if x < 947838377 then 326 else 70))))) else (if x < 1169051512 then (if x < 1153684362 then (if x < 1074898337 then (if x < 1073243705 then (if x < 1073212343 then 421 else 165) else (if x < 1073243924 then 325 else 69)) else (if x < 1074942991 then (if x < 1074898556 then 837 else 581) else (if x < 1074943121 then 933 else 677))) else (if x < 1154140595 then (if x < 1153770155 then (if x < 1153685302 then 588 else 844) else (if x < 1153770182 then 172 else 428)) else (if x < 1155415140 then (if x < 1154140622 then 684 else 940) else (if x < 1155416080 then 76 else 332)))) else (if x < 1330439923 then (if x < 1171039540 then (if x < 1170657672 then (if x < 1169052374 then 294 else 38) else (if x < 1170657979 then 518 else 774)) else (if x < 1172312304 then (if x < 1171040402 then 806 else 550) else (if x < 1172312611 then 6 else 262))) else (if x < 1333506343 then (if x < 1331072178 then (if x < 1330440079 then 471 else 215) else (if x < 1331072990 then 1015 else 759)) else (if x < 1333677606 then (if x < 1333506499 then 983 else 727) else (if x < 1333678418 then 503 else 247)))))) else (if x < 1505586072 then (if x < 1423883252 then (if x < 1415102382 then (if x < 1382807881 then (if x < 1382612795 then (if x < 1380820244 then 764 else 1020) else (if x < 1382613556 then 988 else 732)) else (if x < 1382975003 then (if x < 1382808272 then 252 else 508) else (if x < 1382975764 then 476 else 220))) else (if x < 1418498082 then (if x < 1417465377 then (if x < 1415102644 then 154 else 410) else (if x < 1417465460 then 890 else 634)) else (if x < 1418547885 then (if x < 1418498344 then 666 else 922) else (if x < 1418547968 then 378 else 122)))) else (if x < 1475572357 then (if x < 1427017421 then (if x < 1425934913 then (if x < 1423883735 then 177 else 433) else (if x < 1425935007 then 337 else 81)) else (if x < 1427291300 then (if x < 1427017515 then 849 else 593) else (if x < 1427291783 then 689 else 945))) else (if x < 1476152694 then (if x < 1475790486 then (if x < 1475573637 then 703 else 959) else (if x < 1475790765 then 607 else 863)) else (if x < 1477303135 then (if x < 1476152973 then 95 else 351) else (if x < 1477304415 then 191 else 447))))) else (if x < 1584028945 then (if x < 1572120871 then (if x < 1506407640 then (if x < 1505937990 then (if x < 1505586555 then 555 else 811) else (if x < 1505938473 then 43 else 299)) else (if x < 1507490148 then (if x < 1506408168 then 523 else 779) else (if x < 1507490676 then 11 else 267))) else (if x < 1573096800 then (if x < 1572825144 then (if x < 1572121150 then 818 else 562) else (if x < 1572826135 then 530 else 786)) else (if x < 1575528919 then (if x < 1573097791 then 18 else 274) else (if x < 1575529198 then 306 else 50)))) else (if x < 1589928269 then (if x < 1586878526 then (if x < 1585885261 then (if x < 1584029626 then 192 else 448) else (if x < 1585885942 then 704 else 960)) else (if x < 1587961034 then (if x < 1586879400 then 224 else 480) else (if x < 1587961908 then 736 else 992))) else (if x < 1590381672 then (if x < 1590011232 then (if x < 1589928296 then 652 else 908) else (if x < 1590012172 then 108 else 364)) else (if x < 1591659047 then (if x < 1590382612 then 620 else 876) else (if x < 1591659074 then 140 else 396)))))))) else (if x < 3106218151 then (if x < 2237072976 then (if x < 1881282349 then (if x < 1729694071 then (if x < 1632498905 then (if x < 1629765222 then (if x < 1629018168 then (if x < 1627181303 then 755 else 1011) else (if x < 1629018830 then 979 else 723)) else (if x < 1630589082 then (if x < 1629765884 then 467 else 211) else (if x < 1630589351 then 243 else 499))) else (if x < 1632861113 then (if x < 1632859382 then (if x < 1632499430 then 669 else 925) else (if x < 1632859420 then 893 else 637)) else (if x < 1634575754 then (if x < 1632861638 then 157 else 413) else (if x < 1634575792 then 381 else 125)))) else (if x < 1766638289 then (if x < 1730149280 then (if x < 1729778840 then (if x < 1729694495 then 524 else 780) else (if x < 1729779634 then 300 else 44)) else (if x < 1731424849 then (if x < 1730150074 then 812 else 556) else (if x < 1731425273 then 12 else 268))) else (if x < 1769533233 then (if x < 1768786179 then (if x < 1766638401 then 88 else 344) else (if x < 1768786654 then 184 else 440)) else (if x < 1770033989 then (if x < 1769533708 then 696 else 952) else (if x < 1770034101 then 600 else 856))))) else (if x < 1924551681 then (if x < 1906695046 then (if x < 1881556063 then (if x < 1881302180 then (if x < 1881282474 then 208 else 464) else (if x < 1881303610 then 240 else 496)) else (if x < 1884710228 then (if x < 1881556188 then 720 else 976) else (if x < 1884711658 then 752 else 1008))) else (if x < 1907946048 then (if x < 1906968760 then (if x < 1906695278 then 842 else 586) else (if x < 1906968992 then 330 else 74)) else (if x < 1908297966 then (if x < 1907946459 then 170 else 426) else (if x < 1908298377 then 682 else 938)))) else (if x < 2117773315 then (if x < 1926206313 then (if x < 1925099280 then (if x < 1924552411 then 327 else 71) else (if x < 1925099821 then 423 else 167)) else (if x < 1926815652 then (if x < 1926207043 then 839 else 583) else (if x < 1926816193 then 935 else 679))) else (if x < 2119761343 then (if x < 2119432044 then (if x < 2117773575 then 655 else 911) else (if x < 2119433343 then 111 else 367)) else (if x < 2119802484 then (if x < 2119761603 then 143 else 399) else (if x < 2119803783 then 623 else 879)))))) else (if x < 2588342845 then (if x < 2427399703 then (if x < 2257939422 then (if x < 2238048515 then (if x < 2237776859 then (if x < 2237074283 then 946 else 690) else (if x < 2237778082 then 594 else 850)) else (if x < 2240481024 then (if x < 2238049738 then 82 else 338) else (if x < 2240482331 then 434 else 178))) else (if x < 2258503740 then (if x < 2258230026 then (if x < 2257940376 then 731 else 987) else (if x < 2258230083 then 763 else 1019)) else (if x < 2261335122 then (if x < 2258503797 then 251 else 507) else (if x < 2261336076 then 219 else 475)))) else (if x < 2462778762 then (if x < 2430214518 then (if x < 2428559886 then (if x < 2427400158 then 420 else 164) else (if x < 2428561355 then 836 else 580)) else (if x < 2430466123 then (if x < 2430215987 then 324 else 68) else (if x < 2430466578 then 932 else 676))) else (if x < 2463599478 then (if x < 2463130680 then (if x < 2462779290 then 747 else 1003) else (if x < 2463131208 then 235 else 491)) else (if x < 2464681986 then (if x < 2463599961 then 715 else 971) else (if x < 2464682469 then 203 else 459))))) else (if x < 2622226200 then (if x < 2613223138 then (if x < 2591159213 then (if x < 2589504581 then (if x < 2588342997 then 36 else 292) else (if x < 2589504632 then 516 else 772)) else (if x < 2591409265 then (if x < 2591159264 then 4 else 260) else (if x < 2591409417 then 548 else 804))) else (if x < 2615858166 then (if x < 2615079454 then (if x < 2613223175 then 386 else 130) else (if x < 2615079491 then 898 else 642)) else (if x < 2616605220 then (if x < 2615858213 then 866 else 610) else (if x < 2616605267 then 354 else 98)))) else (if x < 3100777665 then (if x < 2625292620 then (if x < 2622857835 then (if x < 2622226759 then 343 else 87) else (if x < 2622858547 then 951 else 695)) else (if x < 2625463263 then (if x < 2625293179 then 855 else 599) else (if x < 2625463975 then 439 else 183))) else (if x < 3104173365 then (if x < 3103139838 then (if x < 3100777748 then 346 else 90) else (if x < 3103140100 then 698 else 954)) else (if x < 3104222346 then (if x < 3104173448 then 858 else 602) else (if x < 3104222608 then 186 else 442))))))) else (if x < 3775741416 then (if x < 3511607458 then (if x < 3431446104 then (if x < 3241719858 then (if x < 3107872783 then (if x < 3106765735 then (if x < 3106219412 then 263 else 7) else (if x < 3106766028 then 39 else 295)) else (if x < 3108482107 then (if x < 3107874044 then 775 else 519) else (if x < 3108482400 then 551 else 807))) else (if x < 3243403982 then (if x < 3241749350 then (if x < 3241719900 then 485 else 229) else (if x < 3241749518 then 197 else 453)) else (if x < 3243450636 then (if x < 3243404150 then 709 else 965) else (if x < 3243450678 then 997 else 741)))) else (if x < 3464619676 then (if x < 3432421159 then (if x < 3432149503 then (if x < 3431447095 then 754 else 1010) else (if x < 3432149782 then 978 else 722)) else (if x < 3434854152 then (if x < 3432421438 then 466 else 210) else (if x < 3434855143 then 242 else 498))) else (if x < 3466607704 then (if x < 3466411254 then (if x < 3464620151 then 956 else 700) else (if x < 3466412696 then 604 else 860)) else (if x < 3466773462 then (if x < 3466608179 then 444 else 188) else (if x < 3466774904 then 92 else 348))))) else (if x < 3596360198 then (if x < 3591680393 then (if x < 3512893656 then (if x < 3512622000 then (if x < 3511608227 then 921 else 665) else (if x < 3512623086 then 377 else 121)) else (if x < 3515003158 then (if x < 3512894742 then 889 else 633) else (if x < 3515003927 then 409 else 153))) else (if x < 3593668421 then (if x < 3593285505 then (if x < 3591681005 then 358 else 102) else (if x < 3593286265 then 646 else 902)) else (if x < 3594940137 then (if x < 3593669033 then 870 else 614) else (if x < 3594940897 then 134 else 390)))) else (if x < 3706434339 then (if x < 3598069438 then (if x < 3597707230 then (if x < 3596360903 then 766 else 1022) else (if x < 3597707811 then 734 else 990)) else (if x < 3599426618 then (if x < 3598070019 then 222 else 478) else (if x < 3599427323 then 254 else 510))) else (if x < 3709330607 then (if x < 3708583553 then (if x < 3706434814 then 152 else 408) else (if x < 3708583665 then 120 else 376)) else (if x < 3709830039 then (if x < 3709330719 then 632 else 888) else (if x < 3709830514 then 664 else 920)))))) else (if x < 4002955525 then (if x < 3918201853 then (if x < 3894331074 then (if x < 3776348578 then (if x < 3776093334 then (if x < 3775742237 then 425 else 169) else (if x < 3776094155 then 937 else 681)) else (if x < 3777095632 then (if x < 3776349612 then 329 else 73) else (if x < 3777096666 then 841 else 585))) else (if x < 3895153642 then (if x < 3894682992 then (if x < 3894331111 then 683 else 939) else (if x < 3894683029 then 171 else 427)) else (if x < 3896236150 then (if x < 3895153853 then 843 else 587) else (if x < 3896236361 then 331 else 75)))) else (if x < 3985968360 then (if x < 3918765708 then (if x < 3918491994 then (if x < 3918203453 then 859 else 603) else (if x < 3918493420 then 699 else 955)) else (if x < 3921597553 then (if x < 3918767134 then 187 else 443) else (if x < 3921599153 then 347 else 91))) else (if x < 3986531826 then (if x < 3986258112 then (if x < 3985968417 then 539 else 795) else (if x < 3986259066 then 571 else 827)) else (if x < 3989364060 then (if x < 3986532780 then 59 else 315) else (if x < 3989364117 then 27 else 283))))) else (if x < 4017008694 then (if x < 4011380738 then (if x < 4004664443 then (if x < 4004302235 then (if x < 4002955655 then 958 else 702) else (if x < 4004304029 then 862 else 606)) else (if x < 4006021945 then (if x < 4004666237 then 350 else 94) else (if x < 4006022075 then 446 else 190))) else (if x < 4012666308 then (if x < 4012394652 then (if x < 4011381139 then 985 else 729) else (if x < 4012395738 then 505 else 249)) else (if x < 4014776438 then (if x < 4012667394 then 1017 else 761) else (if x < 4014776839 then 473 else 217)))) else (if x < 4101497372 then (if x < 4017370902 then (if x < 4017368590 then (if x < 4017010131 then 797 else 541) else (if x < 4017368708 then 573 else 829)) else (if x < 4019084962 then (if x < 4017372339 then 285 else 29) else (if x < 4019085080 then 61 else 317))) else (if x < 4103184252 then (if x < 4101529620 then (if x < 4101497540 then 37 else 293) else (if x < 4101529662 then 261 else 5)) else (if x < 4103228150 then (if x < 4103184294 then 773 else 517) else (if x < 4103228318 then 549 else 805))))))))) else (if x < 6494562497 then (if x < 5218059266 then (if x < 4813257596 then (if x < 4563518820 then (if x < 4464564032 then (if x < 4421722361 then (if x < 4161373271 then (if x < 4161011063 then (if x < 4160793298 then 1023 else 767) else (if x < 4161012386 then 991 else 735)) else (if x < 4162523274 then (if x < 4161374594 then 479 else 223) else (if x < 4162524076 then 511 else 255))) else (if x < 4423496527 then (if x < 4423224871 then (if x < 4421723440 then 387 else 131) else (if x < 4423226416 then 611 else 867)) else (if x < 4423578677 then (if x < 4423498072 then 99 else 355) else (if x < 4423579756 then 899 else 643)))) else (if x < 4481505462 then (if x < 4467460225 then (if x < 4466713171 then (if x < 4464564844 then 280 else 24) else (if x < 4466713376 then 56 else 312)) else (if x < 4467959732 then (if x < 4467460430 then 568 else 824) else (if x < 4467960544 then 792 else 536))) else (if x < 4482792392 then (if x < 4482520736 then (if x < 4481506548 then 793 else 537) else (if x < 4482521137 then 313 else 57)) else (if x < 4484901162 then (if x < 4482792793 then 825 else 569) else (if x < 4484902248 then 281 else 25))))) else (if x < 4709726862 then (if x < 4629255454 then (if x < 4564126610 then (if x < 4563870738 then (if x < 4563519901 then 297 else 41) else (if x < 4563871819 then 809 else 553)) else (if x < 4564873664 then (if x < 4564127016 then 265 else 9) else (if x < 4564874070 then 777 else 521))) else (if x < 4631891473 then (if x < 4631111770 then (if x < 4629256603 then 194 else 450) else (if x < 4631112919 then 706 else 962)) else (if x < 4632638527 then (if x < 4631891910 then 994 else 738) else (if x < 4632638964 then 482 else 226)))) else (if x < 4718730874 then (if x < 4711501520 then (if x < 4711229864 then (if x < 4709727522 then 259 else 3) else (if x < 4711230131 then 547 else 803)) else (if x < 4711583178 then (if x < 4711501787 then 35 else 291) else (if x < 4711583838 then 771 else 515))) else (if x < 4720315652 then (if x < 4719945212 then (if x < 4718731128 then 717 else 973) else (if x < 4719946785 then 1005 else 749)) else (if x < 4721797294 then (if x < 4720317225 then 493 else 237) else (if x < 4721797548 then 205 else 461)))))) else (if x < 4931130943 then (if x < 4900806264 then (if x < 4871159563 then (if x < 4813619804 then (if x < 4813617419 then (if x < 4813257634 then 861 else 605) else (if x < 4813617944 then 701 else 957)) else (if x < 4815333791 then (if x < 4813619842 then 349 else 93) else (if x < 4815334316 then 189 else 445))) else (if x < 4874054582 then (if x < 4873307528 then (if x < 4871159768 then 216 else 472) else (if x < 4873308340 then 504 else 248)) else (if x < 4874555263 then (if x < 4874055394 then 1016 else 760) else (if x < 4874555468 then 728 else 984)))) else (if x < 4923158634 then (if x < 4901370193 then (if x < 4901096479 then (if x < 4900807690 then 667 else 923) else (if x < 4901098079 then 891 else 635)) else (if x < 4904201964 then (if x < 4901371793 then 379 else 123) else (if x < 4904203390 then 155 else 411))) else (if x < 4923739009 then (if x < 4923376801 then (if x < 4923158913 then 639 else 895) else (if x < 4923378081 then 671 else 927)) else (if x < 4924889412 then (if x < 4923740289 then 159 else 415) else (if x < 4924889691 then 127 else 383))))) else (if x < 5035849911 then (if x < 4974066760 then (if x < 4933736371 then (if x < 4932207429 then (if x < 4931132018 then 52 else 308) else (if x < 4932208301 then 276 else 20)) else (if x < 4933923801 then (if x < 4933737446 then 564 else 820) else (if x < 4933924673 then 788 else 532))) else (if x < 4974561261 then (if x < 4974437200 then (if x < 4974068423 then 558 else 814) else (if x < 4974438863 then 46 else 302)) else (if x < 4976277633 then (if x < 4974561638 then 782 else 526) else (if x < 4976278010 then 270 else 14)))) else (if x < 5069821692 then (if x < 5036901671 then (if x < 5036627957 then (if x < 5035851329 then 193 else 449) else (if x < 5036629354 then 481 else 225)) else (if x < 5037706227 then (if x < 5036903068 then 993 else 737) else (if x < 5037707645 then 705 else 961))) else (if x < 5071809720 then (if x < 5071615150 then (if x < 5069823134 then 636 else 892) else (if x < 5071615625 then 924 else 668)) else (if x < 5071977358 then (if x < 5071811162 then 124 else 380) else (if x < 5071977833 then 412 else 156))))))) else (if x < 6009983753 then (if x < 5629966138 then (if x < 5370977154 then (if x < 5285824922 then (if x < 5220047294 then (if x < 5219135432 then (if x < 5218060518 then 277 else 21) else (if x < 5219136810 then 53 else 309)) else (if x < 5221740860 then (if x < 5220048546 then 789 else 533) else (if x < 5221742238 then 565 else 821))) else (if x < 5287812950 then (if x < 5286901424 then (if x < 5285826300 then 213 else 469) else (if x < 5286902676 then 501 else 245)) else (if x < 5289506852 then (if x < 5287814328 then 725 else 981) else (if x < 5289508104 then 1013 else 757)))) else (if x < 5599242504 then (if x < 5373793027 then (if x < 5372138395 then (if x < 5370978623 then 356 else 100) else (if x < 5372138850 then 900 else 644)) else (if x < 5374043574 then (if x < 5373793482 then 388 else 132) else (if x < 5374045043 then 868 else 612))) else (if x < 5601230532 then (if x < 5600901271 then (if x < 5599243803 then 591 else 847) else (if x < 5600901531 then 175 else 431)) else (if x < 5601271711 then (if x < 5601231831 then 79 else 335) else (if x < 5601271971 then 687 else 943))))) else (if x < 5880350699 then (if x < 5791775060 then (if x < 5632195814 then (if x < 5630465036 then (if x < 5629967058 then 1014 else 758) else (if x < 5630465401 then 214 else 470)) else (if x < 5632571566 then (if x < 5632196179 then 726 else 982) else (if x < 5632572486 then 502 else 246))) else (if x < 5792381490 then (if x < 5792126978 then (if x < 5791775466 then 489 else 233) else (if x < 5792127384 then 1001 else 745)) else (if x < 5793128544 then (if x < 5792382571 then 457 else 201) else (if x < 5793129625 then 969 else 713)))) else (if x < 5908335434 then (if x < 5880930636 then (if x < 5880568428 then (if x < 5880352022 then 831 else 575) else (if x < 5880569230 then 799 else 543)) else (if x < 5882081477 then (if x < 5880931438 then 287 else 31) else (if x < 5882082800 then 319 else 63))) else (if x < 5911185722 then (if x < 5910191750 then (if x < 5908336789 then 384 else 128) else (if x < 5910193105 then 896 else 640)) else (if x < 5912268230 then (if x < 5911187107 then 352 else 96) else (if x < 5912269615 then 864 else 608)))))) else (if x < 6354742596 then (if x < 6164487604 then (if x < 6141280173 then (if x < 6011035269 then (if x < 6010761555 then (if x < 6009985150 then 257 else 1) else (if x < 6010762973 then 33 else 289)) else (if x < 6011840069 then (if x < 6011036687 then 545 else 801) else (if x < 6011841466 then 769 else 513))) else (if x < 6142331717 then (if x < 6142058003 then (if x < 6141280727 then 65 else 321) else (if x < 6142058168 then 417 else 161)) else (if x < 6143136489 then (if x < 6142331882 then 929 else 673) else (if x < 6143137043 then 577 else 833)))) else (if x < 6264638621 then (if x < 6165307320 then (if x < 6164839522 then (if x < 6164487815 then 875 else 619) else (if x < 6164839733 then 363 else 107)) else (if x < 6166389828 then (if x < 6165307357 then 651 else 907) else (if x < 6166389865 then 139 else 395))) else (if x < 6266350099 then (if x < 6265987891 then (if x < 6264640415 then 894 else 638) else (if x < 6265988021 then 926 else 670)) else (if x < 6267705041 then (if x < 6266350229 then 414 else 158) else (if x < 6267706835 then 382 else 126))))) else (if x < 6413847004 then (if x < 6401518372 then (if x < 6356397228 then (if x < 6355289853 then (if x < 6354743137 then 391 else 135) else (if x < 6355290583 then 359 else 103)) else (if x < 6357006225 then (if x < 6356397769 then 903 else 647) else (if x < 6357006955 then 871 else 615))) else (if x < 6401880580 then (if x < 6401878776 then (if x < 6401518490 then 733 else 989) else (if x < 6401880213 then 1021 else 765)) else (if x < 6403595148 then (if x < 6401880698 then 221 else 477) else (if x < 6403596585 then 509 else 253)))) else (if x < 6451240626 then (if x < 6414373377 then (if x < 6414118660 then (if x < 6413847191 then 328 else 72) else (if x < 6414118847 then 840 else 584)) else (if x < 6414725295 then (if x < 6414374151 then 680 else 936) else (if x < 6414726069 then 168 else 424))) else (if x < 6452490821 then (if x < 6451514340 then (if x < 6451241384 then 714 else 970) else (if x < 6451515098 then 202 else 458)) else (if x < 6452842739 then (if x < 6452492504 then 490 else 234) else (if x < 6452844422 then 1002 else 746)))))))) else (if x < 7510996867 then (if x < 7005294336 then (if x < 6901157961 then (if x < 6815868084 then (if x < 6619965900 then (if x < 6495057697 then (if x < 6494932937 then (if x < 6494563907 then 942 else 686) else (if x < 6494934347 then 430 else 174)) else (if x < 6496774069 then (if x < 6495058211 then 846 else 590) else (if x < 6496774583 then 334 else 78))) else (if x < 6621953928 then (if x < 6621570220 then (if x < 6619966207 then 230 else 486) else (if x < 6621571082 then 966 else 710)) else (if x < 6623224852 then (if x < 6621954235 then 742 else 998) else (if x < 6623225714 then 454 else 198)))) else (if x < 6859086460 then (if x < 6818473512 then (if x < 6816944947 then (if x < 6815869068 then 436 else 180) else (if x < 6816945887 then 340 else 84)) else (if x < 6818661319 then (if x < 6818474496 then 948 else 692) else (if x < 6818662259 then 852 else 596))) else (if x < 6859693518 then (if x < 6859438378 then (if x < 6859087494 then 361 else 105) else (if x < 6859439412 then 873 else 617)) else (if x < 6860440572 then (if x < 6859694339 then 393 else 137) else (if x < 6860441393 then 905 else 649))))) else (if x < 6946797579 then (if x < 6907881440 then (if x < 6901651300 then (if x < 6901528401 then (if x < 6901158338 then 1006 else 750) else (if x < 6901528778 then 494 else 238)) else (if x < 6903367672 then (if x < 6901652963 then 718 else 974) else (if x < 6903369335 then 206 else 462))) else (if x < 6909654774 then (if x < 6909383118 then (if x < 6907881707 then 195 else 451) else (if x < 6909383778 then 995 else 739)) else (if x < 6909737756 then (if x < 6909655434 then 483 else 227) else (if x < 6909738023 then 707 else 963)))) else (if x < 6976136198 then (if x < 6949933331 then (if x < 6948850823 then (if x < 6946797701 then 49 else 305) else (if x < 6948850924 then 273 else 17)) else (if x < 6950205627 then (if x < 6949933432 then 785 else 529) else (if x < 6950205749 then 561 else 817))) else (if x < 6979531898 then (if x < 6978497099 then (if x < 6976136342 then 26 else 282) else (if x < 6978498168 then 826 else 570)) else (if x < 6979579607 then (if x < 6979532042 then 538 else 794) else (if x < 6979580676 then 314 else 58)))))) else (if x < 7327981757 then (if x < 7064678249 then (if x < 7013853462 then (if x < 7007931904 then (if x < 7007150652 then (if x < 7005294383 then 322 else 66) else (if x < 7007150699 then 834 else 578)) else (if x < 7008678958 then (if x < 7007931941 then 930 else 674) else (if x < 7008678995 then 418 else 162))) else (if x < 7015841490 then (if x < 7015512629 then (if x < 7013855204 then 975 else 719) else (if x < 7015513012 then 495 else 239)) else (if x < 7015883069 then (if x < 7015843232 then 463 else 207) else (if x < 7015883452 then 1007 else 751)))) else (if x < 7263651583 then (if x < 7066666277 then (if x < 7066336578 then (if x < 7064678632 then 783 else 527) else (if x < 7066338320 then 303 else 47)) else (if x < 7066707018 then (if x < 7066666660 then 271 else 15) else (if x < 7066708760 then 815 else 559))) else (if x < 7266288160 then (if x < 7265507899 then (if x < 7263652020 then 258 else 2) else (if x < 7265508336 then 770 else 514)) else (if x < 7267035214 then (if x < 7266289309 then 546 else 802) else (if x < 7267036363 then 34 else 290))))) else (if x < 7439049949 then (if x < 7408187349 then (if x < 7331114673 then (if x < 7330032165 then (if x < 7327981858 then 497 else 241) else (if x < 7330032287 then 209 else 465)) else (if x < 7331389805 then (if x < 7331114795 then 721 else 977) else (if x < 7331389906 then 1009 else 753))) else (if x < 7411253769 then (if x < 7408819326 then (if x < 7408188061 then 407 else 151) else (if x < 7408819885 then 887 else 631)) else (if x < 7411424754 then (if x < 7411254481 then 919 else 663) else (if x < 7411425313 then 375 else 119)))) else (if x < 7446570743 then (if x < 7439542589 then (if x < 7439420389 then (if x < 7439050463 then 878 else 622) else (if x < 7439420903 then 366 else 110)) else (if x < 7441258961 then (if x < 7439543999 then 910 else 654) else (if x < 7441260371 then 398 else 142))) else (if x < 7447546188 then (if x < 7447274532 then (if x < 7446571966 then 626 else 882) else (if x < 7447275839 then 914 else 658)) else (if x < 7449978791 then (if x < 7447547495 then 402 else 146) else (if x < 7449980014 then 114 else 370))))))) else (if x < 7899755788 then (if x < 7646000264 then (if x < 7606716259 then (if x < 7557056775 then (if x < 7512651499 then (if x < 7511544139 then (if x < 7510997160 then 199 else 455) else (if x < 7511545400 then 487 else 231)) else (if x < 7513260511 then (if x < 7512651792 then 711 else 967) else (if x < 7513261772 then 999 else 743))) else (if x < 7559662203 then (if x < 7558132957 then (if x < 7557057647 then 500 else 244) else (if x < 7558134032 then 212 else 468)) else (if x < 7559849329 then (if x < 7559663075 then 1012 else 756) else (if x < 7559850404 then 724 else 980)))) else (if x < 7632906464 then (if x < 7608490085 then (if x < 7608218429 then (if x < 7606717804 then 67 else 323) else (if x < 7608219508 then 931 else 675)) else (if x < 7608572575 then (if x < 7608491164 then 419 else 163) else (if x < 7608574120 then 579 else 835))) else (if x < 7633180178 then (if x < 7632927086 then (if x < 7632907861 then 400 else 144) else (if x < 7632928429 then 368 else 112)) else (if x < 7636335134 then (if x < 7633181575 then 912 else 656) else (if x < 7636336477 then 880 else 624))))) else (if x < 7819282542 then (if x < 7798105973 then (if x < 7648228216 then (if x < 7646497438 then (if x < 7646000629 then 566 else 822) else (if x < 7646498358 then 278 else 22)) else (if x < 7648605692 then (if x < 7648229136 then 790 else 534) else (if x < 7648606057 then 54 else 310))) else (if x < 7800691900 then (if x < 7799944846 then (if x < 7798106143 then 883 else 627) else (if x < 7799945482 then 659 else 915)) else (if x < 7801514021 then (if x < 7800692536 then 147 else 403) else (if x < 7801514191 then 371 else 115)))) else (if x < 7848619499 then (if x < 7821868050 then (if x < 7821120996 then (if x < 7819283204 then 819 else 563) else (if x < 7821121265 then 531 else 787)) else (if x < 7822690590 then (if x < 7821868319 then 19 else 275) else (if x < 7822691252 then 307 else 51))) else (if x < 7852015199 then (if x < 7850983766 then (if x < 7848620568 then 474 else 218) else (if x < 7850983910 then 762 else 1018)) else (if x < 7852066274 then (if x < 7852016268 then 986 else 730) else (if x < 7852066418 then 250 else 506)))))) else (if x < 8404130103 then (if x < 8110812811 then (if x < 8061066359 then (if x < 7902339557 then (if x < 7901592503 then (if x < 7899756424 then 691 else 947) else (if x < 7901592673 then 851 else 595)) else (if x < 7903163836 then (if x < 7902339727 then 339 else 83) else (if x < 7903164472 then 179 else 435))) else (if x < 8063294433 then (if x < 8061563655 then (if x < 8061066379 then 630 else 886) else (if x < 8061563783 then 150 else 406)) else (if x < 8063671787 then (if x < 8063294561 then 662 else 918) else (if x < 8063671807 then 118 else 374)))) else (if x < 8251025148 then (if x < 8112800839 then (if x < 8111889275 then (if x < 8110813652 then 341 else 85) else (if x < 8111889767 then 181 else 437)) else (if x < 8114494703 then (if x < 8112801680 then 853 else 597) else (if x < 8114495195 then 693 else 949))) else (if x < 8254091568 then (if x < 8251656505 then (if x < 8251025960 then 279 else 23) else (if x < 8251656661 then 823 else 567)) else (if x < 8254261933 then (if x < 8254092380 then 791 else 535) else (if x < 8254262089 then 311 else 55))))) else (if x < 8492440316 then (if x < 8446095800 then (if x < 8406359657 then (if x < 8404628879 then (if x < 8404130231 then 694 else 950) else (if x < 8404628899 then 86 else 342)) else (if x < 8406735531 then (if x < 8406359677 then 598 else 854) else (if x < 8406735659 then 182 else 438))) else (if x < 8446369514 then (if x < 8446117129 then (if x < 8446097230 then 16 else 272) else (if x < 8446117254 then 48 else 304)) else (if x < 8449525177 then (if x < 8446370944 then 528 else 784) else (if x < 8449525302 then 560 else 816)))) else (if x < 8525878613 then (if x < 8494024858 then (if x < 8493654418 then (if x < 8492441889 then 781 else 525) else (if x < 8493654672 then 557 else 813)) else (if x < 8495506736 then (if x < 8494025112 then 45 else 301) else (if x < 8495508309 then 269 else 13))) else (if x < 8527866641 then (if x < 8526954817 then (if x < 8525879105 then 149 else 405) else (if x < 8526955658 then 373 else 117)) else (if x < 8529560245 then (if x < 8527867133 then 661 else 917) else (if x < 8529561086 then 885 else 629))))))))))

def decode (g : Equiv.Perm (Fin 2058)) : ℕ := decodeCode (((0 * 2058 + (g 0).val) * 2058 + (g 1).val) * 2058 + (g 2).val)

abbrev decode_normalPredicate (x : Fin 1024) : Prop := decode (normalTable x) = x.val

private theorem decode_normal_block0 : checkFin 64 (fun j => decide (decode_normalPredicate (blockIndex 1024 64 (by decide) 0 j.val))) = true := by decide +kernel
private theorem decode_normal_block1 : checkFin 64 (fun j => decide (decode_normalPredicate (blockIndex 1024 64 (by decide) 1 j.val))) = true := by decide +kernel
private theorem decode_normal_block2 : checkFin 64 (fun j => decide (decode_normalPredicate (blockIndex 1024 64 (by decide) 2 j.val))) = true := by decide +kernel
private theorem decode_normal_block3 : checkFin 64 (fun j => decide (decode_normalPredicate (blockIndex 1024 64 (by decide) 3 j.val))) = true := by decide +kernel
private theorem decode_normal_block4 : checkFin 64 (fun j => decide (decode_normalPredicate (blockIndex 1024 64 (by decide) 4 j.val))) = true := by decide +kernel
private theorem decode_normal_block5 : checkFin 64 (fun j => decide (decode_normalPredicate (blockIndex 1024 64 (by decide) 5 j.val))) = true := by decide +kernel
private theorem decode_normal_block6 : checkFin 64 (fun j => decide (decode_normalPredicate (blockIndex 1024 64 (by decide) 6 j.val))) = true := by decide +kernel
private theorem decode_normal_block7 : checkFin 64 (fun j => decide (decode_normalPredicate (blockIndex 1024 64 (by decide) 7 j.val))) = true := by decide +kernel
private theorem decode_normal_block8 : checkFin 64 (fun j => decide (decode_normalPredicate (blockIndex 1024 64 (by decide) 8 j.val))) = true := by decide +kernel
private theorem decode_normal_block9 : checkFin 64 (fun j => decide (decode_normalPredicate (blockIndex 1024 64 (by decide) 9 j.val))) = true := by decide +kernel
private theorem decode_normal_block10 : checkFin 64 (fun j => decide (decode_normalPredicate (blockIndex 1024 64 (by decide) 10 j.val))) = true := by decide +kernel
private theorem decode_normal_block11 : checkFin 64 (fun j => decide (decode_normalPredicate (blockIndex 1024 64 (by decide) 11 j.val))) = true := by decide +kernel
private theorem decode_normal_block12 : checkFin 64 (fun j => decide (decode_normalPredicate (blockIndex 1024 64 (by decide) 12 j.val))) = true := by decide +kernel
private theorem decode_normal_block13 : checkFin 64 (fun j => decide (decode_normalPredicate (blockIndex 1024 64 (by decide) 13 j.val))) = true := by decide +kernel
private theorem decode_normal_block14 : checkFin 64 (fun j => decide (decode_normalPredicate (blockIndex 1024 64 (by decide) 14 j.val))) = true := by decide +kernel
private theorem decode_normal_block15 : checkFin 64 (fun j => decide (decode_normalPredicate (blockIndex 1024 64 (by decide) 15 j.val))) = true := by decide +kernel

theorem decode_normal : ∀ x, decode_normalPredicate x := by
  apply allBlocks (b := 16) (m := 64) (by decide) (by decide) (by decide)
  intro k
  fin_cases k
  · exact allFin _ _ decode_normal_block0
  · exact allFin _ _ decode_normal_block1
  · exact allFin _ _ decode_normal_block2
  · exact allFin _ _ decode_normal_block3
  · exact allFin _ _ decode_normal_block4
  · exact allFin _ _ decode_normal_block5
  · exact allFin _ _ decode_normal_block6
  · exact allFin _ _ decode_normal_block7
  · exact allFin _ _ decode_normal_block8
  · exact allFin _ _ decode_normal_block9
  · exact allFin _ _ decode_normal_block10
  · exact allFin _ _ decode_normal_block11
  · exact allFin _ _ decode_normal_block12
  · exact allFin _ _ decode_normal_block13
  · exact allFin _ _ decode_normal_block14
  · exact allFin _ _ decode_normal_block15

theorem order : Nat.card (Subgroup.closure (Set.range input)) = 1024 := by
  apply Nat.le_antisymm upper_bound
  apply lower_bound _ 1024 normalForm (fun x => decode (representation x))
  · intro v
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hx
    apply Subgroup.pow_mem
    exact evalSigned_mem input (pcWord k) _
      (fun i => Subgroup.subset_closure (Set.mem_range_self i))
  · intro v
    rw [← normalTable_eq]
    exact decode_normal v

end Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate.Factors.Pair00Two
