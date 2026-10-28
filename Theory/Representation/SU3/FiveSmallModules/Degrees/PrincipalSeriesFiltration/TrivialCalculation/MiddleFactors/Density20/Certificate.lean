module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.MiddleFactors.Data
public import Theory.Representation.PSL3Three.AbsoluteDegrees.PrincipalModels.CycleSimplicity.Arithmetic
public import Mathlib.Tactic.FinCases

/-!
# Checked rank-one and spanning certificates in degree 20

For M = A₀² + A₁², the straight-line program evaluates
p(M) = M¹⁹ + M¹⁸ + M¹¹ + M¹⁰ + M⁶ + M⁴ + M³ at index 30.
Its value is the outer product of the displayed column and row. Twenty
left and twenty right actor words give spanning columns and rows; their
explicit inverses certify both assertions. All arithmetic is checked by
kernel reduction through the proved packed binary-matrix checker.

The witnesses are from `MiddleFactors/source/density20_witnesses.json`;
`Density20/source/generate.py` generates this certificate. Python assertions
are only diagnostics. The public density theorem uses the Lean proofs below.

Source motivation: Guralnick–Malle, Classification of 2F-modules I,
Proposition 4.3; Aschbacher–Smith K.2, printed p.453.
-/

@[expose] public section

open Thompson.BinaryMatrix CycleCertificate
open scoped Matrix
namespace Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation.MiddleFactors.Density20Certificate

def values : Array (Array ℕ) := #[
  #[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288],
  #[517886, 426114, 98039, 390143, 352255, 456703, 524420, 124031, 1048191, 956672, 1047807, 2048, 924576, 97663, 1013487, 618111, 311424, 753023, 430528, 96127],
  #[288322, 365904, 296001, 281376, 9632, 459552, 798752, 29540, 111712, 25408, 377952, 17408, 391016, 94240, 386624, 13376, 274976, 112448, 94208, 28928],
  #[486750, 255549, 1042751, 389119, 133120, 372479, 126455, 137824, 920320, 268384, 95871, 2048, 326815, 694720, 251647, 299616, 93487, 37824, 820196, 264384],
  #[648240, 582792, 841282, 132672, 159844, 139616, 165224, 983401, 947784, 618848, 943936, 8736, 1014792, 151560, 554752, 881416, 169768, 565832, 348968, 54632],
  #[952686, 721589, 212861, 518591, 30820, 495519, 223391, 858889, 32072, 878848, 987455, 10784, 753815, 575944, 762367, 647528, 260615, 536968, 643276, 318888],
  #[952686, 721589, 212861, 518591, 30820, 495519, 223391, 858889, 32072, 878848, 987455, 10784, 753815, 575944, 762367, 647528, 260615, 536968, 643276, 318888],
  #[952687, 721591, 212857, 518583, 30836, 495551, 223455, 859017, 31816, 879360, 988479, 8736, 757911, 584136, 778751, 614760, 195079, 668040, 905420, 843176],
  #[602357, 927603, 479794, 302368, 1008281, 156823, 515955, 799300, 217759, 41276, 295145, 143191, 434195, 498102, 867140, 474223, 184262, 338561, 889399, 456218],
  #[23694, 976108, 239205, 227579, 836704, 1023819, 581803, 228057, 703891, 160977, 44412, 488266, 342619, 195822, 55222, 774938, 921622, 799300, 48321, 918493],
  #[906505, 888391, 117251, 585478, 310220, 492216, 434693, 592684, 125686, 1002123, 927569, 549950, 348715, 11041, 595021, 479489, 457175, 228057, 354768, 818426],
  #[80837, 38957, 619115, 280168, 320455, 759398, 5879, 606362, 362973, 1006937, 158150, 34604, 167768, 848209, 688436, 839181, 524464, 592684, 466534, 1028540],
  #[936117, 1022956, 271211, 198579, 428779, 251183, 444515, 855607, 510101, 250366, 868489, 572738, 460531, 122993, 112774, 475200, 930138, 606362, 463619, 141732],
  #[650706, 308151, 690216, 436689, 974177, 767358, 190248, 910881, 42122, 272093, 77124, 612834, 814282, 222546, 810705, 709155, 652042, 855607, 66631, 591043],
  #[516576, 144615, 344392, 7184, 644309, 104820, 56192, 983282, 1034652, 472421, 270970, 372499, 247504, 1039745, 1047695, 672100, 512293, 910881, 603905, 249565],
  #[516577, 144613, 344396, 7192, 644293, 104788, 56256, 983154, 1034396, 472933, 271994, 370451, 251600, 1047937, 1031311, 704868, 446757, 1041953, 866049, 773853],
  #[1022515, 9202, 411681, 207443, 144149, 123670, 691710, 613178, 858611, 657016, 726357, 849059, 948290, 727827, 988115, 592258, 157056, 471418, 78373, 741617],
  #[1022514, 9200, 411685, 207451, 144133, 123702, 691646, 613306, 858355, 656504, 725333, 851107, 944194, 736019, 1004499, 625026, 222592, 340346, 340517, 217329],
  #[332154, 809453, 21271, 996344, 776844, 765219, 1012634, 802647, 610914, 35780, 675088, 794878, 922833, 299695, 29666, 559123, 709830, 92850, 930584, 845796],
  #[631674, 972993, 784866, 456238, 153804, 228500, 176740, 642865, 363122, 627691, 553964, 234678, 77784, 856508, 459348, 583007, 815937, 802647, 847904, 999992],
  #[225065, 797748, 833083, 707419, 171924, 148512, 534722, 931578, 70994, 248949, 789387, 289397, 65237, 733324, 1007045, 226658, 331901, 642865, 756531, 4176],
  #[287649, 931637, 18675, 188480, 402224, 724695, 610147, 90859, 984233, 1022320, 1002081, 971436, 58934, 365235, 681041, 240365, 1010324, 931578, 636167, 561260],
  #[287648, 931639, 18679, 188488, 402208, 724727, 610083, 90731, 984489, 1022832, 1003105, 973484, 63030, 373427, 664657, 207597, 944788, 800506, 898311, 36972],
  #[866341, 340889, 310036, 408055, 242523, 161011, 830787, 753236, 679643, 853528, 351077, 1047960, 834500, 167125, 437570, 910018, 347115, 611171, 886661, 151613],
  #[503184, 29792, 852362, 905144, 853359, 247713, 360663, 361246, 194241, 728711, 943320, 132006, 514000, 874014, 517529, 812575, 469809, 753236, 376422, 374967],
  #[503185, 29794, 852366, 905136, 853375, 247681, 360599, 361374, 194497, 728199, 942296, 134054, 509904, 882206, 501145, 845343, 404273, 622164, 114278, 899255],
  #[1023927, 531498, 804181, 291921, 285033, 531464, 531560, 813297, 772047, 512, 1029782, 501438, 808273, 773103, 547880, 317817, 878705, 897686, 514791, 535840],
  #[1023926, 531496, 804177, 291929, 285049, 531496, 531496, 813169, 771791, 0, 1028758, 503486, 804177, 781295, 531496, 285049, 813169, 1028758, 252647, 11552],
  #[285049, 0, 285049, 285049, 285049, 0, 0, 285049, 0, 0, 285049, 285049, 285049, 0, 0, 285049, 285049, 285049, 0, 0],
  #[285049, 0, 285049, 285049, 285049, 0, 0, 285049, 0, 0, 285049, 285049, 285049, 0, 0, 285049, 285049, 285049, 0, 0],
  #[285049, 0, 285049, 285049, 285049, 0, 0, 285049, 0, 0, 285049, 285049, 285049, 0, 0, 285049, 285049, 285049, 0, 0],
  #[491433, 555364, 1041722, 950191, 420991, 965823, 948127, 982723, 246692, 486507, 344660, 35344, 962571, 141135, 807380, 563876, 104928, 283428, 315568, 1044047],
  #[774037, 333108, 959135, 1022463, 744959, 1038591, 296485, 1015475, 661723, 296200, 657663, 17408, 238156, 740859, 671327, 990387, 315748, 691131, 586572, 748219],
  #[557022, 622105, 428964, 262304, 750975, 297008, 654239, 327844, 914623, 423195, 784063, 2048, 84868, 748891, 621759, 100964, 646427, 1046107, 98892, 1015099],
  #[174350, 71868, 1042258, 57476, 151584, 180372, 213124, 789239, 962407, 176552, 1023779, 172160, 919267, 618608, 307324, 982743, 217124, 70392, 843407, 243872],
  #[287257, 958103, 737588, 1015663, 2752, 1046527, 980406, 658572, 800551, 659136, 370063, 35344, 375411, 1011607, 832815, 695836, 976131, 316156, 385987, 559596],
  #[952047, 915951, 118, 137220, 320707, 723204, 595204, 739141, 7540, 306891, 265044, 594816, 150640, 1041359, 1047759, 500367, 104224, 658948, 89968, 197940],
  #[858289, 462787, 511187, 1044215, 127808, 769239, 702103, 1004648, 75104, 1044584, 712411, 17408, 315295, 636492, 679583, 1041256, 175891, 546636, 992837, 882500],
  #[433678, 1005353, 175792, 248895, 785299, 519359, 306879, 635006, 160837, 747602, 546529, 13984, 114042, 645235, 542445, 418157, 737548, 209257, 393356, 575795],
  #[82497, 229582, 229576, 98880, 39872, 810943, 849467, 277559, 131972, 799859, 95803, 2048, 672664, 590184, 914491, 833139, 816179, 625160, 1030771, 1014899],
  #[955786, 791127, 686806, 524135, 845775, 565400, 20888, 205775, 324784, 27615, 404636, 166400, 232263, 921419, 1031404, 535551, 612792, 785700, 690043, 962271],
  #[84398, 925931, 824551, 902399, 488955, 6400, 21765, 38792, 62612, 164612, 937931, 172160, 1560, 811099, 192532, 901335, 694995, 969219, 840023, 815475],
  #[944176, 1005183, 808689, 266280, 428631, 16904, 708648, 114530, 313171, 171591, 778035, 733023, 22507, 153183, 188031, 764212, 776480, 661768, 38603, 878984],
  #[653589, 216945, 20479, 4836, 198220, 399908, 542772, 662097, 657725, 726761, 625205, 594080, 661849, 487991, 203933, 99805, 708376, 247589, 558536, 677868],
  #[1015903, 675153, 307903, 873188, 527216, 180372, 541191, 376394, 138033, 308299, 914111, 594816, 521806, 613953, 199096, 828602, 149109, 21873, 848062, 320266],
  #[329988, 835912, 353600, 526980, 768942, 359663, 326911, 326841, 888132, 899515, 950596, 784283, 361792, 576852, 968004, 45551, 218880, 145407, 246864, 151044],
  #[63545, 136938, 934624, 978771, 152972, 716567, 843623, 14629, 343945, 832218, 489609, 835551, 306597, 267652, 623318, 162957, 142608, 479513, 265348, 942787],
  #[312807, 485257, 64471, 716447, 755967, 965823, 197187, 434366, 895998, 98144, 777207, 8736, 548097, 719830, 887771, 152990, 1005129, 167158, 789545, 239766],
  #[818077, 51658, 168997, 393284, 708539, 403136, 389119, 439845, 510879, 19418, 487327, 17408, 307301, 850866, 445407, 759393, 380890, 646074, 563809, 217050],
  #[565022, 998712, 859432, 263968, 317748, 759120, 640084, 904820, 739332, 663947, 739912, 35344, 1002020, 939820, 744004, 351572, 640124, 134204, 449357, 316412],
  #[242670, 856694, 602870, 776183, 557160, 906943, 390143, 928008, 655616, 698632, 909022, 8736, 106487, 632905, 351999, 952640, 357074, 560169, 819523, 587017],
  #[364002, 374751, 132225, 769371, 812036, 760799, 251901, 326181, 254331, 550436, 80215, 13984, 734170, 91351, 523611, 68745, 104306, 695437, 886646, 670245],
  #[132064, 339716, 861752, 532544, 1007881, 671744, 690976, 929378, 789352, 1025352, 787264, 397376, 273960, 388424, 328520, 118312, 208680, 601376, 511016, 732488],
  #[976183, 273990, 645087, 126455, 1039767, 519359, 533778, 232693, 777109, 669544, 676031, 397376, 12906, 817117, 871062, 55965, 864042, 948149, 241442, 377557],
  #[301817, 481928, 505928, 155744, 198601, 545480, 836737, 692449, 316001, 313686, 544352, 13984, 180737, 227433, 882281, 653001, 1019009, 253633, 649227, 731373]]
def operations : Array Operation := #[.one, .actor 0, .actor 1, .mul 1 1, .mul 2 2, .add 3 4, .mul 0 5, .add 6 0, .mul 7 5, .mul 8 5, .mul 9 5, .mul 10 5, .mul 11 5, .mul 12 5, .mul 13 5, .add 14 0, .mul 15 5, .add 16 0, .mul 17 5, .mul 18 5, .mul 19 5, .mul 20 5, .add 21 0, .mul 22 5, .mul 23 5, .add 24 0, .mul 25 5, .add 26 0, .mul 27 5, .mul 28 5, .mul 29 5, .mul 2 1, .mul 1 2, .mul 1 3, .mul 2 3, .mul 1 31, .mul 2 31, .mul 1 32, .mul 2 32, .mul 1 33, .mul 2 33, .mul 1 34, .mul 2 34, .mul 2 35, .mul 1 36, .mul 2 36, .mul 2 41, .mul 1 4, .mul 1 37, .mul 1 35, .mul 1 47, .mul 1 38, .mul 2 4, .mul 1 52, .mul 1 51]
def leftIndex : Fin 20 → ℕ := ![0, 1, 2, 3, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46]
def rightIndex : Fin 20 → ℕ := ![0, 1, 2, 3, 32, 31, 33, 37, 35, 47, 34, 38, 39, 48, 49, 50, 51, 44, 53, 54]
def columns : Array ℕ := #[510957, 655862, 233701, 330957, 66579, 688330, 328004, 116443, 932464, 771232, 796607, 1015807, 444477, 451288, 588996, 135827, 180277, 10411, 284168, 553766]
def columnInverse : Array ℕ := #[140655, 214483, 283527, 852343, 389334, 339958, 578255, 730197, 42148, 62956, 186239, 422878, 420490, 399798, 469959, 600406, 411397, 633689, 680617, 864273]
def rows : Array ℕ := #[285049, 112501, 764554, 90925, 1009355, 712578, 929894, 186723, 672855, 806486, 785997, 21084, 717841, 922393, 203063, 696922, 558771, 220321, 786673, 250811]
def rowInverse : Array ℕ := #[934627, 924532, 801047, 479144, 869402, 567822, 7525, 273815, 392696, 1036076, 113818, 515107, 303712, 315085, 871052, 148139, 927951, 91616, 472844, 830217]
def column : ℕ := 236701
def row : ℕ := 285049
def columnEntries : Array ℕ := #[1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0]
def columnVectors : Fin 20 → ℕ := ![236701, 691378, 613455, 408745, 114066, 728839, 27119, 192175, 527427, 830849, 282264, 153865, 837892, 683264, 883329, 94885, 2781, 113447, 277833, 544546]

private theorem step_0 : Step 20 factorRows20 values operations 0 := by decide +kernel
private theorem step_1 : Step 20 factorRows20 values operations 1 := by rfl
private theorem step_2 : Step 20 factorRows20 values operations 2 := by rfl
private theorem step_3 : Step 20 factorRows20 values operations 3 := by decide +kernel
private theorem step_4 : Step 20 factorRows20 values operations 4 := by decide +kernel
private theorem step_5 : Step 20 factorRows20 values operations 5 := by decide +kernel
private theorem step_6 : Step 20 factorRows20 values operations 6 := by decide +kernel
private theorem step_7 : Step 20 factorRows20 values operations 7 := by decide +kernel
private theorem step_8 : Step 20 factorRows20 values operations 8 := by decide +kernel
private theorem step_9 : Step 20 factorRows20 values operations 9 := by decide +kernel
private theorem step_10 : Step 20 factorRows20 values operations 10 := by decide +kernel
private theorem step_11 : Step 20 factorRows20 values operations 11 := by decide +kernel
private theorem step_12 : Step 20 factorRows20 values operations 12 := by decide +kernel
private theorem step_13 : Step 20 factorRows20 values operations 13 := by decide +kernel
private theorem step_14 : Step 20 factorRows20 values operations 14 := by decide +kernel
private theorem step_15 : Step 20 factorRows20 values operations 15 := by decide +kernel
private theorem step_16 : Step 20 factorRows20 values operations 16 := by decide +kernel
private theorem step_17 : Step 20 factorRows20 values operations 17 := by decide +kernel
private theorem step_18 : Step 20 factorRows20 values operations 18 := by decide +kernel
private theorem step_19 : Step 20 factorRows20 values operations 19 := by decide +kernel
private theorem step_20 : Step 20 factorRows20 values operations 20 := by decide +kernel
private theorem step_21 : Step 20 factorRows20 values operations 21 := by decide +kernel
private theorem step_22 : Step 20 factorRows20 values operations 22 := by decide +kernel
private theorem step_23 : Step 20 factorRows20 values operations 23 := by decide +kernel
private theorem step_24 : Step 20 factorRows20 values operations 24 := by decide +kernel
private theorem step_25 : Step 20 factorRows20 values operations 25 := by decide +kernel
private theorem step_26 : Step 20 factorRows20 values operations 26 := by decide +kernel
private theorem step_27 : Step 20 factorRows20 values operations 27 := by decide +kernel
private theorem step_28 : Step 20 factorRows20 values operations 28 := by decide +kernel
private theorem step_29 : Step 20 factorRows20 values operations 29 := by decide +kernel
private theorem step_30 : Step 20 factorRows20 values operations 30 := by decide +kernel
private theorem step_31 : Step 20 factorRows20 values operations 31 := by decide +kernel
private theorem step_32 : Step 20 factorRows20 values operations 32 := by decide +kernel
private theorem step_33 : Step 20 factorRows20 values operations 33 := by decide +kernel
private theorem step_34 : Step 20 factorRows20 values operations 34 := by decide +kernel
private theorem step_35 : Step 20 factorRows20 values operations 35 := by decide +kernel
private theorem step_36 : Step 20 factorRows20 values operations 36 := by decide +kernel
private theorem step_37 : Step 20 factorRows20 values operations 37 := by decide +kernel
private theorem step_38 : Step 20 factorRows20 values operations 38 := by decide +kernel
private theorem step_39 : Step 20 factorRows20 values operations 39 := by decide +kernel
private theorem step_40 : Step 20 factorRows20 values operations 40 := by decide +kernel
private theorem step_41 : Step 20 factorRows20 values operations 41 := by decide +kernel
private theorem step_42 : Step 20 factorRows20 values operations 42 := by decide +kernel
private theorem step_43 : Step 20 factorRows20 values operations 43 := by decide +kernel
private theorem step_44 : Step 20 factorRows20 values operations 44 := by decide +kernel
private theorem step_45 : Step 20 factorRows20 values operations 45 := by decide +kernel
private theorem step_46 : Step 20 factorRows20 values operations 46 := by decide +kernel
private theorem step_47 : Step 20 factorRows20 values operations 47 := by decide +kernel
private theorem step_48 : Step 20 factorRows20 values operations 48 := by decide +kernel
private theorem step_49 : Step 20 factorRows20 values operations 49 := by decide +kernel
private theorem step_50 : Step 20 factorRows20 values operations 50 := by decide +kernel
private theorem step_51 : Step 20 factorRows20 values operations 51 := by decide +kernel
private theorem step_52 : Step 20 factorRows20 values operations 52 := by decide +kernel
private theorem step_53 : Step 20 factorRows20 values operations 53 := by decide +kernel
private theorem step_54 : Step 20 factorRows20 values operations 54 := by decide +kernel

private theorem steps : ∀ i : Fin 55, Step 20 factorRows20 values operations i.val := by
  intro i
  fin_cases i
  · exact step_0
  · exact step_1
  · exact step_2
  · exact step_3
  · exact step_4
  · exact step_5
  · exact step_6
  · exact step_7
  · exact step_8
  · exact step_9
  · exact step_10
  · exact step_11
  · exact step_12
  · exact step_13
  · exact step_14
  · exact step_15
  · exact step_16
  · exact step_17
  · exact step_18
  · exact step_19
  · exact step_20
  · exact step_21
  · exact step_22
  · exact step_23
  · exact step_24
  · exact step_25
  · exact step_26
  · exact step_27
  · exact step_28
  · exact step_29
  · exact step_30
  · exact step_31
  · exact step_32
  · exact step_33
  · exact step_34
  · exact step_35
  · exact step_36
  · exact step_37
  · exact step_38
  · exact step_39
  · exact step_40
  · exact step_41
  · exact step_42
  · exact step_43
  · exact step_44
  · exact step_45
  · exact step_46
  · exact step_47
  · exact step_48
  · exact step_49
  · exact step_50
  · exact step_51
  · exact step_52
  · exact step_53
  · exact step_54

/-- Every checked straight-line value lies in any algebra containing the actors. -/
theorem value_mem
    (Q : Subalgebra (ZMod 2) (Matrix (Fin 20) (Fin 20) (ZMod 2)))
    (h : ∀ a, factor20 a ∈ Q) (k : ℕ) (hk : k < 55) :
    decode 20 values[k]! ∈ Q :=
  certificate_mem 20 55 factorRows20 values operations steps Q h k hk

/-- The polynomial value is the outer product of the supplied column and row. -/
theorem rank_one : decode 20 values[30]! =
    Matrix.vecMulVec (fun i : Fin 20 => bit column i.val) (fun j : Fin 20 => bit row j.val) := by
  ext i j
  change bit (values[30]!)[i.val]! j.val = bit column i.val * bit row j.val
  revert i j
  decide +kernel

/-- The left orbit columns have a right inverse. -/
theorem columns_inverse : decode 20 columns * decode 20 columnInverse = 1 :=
  decode_mul_one 20 columns columnInverse (by decide +kernel)

/-- The right orbit rows have a left inverse. -/
theorem rows_inverse : decode 20 rowInverse * decode 20 rows = 1 :=
  decode_mul_one 20 rowInverse rows (by decide +kernel)

/-- The certified words send the rank-one column to the columns of the spanning matrix. -/
theorem left_action (i : Fin 20) :
    decode 20 values[leftIndex i]! *ᵥ (fun j : Fin 20 => bit column j.val) =
      fun j => decode 20 columns j i := by
  have h := decode_mulVec_of_column 20 values[leftIndex i]! columnEntries column (columnVectors i)
    (by decide +kernel) (by revert i; decide +kernel)
  refine h.trans ?_
  funext j
  change bit (columnVectors i) j.val = bit columns[j.val]! i.val
  revert i j
  decide +kernel

/-- The certified words send the rank-one row to the rows of the spanning matrix. -/
theorem right_action (i : Fin 20) :
    (fun j : Fin 20 => bit row j.val) ᵥ* decode 20 values[rightIndex i]! =
      decode 20 rows i :=
  decode_vecMul 20 values[rightIndex i]! row rows[i.val]!
    (by revert i; decide +kernel)

theorem leftIndex_lt (i : Fin 20) : leftIndex i < 55 :=
  (by decide +kernel : ∀ i : Fin 20, leftIndex i < 55) i

theorem rightIndex_lt (i : Fin 20) : rightIndex i < 55 :=
  (by decide +kernel : ∀ i : Fin 20, rightIndex i < 55) i

end Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation.MiddleFactors.Density20Certificate
