module

public import Mathlib.GroupTheory.OrderOfElement
public import Theory.Mathieu.M24.Basic

open Theory.GroupTheory

namespace Sporadic.Mathieu

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

open scoped Pointwise

/-- The Atlas `2A` representative: the involution fixing the standard octad
pointwise and acting as eight transpositions on its complement. -/
@[expose] public def m24Involution2A : Equiv.Perm (Fin 24) :=
  Equiv.swap (6 : Fin 24) 7 * Equiv.swap 8 23 * Equiv.swap 9 12 *
    Equiv.swap 10 18 * Equiv.swap 13 22 * Equiv.swap 14 20 *
    Equiv.swap 15 19 * Equiv.swap 16 21

/-- The Atlas `2B` representative, the first standard generator. -/
@[expose] public def m24Involution2B : Equiv.Perm (Fin 24) := m24GeneratorA

/-- The Atlas `3A` representative: a fixed-point-free order-three element. -/
@[expose] public def m24Element3A : Equiv.Perm (Fin 24) :=
  m24GeneratorA * (m24GeneratorB * (m24GeneratorA * (m24GeneratorB * (m24GeneratorB * (m24GeneratorA * (m24GeneratorB * (m24GeneratorA * (m24GeneratorA * (m24GeneratorB * (m24GeneratorB * (m24GeneratorB * (m24GeneratorA * (m24GeneratorB * (m24GeneratorB * (m24GeneratorA * (m24GeneratorB * (m24GeneratorB * (m24GeneratorB * (m24GeneratorB * (m24GeneratorA * (m24GeneratorB * (m24GeneratorB * (m24GeneratorA * (m24GeneratorB * (m24GeneratorA * (m24GeneratorB * (m24GeneratorB * (m24GeneratorA * (m24GeneratorA * (m24GeneratorA * (m24GeneratorB * (m24GeneratorB * (m24GeneratorB * (m24GeneratorA * (m24GeneratorB * (m24GeneratorA * (m24GeneratorA * (m24GeneratorB * (m24GeneratorB)))))))))))))))))))))))))))))))))))))))

/-- The Atlas `3B` representative, the second standard generator. -/
@[expose] public def m24Element3B : Equiv.Perm (Fin 24) := m24GeneratorB

/-- The `2A` representative has order two. -/
public theorem m24Involution2A_order : orderOf m24Involution2A = 2 := by
  apply orderOf_eq_prime
  · decide
  · decide

/-- The `2B` representative has order two. -/
public theorem m24Involution2B_order : orderOf m24Involution2B = 2 := by
  exact m24GeneratorA_order

/-- The `3A` representative has order three. -/
public theorem m24Element3A_order : orderOf m24Element3A = 3 := by
  apply orderOf_eq_prime
  · decide
  · decide

/-- The `3B` representative has order three. -/
public theorem m24Element3B_order : orderOf m24Element3B = 3 := by
  exact m24GeneratorB_order

/-- The `2A` representative fixes eight points (the standard octad). -/
public theorem m24Involution2A_fixed_card :
    ((m24Involution2A : Equiv.Perm (Fin 24)).support).card = 16 := by
  decide +kernel

/-- The `2B` representative fixes no point. -/
public theorem m24Involution2B_fixed_card :
    ((m24Involution2B : Equiv.Perm (Fin 24)).support).card = 24 := by
  decide +kernel

/-- The `3A` representative fixes no point. -/
public theorem m24Element3A_fixed_card :
    ((m24Element3A : Equiv.Perm (Fin 24)).support).card = 24 := by
  decide +kernel

/-- The `3B` representative fixes six points. -/
public theorem m24Element3B_fixed_card :
    ((m24Element3B : Equiv.Perm (Fin 24)).support).card = 18 := by
  decide +kernel

/-- The two involution representatives are distinct. -/
public theorem m24Involution2A_ne_2B : m24Involution2A ≠ m24Involution2B := by
  intro h
  have hc := congrArg (fun g : Equiv.Perm (Fin 24) => (g.support).card) h
  rw [m24Involution2A_fixed_card, m24Involution2B_fixed_card] at hc
  omega

/-- The two order-three representatives are distinct. -/
public theorem m24Element3A_ne_3B : m24Element3A ≠ m24Element3B := by
  intro h
  have hc := congrArg (fun g : Equiv.Perm (Fin 24) => (g.support).card) h
  rw [m24Element3A_fixed_card, m24Element3B_fixed_card] at hc
  omega





/-- The `2B` representative belongs to M24. -/
public theorem m24Involution2B_mem : m24Involution2B ∈ M24 := by
  change m24GeneratorA ∈ M24
  exact m24GeneratorA_mem

/-- The `3B` representative belongs to M24. -/
public theorem m24Element3B_mem : m24Element3B ∈ M24 := by
  change m24GeneratorB ∈ M24
  exact m24GeneratorB_mem


private theorem m24TestSmul0 : m24Involution2A • m24BlockAt (0 : Fin 759) = m24BlockAt (0 : Fin 759) := by
  decide +kernel

private theorem m24TestSmul5 : m24Involution2A • m24BlockAt (5 : Fin 759) = m24BlockAt (6 : Fin 759) := by
  decide +kernel

private theorem m24TestSmul100 : m24Involution2A • m24BlockAt (100 : Fin 759) = m24BlockAt (101 : Fin 759) := by
  decide +kernel
@[expose] public def m24Involution2AIndexChunk0 : Array (Fin 759) := #[
  0, 2, 1, 4, 3, 6, 5, 8, 7, 9, 13, 12,
  11, 10, 14, 20, 16, 19, 18, 17, 15, 22, 21, 24,
  23, 25, 28, 29, 26, 27, 34, 31, 35, 33, 30, 32,
  36, 37, 40, 41, 38, 39, 46, 45, 44, 43, 42, 47,
  48, 50, 49, 61, 64, 58, 63, 62, 60, 59, 53, 57,
  56, 51, 55, 54, 52, 71, 67, 66, 76, 74, 75, 65,
  73, 72, 69, 70, 68, 78, 77, 80, 79, 81, 84, 85,
  82, 83, 91, 90, 88, 89, 87, 86, 92, 93, 96, 97,
]

@[expose] public def m24Involution2AIndexChunk1 : Array (Fin 759) := #[
  94, 95, 102, 99, 101, 100, 98, 103, 104, 106, 105, 114,
  116, 120, 119, 118, 117, 115, 107, 113, 108, 112, 111, 110,
  109, 127, 125, 131, 132, 122, 130, 121, 129, 128, 126, 123,
  124, 133, 137, 136, 135, 134, 138, 144, 143, 141, 142, 140,
  139, 146, 145, 158, 155, 157, 156, 154, 159, 160, 151, 148,
  150, 149, 147, 152, 153, 170, 169, 168, 166, 167, 164, 165,
  163, 162, 161, 172, 171, 174, 173, 187, 186, 184, 185, 183,
  182, 188, 180, 179, 177, 178, 176, 175, 181, 198, 196, 192,
]

@[expose] public def m24Involution2AIndexChunk2 : Array (Fin 759) := #[
  191, 197, 195, 194, 190, 193, 189, 200, 199, 204, 207, 206,
  201, 205, 203, 202, 222, 221, 230, 231, 224, 220, 228, 229,
  227, 226, 225, 223, 213, 209, 208, 219, 212, 218, 217, 216,
  214, 215, 210, 211, 247, 244, 238, 242, 243, 237, 234, 252,
  251, 241, 235, 236, 233, 250, 249, 232, 248, 246, 245, 240,
  239, 253, 254, 255, 256, 262, 261, 260, 259, 258, 257, 265,
  268, 263, 267, 266, 264, 274, 273, 272, 271, 270, 269, 280,
  279, 278, 277, 276, 275, 282, 281, 283, 291, 293, 292, 290,
]

@[expose] public def m24Involution2AIndexChunk3 : Array (Fin 759) := #[
  295, 294, 287, 284, 286, 285, 289, 288, 296, 305, 306, 304,
  302, 303, 300, 301, 299, 297, 298, 307, 308, 313, 312, 314,
  310, 309, 311, 318, 317, 316, 315, 320, 319, 323, 322, 321,
  330, 335, 334, 332, 333, 331, 324, 329, 327, 328, 326, 325,
  343, 341, 338, 348, 347, 337, 346, 336, 344, 345, 342, 340,
  339, 351, 350, 349, 362, 363, 358, 361, 360, 359, 354, 357,
  356, 355, 352, 353, 367, 370, 366, 364, 376, 369, 365, 375,
  374, 373, 372, 371, 368, 380, 379, 378, 377, 382, 381, 406,
]

@[expose] public def m24Involution2AIndexChunk4 : Array (Fin 759) := #[
  396, 405, 402, 399, 404, 403, 401, 398, 400, 397, 407, 408,
  384, 393, 391, 387, 392, 390, 386, 389, 388, 385, 383, 394,
  395, 417, 426, 424, 425, 422, 421, 416, 415, 409, 423, 420,
  419, 414, 413, 418, 411, 412, 410, 428, 427, 432, 433, 434,
  429, 430, 431, 438, 437, 436, 435, 440, 439, 441, 443, 442,
  452, 455, 454, 453, 450, 451, 448, 449, 444, 447, 446, 445,
  463, 458, 457, 468, 460, 467, 466, 456, 464, 465, 462, 461,
  459, 471, 470, 469, 478, 483, 481, 482, 480, 479, 472, 477,
]

@[expose] public def m24Involution2AIndexChunk5 : Array (Fin 759) := #[
  476, 474, 475, 473, 491, 490, 486, 496, 495, 489, 485, 484,
  494, 493, 492, 488, 487, 500, 499, 498, 497, 502, 501, 526,
  525, 524, 522, 520, 516, 523, 521, 519, 518, 517, 527, 528,
  508, 513, 512, 511, 507, 510, 506, 509, 505, 504, 503, 514,
  515, 531, 546, 529, 545, 542, 541, 536, 535, 543, 544, 540,
  539, 534, 533, 537, 538, 532, 530, 548, 547, 550, 549, 551,
  561, 558, 560, 559, 563, 562, 553, 555, 554, 552, 557, 556,
  575, 574, 571, 572, 568, 573, 570, 566, 567, 569, 565, 564,
]

@[expose] public def m24Involution2AIndexChunk6 : Array (Fin 759) := #[
  576, 582, 581, 580, 579, 578, 577, 603, 601, 598, 608, 607,
  599, 597, 606, 605, 596, 604, 602, 600, 592, 589, 585, 588,
  595, 584, 594, 583, 593, 591, 590, 587, 586, 620, 614, 619,
  613, 612, 610, 627, 628, 618, 617, 611, 609, 625, 626, 624,
  623, 621, 622, 615, 616, 631, 634, 629, 633, 632, 630, 654,
  650, 649, 660, 653, 659, 648, 657, 658, 656, 655, 652, 651,
  641, 637, 636, 647, 646, 639, 635, 645, 644, 642, 643, 640,
  638, 674, 673, 670, 666, 669, 664, 679, 680, 665, 663, 677,
]

@[expose] public def m24Involution2AIndexChunk7 : Array (Fin 759) := #[
  678, 662, 661, 676, 675, 671, 672, 667, 668, 681, 691, 689,
  684, 685, 690, 687, 688, 683, 686, 682, 692, 693, 722, 716,
  731, 730, 729, 727, 726, 721, 728, 725, 720, 719, 723, 724,
  717, 718, 715, 714, 733, 732, 711, 710, 695, 708, 709, 705,
  704, 701, 694, 706, 707, 703, 700, 699, 702, 698, 697, 696,
  713, 712, 746, 740, 736, 737, 756, 757, 735, 755, 754, 751,
  744, 745, 734, 753, 752, 749, 750, 743, 748, 747, 742, 741,
  738, 739, 758,
]

@[reducible, expose]
public def m24Involution2AIndexValue (i : Fin 759) : Fin 759 :=
  if h0 : i.val < 96 then
    m24Involution2AIndexChunk0[i.val]'(by change i.val < 96; omega)
  else if h1 : i.val < 192 then
    m24Involution2AIndexChunk1[i.val - 96]'(by change i.val - 96 < 96; omega)
  else if h2 : i.val < 288 then
    m24Involution2AIndexChunk2[i.val - 192]'(by change i.val - 192 < 96; omega)
  else if h3 : i.val < 384 then
    m24Involution2AIndexChunk3[i.val - 288]'(by change i.val - 288 < 96; omega)
  else if h4 : i.val < 480 then
    m24Involution2AIndexChunk4[i.val - 384]'(by change i.val - 384 < 96; omega)
  else if h5 : i.val < 576 then
    m24Involution2AIndexChunk5[i.val - 480]'(by change i.val - 480 < 96; omega)
  else if h6 : i.val < 672 then
    m24Involution2AIndexChunk6[i.val - 576]'(by change i.val - 576 < 96; omega)
  else
    m24Involution2AIndexChunk7[i.val - 672]'(by change i.val - 672 < 87; omega)

@[expose] public def m24Involution2AIndex (i : Fin 759) : Fin 759 :=
  m24Involution2AIndexValue i

private theorem m24Involution2A_smul_all :
    ∀ i : Fin 759, m24Involution2A • m24BlockAt i = m24BlockAt (m24Involution2AIndex i) := by
  intro i
  fin_cases i
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

/-- The `2A` representative is an involution. -/
private theorem m24Involution2A_sq : m24Involution2A * m24Involution2A = 1 := by
  decide

/-- The block map `m24BlockAt` is injective. -/
private theorem m24BlockAt_injective : Function.Injective m24BlockAt := by
  intro i j hij
  apply m24BlockMessage_injective
  apply m24GolayWord_injective
  simpa only [m24BlockAt_eq_m24GolayWord] using hij

/-- The `2A` representative acts as an involution on every point. -/
private theorem m24Involution2A_involutive_point :
    ∀ x : Fin 24, m24Involution2A (m24Involution2A x) = x := by
  intro x
  fin_cases x <;> decide

private theorem m24Involution2A_sq_smul (S : Finset (Fin 24)) :
    m24Involution2A • (m24Involution2A • S) = S := by
  ext x
  simp [Finset.mem_smul_finset, m24Involution2A_involutive_point]

/-- The block index map of the `2A` representative is an involution. -/
private theorem m24Involution2AIndex_involutive :
    ∀ j : Fin 759, m24Involution2AIndex (m24Involution2AIndex j) = j := by
  intro j
  apply m24BlockAt_injective
  calc
    m24BlockAt (m24Involution2AIndex (m24Involution2AIndex j))
        = m24Involution2A • m24BlockAt (m24Involution2AIndex j) := (m24Involution2A_smul_all _).symm
    _ = m24Involution2A • (m24Involution2A • m24BlockAt j) := by
        exact congrArg (fun B : Finset (Fin 24) => m24Involution2A • B)
          (m24Involution2A_smul_all j).symm
    _ = m24BlockAt j := m24Involution2A_sq_smul (m24BlockAt j)

private theorem m24Involution2A_blocks_smul :
    m24Involution2A • m24Blocks = m24Blocks := by
  apply m24Blocks_smul_of_reindex m24Involution2A m24Involution2AIndex
  · intro i
    exact ⟨m24Involution2AIndex i, m24Involution2AIndex_involutive i⟩
  · intro i
    -- need: m24Involution2A • m24BlockAt i = m24BlockAt (m24Involution2AIndex i)
    exact m24Involution2A_smul_all i


/-- The `2A` representative fixes the standard octad `{0,1,2,3,4,5,11,17}` pointwise. -/
public theorem m24Involution2A_fixes_octad :
    m24Involution2A • ({0, 1, 2, 3, 4, 5, 11, 17} : Finset (Fin 24)) =
      {0, 1, 2, 3, 4, 5, 11, 17} := by
  decide +kernel

/-- The `2A` representative belongs to M24. -/
public theorem m24Involution2A_mem : m24Involution2A ∈ M24 := by
  change m24Involution2A ∈ m24WittDesign.aut
  rw [SteinerSystem.mem_aut_iff]
  rw [m24WittDesign_blocks]
  have h := congrArg (fun s : Finset (Finset (Fin 24)) => (s : Set (Finset (Fin 24))))
    m24Involution2A_blocks_smul
  simpa only [Finset.coe_smul_finset] using h

public theorem m24Element3A_mem : m24Element3A ∈ M24 := by
  change (m24GeneratorA * (m24GeneratorB * (m24GeneratorA * (m24GeneratorB * (m24GeneratorB * (m24GeneratorA * (m24GeneratorB * (m24GeneratorA * (m24GeneratorA * (m24GeneratorB * (m24GeneratorB * (m24GeneratorB * (m24GeneratorA * (m24GeneratorB * (m24GeneratorB * (m24GeneratorA * (m24GeneratorB * (m24GeneratorB * (m24GeneratorB * (m24GeneratorB * (m24GeneratorA * (m24GeneratorB * (m24GeneratorB * (m24GeneratorA * (m24GeneratorB * (m24GeneratorA * (m24GeneratorB * (m24GeneratorB * (m24GeneratorA * (m24GeneratorA * (m24GeneratorA * (m24GeneratorB * (m24GeneratorB * (m24GeneratorB * (m24GeneratorA * (m24GeneratorB * (m24GeneratorA * (m24GeneratorA * (m24GeneratorB * (m24GeneratorB)))))))))))))))))))))))))))))))))))))))) ∈ M24
  exact M24.mul_mem m24GeneratorA_mem (M24.mul_mem m24GeneratorB_mem (M24.mul_mem m24GeneratorA_mem (M24.mul_mem m24GeneratorB_mem (M24.mul_mem m24GeneratorB_mem (M24.mul_mem m24GeneratorA_mem (M24.mul_mem m24GeneratorB_mem (M24.mul_mem m24GeneratorA_mem (M24.mul_mem m24GeneratorA_mem (M24.mul_mem m24GeneratorB_mem (M24.mul_mem m24GeneratorB_mem (M24.mul_mem m24GeneratorB_mem (M24.mul_mem m24GeneratorA_mem (M24.mul_mem m24GeneratorB_mem (M24.mul_mem m24GeneratorB_mem (M24.mul_mem m24GeneratorA_mem (M24.mul_mem m24GeneratorB_mem (M24.mul_mem m24GeneratorB_mem (M24.mul_mem m24GeneratorB_mem (M24.mul_mem m24GeneratorB_mem (M24.mul_mem m24GeneratorA_mem (M24.mul_mem m24GeneratorB_mem (M24.mul_mem m24GeneratorB_mem (M24.mul_mem m24GeneratorA_mem (M24.mul_mem m24GeneratorB_mem (M24.mul_mem m24GeneratorA_mem (M24.mul_mem m24GeneratorB_mem (M24.mul_mem m24GeneratorB_mem (M24.mul_mem m24GeneratorA_mem (M24.mul_mem m24GeneratorA_mem (M24.mul_mem m24GeneratorA_mem (M24.mul_mem m24GeneratorB_mem (M24.mul_mem m24GeneratorB_mem (M24.mul_mem m24GeneratorB_mem (M24.mul_mem m24GeneratorA_mem (M24.mul_mem m24GeneratorB_mem (M24.mul_mem m24GeneratorA_mem (M24.mul_mem m24GeneratorA_mem (M24.mul_mem m24GeneratorB_mem (m24GeneratorB_mem)))))))))))))))))))))))))))))))))))))))

end Sporadic.Mathieu
