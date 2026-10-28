module
public import Theory.Mathieu.M12.ExceptionalParabolics.EightExtensions.Coordinates

/-!
# Certificates for four automorphisms of the first M₁₂ endpoint

The four tables permute the actual 192 word coordinates. Each fixes the identity,
has fourth iterate the identity, and takes every right-generator transition to
multiplication by the proposed generator image. The following automorphism
module turns these finite identities into actual group automorphisms.

Each generator relation has its own certificate to bound kernel memory.
Blocked tables shorten kernel lookup paths; `fastStep_eq` connects them to the
original transition table before the structural word proof is applied.
All candidate data are reconstructed by `../source/generate.py` and checked here;
no external computation is trusted. Source: the marked permutations in
`SmallParabolicPair.Seeds`, following Aschbacher--Smith 14.2.21, printed p.988.
-/

@[expose] public section
namespace Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics.EightExtensions
open Coordinates
set_option maxRecDepth 1000000
set_option Elab.async false

def imageTable : Array (Array (Array (Fin 192))) := #[
  #[#[0,58,23,51,4,39,37,59,43,34,30,56,20,55,14,24],#[46,22,18,15,12,49,47,2,45,42,32,31,38,60,10,7],#[26,61,29,41,40,6,28,25,33,35,5,8,44,19,16,50],#[48,21,17,13,53,52,57,3,1,54,11,27,9,36,62,63],#[182,161,191,137,180,129,177,131,144,152,185,164,190,157,156,162],#[166,153,134,135,169,165,168,163,155,139,149,141,174,147,181,143],#[176,145,183,140,175,146,142,150,186,130,178,172,136,188,171,133],#[154,160,189,159,138,132,158,187,167,128,170,173,179,184,148,151],#[104,76,86,82,125,74,71,102,95,72,106,66,114,112,83,108],#[67,87,115,113,122,79,118,120,85,94,91,107,123,92,103,101],#[93,68,90,97,64,73,124,127,105,100,126,98,88,78,77,84],#[119,109,116,80,65,81,75,110,117,111,121,96,70,99,69,89]],
  #[#[0,1,2,13,4,5,26,27,28,29,10,11,12,3,44,45],#[46,17,48,24,20,49,22,23,19,25,6,7,8,9,30,59],#[37,33,60,35,36,32,43,39,40,41,42,38,14,15,16,47],#[18,21,50,55,52,53,54,51,56,57,58,31,34,61,62,63],#[64,65,66,77,68,69,90,91,92,93,74,75,76,67,108,109],#[110,81,112,88,84,113,86,87,83,89,70,71,72,73,94,123],#[101,97,124,99,100,96,107,103,104,105,106,102,78,79,80,111],#[82,85,114,119,116,117,118,115,120,121,122,95,98,125,126,127],#[128,129,130,141,132,133,154,155,156,157,138,139,140,131,172,173],#[174,145,176,152,148,177,150,151,147,153,134,135,136,137,158,187],#[165,161,188,163,164,160,171,167,168,169,170,166,142,143,144,175],#[146,149,178,183,180,181,182,179,184,185,186,159,162,189,190,191]],
  #[#[0,23,56,48,4,42,43,7,8,31,63,20,58,18,19,49],#[51,52,13,14,11,45,53,1,44,39,38,27,28,59,62,9],#[32,33,34,35,36,37,26,25,40,41,5,6,24,21,55,54],#[3,15,57,16,17,22,47,46,2,50,12,29,60,61,30,10],#[175,153,163,157,145,185,141,177,152,144,150,133,169,137,156,135],#[134,189,171,188,158,160,167,138,162,181,131,149,147,174,178,146],#[173,140,172,184,130,143,183,151,182,186,148,179,136,155,154,168],#[166,165,170,159,132,191,128,187,164,190,161,176,142,180,139,129],#[118,127,100,90,116,75,80,79,108,77,87,126,97,70,124,101],#[73,68,95,92,106,91,74,103,72,65,110,109,78,67,84,115],#[85,122,88,66,120,113,112,86,111,76,114,82,98,96,93,64],#[123,71,94,107,125,89,104,102,99,69,105,119,83,81,121,117]],
  #[#[0,2,1,49,4,5,43,60,8,9,63,12,11,21,55,18],#[19,53,15,16,56,13,54,58,46,25,38,34,28,29,62,31],#[32,61,27,35,40,37,26,39,36,41,42,6,51,48,24,57],#[45,3,52,44,50,17,22,14,20,47,23,59,7,33,30,10],#[64,66,65,113,68,69,107,124,72,73,127,76,75,85,119,82],#[83,117,79,80,120,77,118,122,110,89,102,98,92,93,126,95],#[96,125,91,99,104,101,90,103,100,105,106,70,115,112,88,121],#[109,67,116,108,114,81,86,78,84,111,87,123,71,97,94,74],#[128,130,129,177,132,133,171,188,136,137,191,140,139,149,183,146],#[147,181,143,144,184,141,182,186,174,153,166,162,156,157,190,159],#[160,189,155,163,168,165,154,167,164,169,170,134,179,176,152,185],#[173,131,180,172,178,145,150,142,148,175,151,187,135,161,158,138]]]

def image (g : Fin 4) (i : Fin 192) : Fin 192 :=
  ((imageTable[g.val]!)[i.val / 16]!)[i.val % 16]!

private def stepBlocks : Array (Array (Array (Fin 192))) := #[
  #[#[1,2,3,64],#[4,5,6,65],#[5,4,7,66],#[8,9,10,67],#[11,12,13,68],#[12,11,14,69],#[15,16,17,70],#[18,19,20,71],#[13,21,22,72],#[21,13,12,73],#[17,23,24,74],#[0,25,26,75],#[25,0,27,76],#[28,29,30,77],#[31,32,33,78],#[26,34,35,79]],
  #[#[34,26,25,80],#[30,36,37,81],#[27,38,39,82],#[38,27,0,83],#[33,10,9,84],#[29,28,40,85],#[41,42,43,86],#[36,30,29,87],#[43,7,4,88],#[2,1,44,89],#[45,46,47,90],#[48,24,23,91],#[3,49,50,92],#[49,3,2,93],#[47,20,19,94],#[44,51,52,95]],
  #[#[51,44,1,96],#[23,17,16,97],#[46,45,53,98],#[22,54,55,99],#[20,47,46,100],#[55,14,11,101],#[24,48,56,102],#[54,22,21,103],#[57,56,48,104],#[50,52,51,105],#[52,50,49,106],#[19,18,58,107],#[59,37,36,108],#[6,60,41,109],#[60,6,5,110],#[10,33,32,111]],
  #[#[7,43,42,112],#[9,8,61,113],#[35,39,38,114],#[37,59,62,115],#[39,35,34,116],#[40,62,59,117],#[42,41,60,118],#[32,31,63,119],#[63,61,8,120],#[61,63,31,121],#[62,40,28,122],#[14,55,54,123],#[16,15,57,124],#[53,58,18,125],#[56,57,15,126],#[58,53,45,127]],
  #[#[126,94,147,128],#[122,111,160,129],#[121,87,157,130],#[109,83,128,131],#[127,74,152,132],#[104,100,174,133],#[72,96,129,134],#[123,93,130,135],#[90,102,184,136],#[124,71,148,137],#[99,64,131,138],#[120,81,165,139],#[117,84,137,140],#[79,88,132,141],#[82,110,133,142],#[67,115,190,143]],
  #[#[85,78,161,144],#[114,65,134,145],#[108,113,189,146],#[119,77,158,147],#[116,66,135,148],#[110,82,167,149],#[81,120,136,150],#[118,76,155,151],#[115,67,138,152],#[125,97,144,153],#[92,101,139,154],#[95,73,140,155],#[70,107,186,156],#[98,91,151,157],#[105,68,141,158],#[71,124,185,159]],
  #[#[102,90,175,160],#[106,69,142,161],#[73,95,180,162],#[94,126,143,163],#[103,89,172,164],#[107,70,145,165],#[101,92,178,166],#[97,125,146,167],#[89,103,149,168],#[74,127,173,169],#[100,104,176,170],#[96,72,150,171],#[112,80,153,172],#[77,119,191,173],#[113,108,164,174],#[86,75,154,175]],
  #[#[78,85,168,176],#[80,112,170,177],#[111,122,156,178],#[83,109,169,179],#[87,121,159,180],#[66,116,162,181],#[84,117,187,182],#[88,79,163,183],#[65,114,166,184],#[76,118,188,185],#[75,86,171,186],#[91,98,181,187],#[93,123,182,188],#[69,106,177,189],#[68,105,179,190],#[64,99,183,191]],
  #[#[186,151,91,0],#[191,164,108,1],#[168,138,67,2],#[154,135,66,3],#[184,148,71,4],#[181,145,70,5],#[131,142,69,6],#[172,141,68,7],#[143,146,125,8],#[174,152,74,9],#[178,140,73,10],#[190,161,78,11],#[189,158,77,12],#[134,155,76,13],#[135,154,75,14],#[156,159,121,15]],
  #[#[137,165,81,16],#[169,153,80,17],#[159,156,122,18],#[165,137,84,19],#[170,128,83,20],#[162,171,86,21],#[138,168,85,22],#[167,132,88,23],#[160,157,87,24],#[185,175,90,25],#[141,172,89,26],#[142,131,64,27],#[173,176,104,28],#[144,147,94,29],#[150,130,93,30],#[176,173,127,31]],
  #[#[147,144,97,32],#[182,129,96,33],#[177,183,99,34],#[145,181,98,35],#[180,139,101,36],#[152,174,100,37],#[179,149,103,38],#[148,184,102,39],#[140,178,92,40],#[175,185,124,41],#[151,186,107,42],#[183,177,106,43],#[155,134,65,44],#[136,187,117,45],#[157,160,111,46],#[163,133,110,47]],
  #[#[187,136,120,48],#[188,166,114,49],#[158,189,113,50],#[171,162,116,51],#[161,190,115,52],#[153,169,109,53],#[164,191,119,54],#[166,188,118,55],#[128,170,112,56],#[133,163,79,57],#[132,167,82,58],#[146,143,126,59],#[149,179,105,60],#[130,150,72,61],#[129,182,123,62],#[139,180,95,63]]]

private def fastStep (i : Fin 192) (j : Fin 4) : Fin 192 :=
  ((stepBlocks[i.val / 16]!)[i.val % 16]!)[j.val]!

private theorem fastStep_eq : ∀ i j, fastStep i j = step i j := by decide +kernel

private def fastWord (i : Fin 192) : List (Fin 4) → Fin 192
  | [] => i
  | j :: w => fastWord (fastStep i j) w

private theorem fastWord_eq (i : Fin 192) (w : List (Fin 4)) :
    fastWord i w = rightWord i w := by
  induction w generalizing i with
  | nil => rfl
  | cons j w ih => rw [fastWord, rightWord, ih, fastStep_eq]

theorem image_zero : ∀ g, image g 0 = 0 := by decide +kernel

private theorem image_four_0 : ∀ i, image 0 (image 0 (image 0 (image 0 i))) = i := by
  decide +kernel

private theorem image_four_1 : ∀ i, image 1 (image 1 (image 1 (image 1 i))) = i := by
  decide +kernel

private theorem image_four_2 : ∀ i, image 2 (image 2 (image 2 (image 2 i))) = i := by
  decide +kernel

private theorem image_four_3 : ∀ i, image 3 (image 3 (image 3 (image 3 i))) = i := by
  decide +kernel

theorem image_four (g : Fin 4) (i : Fin 192) :
    image g (image g (image g (image g i))) = i := by
  fin_cases g
  · exact image_four_0 i
  · exact image_four_1 i
  · exact image_four_2 i
  · exact image_four_3 i

private theorem image_step_0_0 : ∀ i, image 0 (step i 0) =
    rightWord (image 0 i) (words (image 0 (generatorIndex 0))) := by
  have h : ∀ i, image 0 (fastStep i 0) =
      fastWord (image 0 i) (words (image 0 (generatorIndex 0))) := by
    decide +kernel
  simpa only [fastStep_eq, fastWord_eq] using h

private theorem image_step_0_1 : ∀ i, image 0 (step i 1) =
    rightWord (image 0 i) (words (image 0 (generatorIndex 1))) := by
  have h : ∀ i, image 0 (fastStep i 1) =
      fastWord (image 0 i) (words (image 0 (generatorIndex 1))) := by
    decide +kernel
  simpa only [fastStep_eq, fastWord_eq] using h

private theorem image_step_0_2 : ∀ i, image 0 (step i 2) =
    rightWord (image 0 i) (words (image 0 (generatorIndex 2))) := by
  have h : ∀ i, image 0 (fastStep i 2) =
      fastWord (image 0 i) (words (image 0 (generatorIndex 2))) := by
    decide +kernel
  simpa only [fastStep_eq, fastWord_eq] using h

private theorem image_step_0_3 : ∀ i, image 0 (step i 3) =
    rightWord (image 0 i) (words (image 0 (generatorIndex 3))) := by
  have h : ∀ i, image 0 (fastStep i 3) =
      fastWord (image 0 i) (words (image 0 (generatorIndex 3))) := by
    decide +kernel
  simpa only [fastStep_eq, fastWord_eq] using h

private theorem image_step_1_0 : ∀ i, image 1 (step i 0) =
    rightWord (image 1 i) (words (image 1 (generatorIndex 0))) := by
  have h : ∀ i, image 1 (fastStep i 0) =
      fastWord (image 1 i) (words (image 1 (generatorIndex 0))) := by
    decide +kernel
  simpa only [fastStep_eq, fastWord_eq] using h

private theorem image_step_1_1 : ∀ i, image 1 (step i 1) =
    rightWord (image 1 i) (words (image 1 (generatorIndex 1))) := by
  have h : ∀ i, image 1 (fastStep i 1) =
      fastWord (image 1 i) (words (image 1 (generatorIndex 1))) := by
    decide +kernel
  simpa only [fastStep_eq, fastWord_eq] using h

private theorem image_step_1_2 : ∀ i, image 1 (step i 2) =
    rightWord (image 1 i) (words (image 1 (generatorIndex 2))) := by
  have h : ∀ i, image 1 (fastStep i 2) =
      fastWord (image 1 i) (words (image 1 (generatorIndex 2))) := by
    decide +kernel
  simpa only [fastStep_eq, fastWord_eq] using h

private theorem image_step_1_3 : ∀ i, image 1 (step i 3) =
    rightWord (image 1 i) (words (image 1 (generatorIndex 3))) := by
  have h : ∀ i, image 1 (fastStep i 3) =
      fastWord (image 1 i) (words (image 1 (generatorIndex 3))) := by
    decide +kernel
  simpa only [fastStep_eq, fastWord_eq] using h

private theorem image_step_2_0 : ∀ i, image 2 (step i 0) =
    rightWord (image 2 i) (words (image 2 (generatorIndex 0))) := by
  have h : ∀ i, image 2 (fastStep i 0) =
      fastWord (image 2 i) (words (image 2 (generatorIndex 0))) := by
    decide +kernel
  simpa only [fastStep_eq, fastWord_eq] using h

private theorem image_step_2_1 : ∀ i, image 2 (step i 1) =
    rightWord (image 2 i) (words (image 2 (generatorIndex 1))) := by
  have h : ∀ i, image 2 (fastStep i 1) =
      fastWord (image 2 i) (words (image 2 (generatorIndex 1))) := by
    decide +kernel
  simpa only [fastStep_eq, fastWord_eq] using h

private theorem image_step_2_2 : ∀ i, image 2 (step i 2) =
    rightWord (image 2 i) (words (image 2 (generatorIndex 2))) := by
  have h : ∀ i, image 2 (fastStep i 2) =
      fastWord (image 2 i) (words (image 2 (generatorIndex 2))) := by
    decide +kernel
  simpa only [fastStep_eq, fastWord_eq] using h

private theorem image_step_2_3 : ∀ i, image 2 (step i 3) =
    rightWord (image 2 i) (words (image 2 (generatorIndex 3))) := by
  have h : ∀ i, image 2 (fastStep i 3) =
      fastWord (image 2 i) (words (image 2 (generatorIndex 3))) := by
    decide +kernel
  simpa only [fastStep_eq, fastWord_eq] using h

private theorem image_step_3_0 : ∀ i, image 3 (step i 0) =
    rightWord (image 3 i) (words (image 3 (generatorIndex 0))) := by
  have h : ∀ i, image 3 (fastStep i 0) =
      fastWord (image 3 i) (words (image 3 (generatorIndex 0))) := by
    decide +kernel
  simpa only [fastStep_eq, fastWord_eq] using h

private theorem image_step_3_1 : ∀ i, image 3 (step i 1) =
    rightWord (image 3 i) (words (image 3 (generatorIndex 1))) := by
  have h : ∀ i, image 3 (fastStep i 1) =
      fastWord (image 3 i) (words (image 3 (generatorIndex 1))) := by
    decide +kernel
  simpa only [fastStep_eq, fastWord_eq] using h

private theorem image_step_3_2 : ∀ i, image 3 (step i 2) =
    rightWord (image 3 i) (words (image 3 (generatorIndex 2))) := by
  have h : ∀ i, image 3 (fastStep i 2) =
      fastWord (image 3 i) (words (image 3 (generatorIndex 2))) := by
    decide +kernel
  simpa only [fastStep_eq, fastWord_eq] using h

private theorem image_step_3_3 : ∀ i, image 3 (step i 3) =
    rightWord (image 3 i) (words (image 3 (generatorIndex 3))) := by
  have h : ∀ i, image 3 (fastStep i 3) =
      fastWord (image 3 i) (words (image 3 (generatorIndex 3))) := by
    decide +kernel
  simpa only [fastStep_eq, fastWord_eq] using h

theorem image_step (g : Fin 4) (i : Fin 192) (j : Fin 4) : image g (step i j) =
    rightWord (image g i) (words (image g (generatorIndex j))) := by
  fin_cases g <;> fin_cases j
  · exact image_step_0_0 i
  · exact image_step_0_1 i
  · exact image_step_0_2 i
  · exact image_step_0_3 i
  · exact image_step_1_0 i
  · exact image_step_1_1 i
  · exact image_step_1_2 i
  · exact image_step_1_3 i
  · exact image_step_2_0 i
  · exact image_step_2_1 i
  · exact image_step_2_2 i
  · exact image_step_2_3 i
  · exact image_step_3_0 i
  · exact image_step_3_1 i
  · exact image_step_3_2 i
  · exact image_step_3_3 i

end Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics.EightExtensions
