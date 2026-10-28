module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Quotients.PureInnerCore.WordCore
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.Factors.Support

/-!
# A 256-element lower bound for the pure Held word core

The eight certified residual words yield 256 binary products. Their images
on the three marked letters 0, 1, 2 distinguish every product. The decoder
is only a proposed finite table; its left-inverse equation is checked by
Lean kernel reduction against the existing certified degree-2058 permutations.
No order, simplicity, or quotient identification of Held is used.

Source: the unchanged ATLAS representation and ResidualRoots.Pair00 words;
GLS3 Table 5.3p, for the pure pair in Aschbacher--Smith 15.3.41--42.
-/

set_option Elab.async false

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.PureCoreCount
open Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry
open Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate
open Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate.Factors
open ResidualRoots.Pair00

def generatorTable : Fin 8 → Equiv.Perm (Fin 2058)
  | 0 => q0
  | 1 => q1
  | 2 => q2
  | 3 => q3
  | 4 => q4
  | 5 => q5
  | 6 => q6
  | 7 => q7

theorem generatorTable_eq (k : Fin 8) :
    generatorTable k = Held.representation (ResidualRoots.generator false 0 k) := by
  fin_cases k
  · exact q0_eq
  · exact q1_eq
  · exact q2_eq
  · exact q3_eq
  · exact q4_eq
  · exact q5_eq
  · exact q6_eq
  · exact q7_eq

def normalForm (v : Fin 256) : Held.He :=
  (List.ofFn (fun k : Fin 8 => ResidualRoots.generator false 0 k ^ (v.val / 2 ^ k.val % 2))).prod

def normalTable (v : Fin 256) : Equiv.Perm (Fin 2058) :=
  (List.ofFn (fun k : Fin 8 => generatorTable k ^ (v.val / 2 ^ k.val % 2))).prod

theorem normalTable_eq (v : Fin 256) : normalTable v = Held.representation (normalForm v) := by
  simp only [normalForm, normalTable, map_list_prod, List.map_ofFn, Function.comp_def,
    map_pow, ← generatorTable_eq]

theorem normalForm_mem (v : Fin 256) : normalForm v ∈ ResidualRoots.group false 0 := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
  exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self k)) _

def decodeCode (x : ℕ) : ℕ :=
  (if x < 4161373271 then (if x < 1630589082 then (if x < 712031802 then (if x < 294486476 then (if x < 222271446 then (if x < 80445383 then (if x < 39868636 then (if x < 2934 then 0 else 64) else (if x < 39868796 then 205 else 143)) else (if x < 209565446 then (if x < 80445477 then 20 else 84) else (if x < 209565466 then 9 else 73))) else (if x < 268860442 then (if x < 232947299 then (if x < 222272204 then 58 else 122) else (if x < 232947464 then 17 else 81)) else (if x < 281918698 then (if x < 268860674 then 59 else 123) else (if x < 281918885 then 75 else 11)))) else (if x < 516688208 then (if x < 434253043 then (if x < 332478827 then (if x < 294487181 then 167 else 229) else (if x < 332479154 then 206 else 140)) else (if x < 488234797 then (if x < 434253434 then 214 else 148) else (if x < 488235737 then 144 else 210))) else (if x < 649706845 then (if x < 531804236 then (if x < 516689605 then 4 else 68) else (if x < 531804823 then 10 else 74)) else (if x < 704766415 then (if x < 649706997 then 152 else 218) else (if x < 704766545 then 200 else 138))))) else (if x < 1382612795 then (if x < 1074898337 then (if x < 927547328 then (if x < 756015169 then (if x < 712032888 then 94 else 30) else (if x < 756015593 then 220 else 158)) else (if x < 947837765 then (if x < 927548713 then 1 else 65) else (if x < 947838377 then 235 else 169))) else (if x < 1172312304 then (if x < 1154140595 then (if x < 1074898556 then 203 else 137) else (if x < 1154140622 then 159 else 221)) else (if x < 1333677606 then (if x < 1172312611 then 234 else 168) else (if x < 1333678418 then 241 else 179)))) else (if x < 1505586072 then (if x < 1423883252 then (if x < 1418498082 then (if x < 1382613556 then 151 else 213) else (if x < 1418498344 then 126 else 62)) else (if x < 1475790486 then (if x < 1423883735 then 87 else 23) else (if x < 1475790765 then 183 else 245))) else (if x < 1585885261 then (if x < 1575528919 then (if x < 1505586555 then 43 else 107) else (if x < 1575529198 then 54 else 118)) else (if x < 1590011232 then (if x < 1585885942 then 3 else 67) else (if x < 1590012172 then 156 else 222)))))) else (if x < 3107872783 then (if x < 2237072976 then (if x < 1884710228 then (if x < 1729778840 then (if x < 1632861113 then (if x < 1630589351 then 103 else 39) else (if x < 1632861638 then 196 else 134)) else (if x < 1766638289 then (if x < 1729779634 then 157 else 223) else (if x < 1766638401 then 14 else 78))) else (if x < 1926206313 then (if x < 1908297966 then (if x < 1884711658 then 5 else 69) else (if x < 1908298377 then 120 else 56)) else (if x < 2119802484 then (if x < 1926207043 then 187 else 249) else (if x < 2119803783 then 190 else 252)))) else (if x < 2591159213 then (if x < 2430214518 then (if x < 2261335122 then (if x < 2237074283 then 116 else 52) else (if x < 2261336076 then 46 else 110)) else (if x < 2463130680 then (if x < 2430215987 then 154 else 216) else (if x < 2463131208 then 40 else 104))) else (if x < 2625463263 then (if x < 2615079454 then (if x < 2591159264 then 155 else 217) else (if x < 2615079491 then 113 else 49)) else (if x < 3100777665 then (if x < 2625463975 then 178 else 240) else (if x < 3100777748 then 61 else 125))))) else (if x < 3775741416 then (if x < 3515003158 then (if x < 3431446104 then (if x < 3241749350 then (if x < 3107874044 then 248 else 186) else (if x < 3241749518 then 201 else 139)) else (if x < 3466773462 then (if x < 3431447095 then 117 else 53) else (if x < 3466774904 then 149 else 215))) else (if x < 3597707230 then (if x < 3593285505 then (if x < 3515003927 then 93 else 29) else (if x < 3593286265 then 170 else 232)) else (if x < 3709830039 then (if x < 3597707811 then 164 else 230) else (if x < 3709830514 then 13 else 77)))) else (if x < 4004664443 then (if x < 3918201853 then (if x < 3894682992 then (if x < 3775742237 then 88 else 24) else (if x < 3894683029 then 105 else 41)) else (if x < 3985968360 then (if x < 3918203453 then 44 else 108) else (if x < 3985968417 then 45 else 109))) else (if x < 4017008694 then (if x < 4014776438 then (if x < 4004666237 then 166 else 228) else (if x < 4014776839 then 28 else 92)) else (if x < 4103184252 then (if x < 4017010131 then 198 else 132) else (if x < 4103184294 then 136 else 202))))))) else (if x < 6494562497 then (if x < 5221740860 then (if x < 4813257596 then (if x < 4563870738 then (if x < 4464564032 then (if x < 4421722361 then (if x < 4161374594 then 181 else 247) else (if x < 4421723440 then 99 else 35)) else (if x < 4481505462 then (if x < 4464564844 then 15 else 79) else (if x < 4481506548 then 31 else 95))) else (if x < 4711583178 then (if x < 4631111770 then (if x < 4563871819 then 26 else 90) else (if x < 4631112919 then 112 else 48)) else (if x < 4720315652 then (if x < 4711583838 then 33 else 97) else (if x < 4720317225 then 207 else 141)))) else (if x < 4931130943 then (if x < 4904201964 then (if x < 4874555263 then (if x < 4813257634 then 133 else 199) else (if x < 4874555468 then 76 else 12)) else (if x < 4923739009 then (if x < 4904203390 then 111 else 47) else (if x < 4923740289 then 180 else 246))) else (if x < 5035849911 then (if x < 4974437200 then (if x < 4931132018 then 145 else 211) else (if x < 4974438863 then 173 else 239)) else (if x < 5071615150 then (if x < 5035851329 then 16 else 80) else (if x < 5071615625 then 212 else 150))))) else (if x < 6011840069 then (if x < 5629966138 then (if x < 5372138395 then (if x < 5286901424 then (if x < 5221742238 then 195 else 129) else (if x < 5286902676 then 130 else 192)) else (if x < 5600901271 then (if x < 5372138850 then 153 else 219) else (if x < 5600901531 then 189 else 255))) else (if x < 5880568428 then (if x < 5791775060 then (if x < 5629967058 then 162 else 224) else (if x < 5791775466 then 25 else 89)) else (if x < 5910191750 then (if x < 5880569230 then 182 else 244) else (if x < 5910193105 then 2 else 66)))) else (if x < 6354742596 then (if x < 6164487604 then (if x < 6143136489 then (if x < 6011841466 then 83 else 19) else (if x < 6143137043 then 82 else 18)) else (if x < 6265987891 then (if x < 6164487815 then 42 else 106) else (if x < 6265988021 then 165 else 231))) else (if x < 6414373377 then (if x < 6401880580 then (if x < 6354743137 then 184 else 250) else (if x < 6401880698 then 135 else 197)) else (if x < 6452842739 then (if x < 6414374151 then 8 else 72) else (if x < 6452844422 then 121 else 57)))))) else (if x < 7510996867 then (if x < 7005294336 then (if x < 6901157961 then (if x < 6818473512 then (if x < 6621570220 then (if x < 6494563907 then 175 else 237) else (if x < 6621571082 then 171 else 233)) else (if x < 6859438378 then (if x < 6818474496 then 147 else 209) else (if x < 6859439412 then 91 else 27))) else (if x < 6950205627 then (if x < 6907881440 then (if x < 6901158338 then 236 else 174) else (if x < 6907881707 then 98 else 34)) else (if x < 6976136198 then (if x < 6950205749 then 21 else 85) else (if x < 6976136342 then 60 else 124)))) else (if x < 7327981757 then (if x < 7066707018 then (if x < 7015512629 then (if x < 7005294383 then 114 else 50) else (if x < 7015513012 then 188 else 254)) else (if x < 7263651583 then (if x < 7066708760 then 191 else 253) else (if x < 7263652020 then 51 else 115))) else (if x < 7439420389 then (if x < 7408819326 then (if x < 7327981858 then 86 else 22) else (if x < 7408819885 then 177 else 243)) else (if x < 7449978791 then (if x < 7439420903 then 172 else 238) else (if x < 7449980014 then 55 else 119))))) else (if x < 7903163836 then (if x < 7648605692 then (if x < 7608572575 then (if x < 7559662203 then (if x < 7510997160 then 185 else 251) else (if x < 7559663075 then 208 else 146)) else (if x < 7632927086 then (if x < 7608574120 then 32 else 96) else (if x < 7632928429 then 7 else 71))) else (if x < 7819282542 then (if x < 7798105973 then (if x < 7648606057 then 227 else 161) else (if x < 7798106143 then 101 else 37)) else (if x < 7852015199 then (if x < 7819283204 then 36 else 100) else (if x < 7852016268 then 127 else 63)))) else (if x < 8404130103 then (if x < 8111889275 then (if x < 8063671787 then (if x < 7903164472 then 38 else 102) else (if x < 8063671807 then 160 else 226)) else (if x < 8251656505 then (if x < 8111889767 then 131 else 193) else (if x < 8251656661 then 242 else 176))) else (if x < 8493654418 then (if x < 8446117129 then (if x < 8404130231 then 163 else 225) else (if x < 8446117254 then 6 else 70)) else (if x < 8529560245 then (if x < 8493654672 then 142 else 204) else (if x < 8529561086 then 194 else 128))))))))

def decode (g : Equiv.Perm (Fin 2058)) : ℕ :=
  decodeCode (((g 0).val * 2058 + (g 1).val) * 2058 + (g 2).val)

abbrev decodePredicate (v : Fin 256) : Prop := decode (normalTable v) = v.val

private theorem decode_block0 :
    checkFin 16 (fun j => decide (decodePredicate (blockIndex 256 16 (by decide) 0 j.val))) = true := by
  decide +kernel

private theorem decode_block1 :
    checkFin 16 (fun j => decide (decodePredicate (blockIndex 256 16 (by decide) 1 j.val))) = true := by
  decide +kernel

private theorem decode_block2 :
    checkFin 16 (fun j => decide (decodePredicate (blockIndex 256 16 (by decide) 2 j.val))) = true := by
  decide +kernel

private theorem decode_block3 :
    checkFin 16 (fun j => decide (decodePredicate (blockIndex 256 16 (by decide) 3 j.val))) = true := by
  decide +kernel

private theorem decode_block4 :
    checkFin 16 (fun j => decide (decodePredicate (blockIndex 256 16 (by decide) 4 j.val))) = true := by
  decide +kernel

private theorem decode_block5 :
    checkFin 16 (fun j => decide (decodePredicate (blockIndex 256 16 (by decide) 5 j.val))) = true := by
  decide +kernel

private theorem decode_block6 :
    checkFin 16 (fun j => decide (decodePredicate (blockIndex 256 16 (by decide) 6 j.val))) = true := by
  decide +kernel

private theorem decode_block7 :
    checkFin 16 (fun j => decide (decodePredicate (blockIndex 256 16 (by decide) 7 j.val))) = true := by
  decide +kernel

private theorem decode_block8 :
    checkFin 16 (fun j => decide (decodePredicate (blockIndex 256 16 (by decide) 8 j.val))) = true := by
  decide +kernel

private theorem decode_block9 :
    checkFin 16 (fun j => decide (decodePredicate (blockIndex 256 16 (by decide) 9 j.val))) = true := by
  decide +kernel

private theorem decode_block10 :
    checkFin 16 (fun j => decide (decodePredicate (blockIndex 256 16 (by decide) 10 j.val))) = true := by
  decide +kernel

private theorem decode_block11 :
    checkFin 16 (fun j => decide (decodePredicate (blockIndex 256 16 (by decide) 11 j.val))) = true := by
  decide +kernel

private theorem decode_block12 :
    checkFin 16 (fun j => decide (decodePredicate (blockIndex 256 16 (by decide) 12 j.val))) = true := by
  decide +kernel

private theorem decode_block13 :
    checkFin 16 (fun j => decide (decodePredicate (blockIndex 256 16 (by decide) 13 j.val))) = true := by
  decide +kernel

private theorem decode_block14 :
    checkFin 16 (fun j => decide (decodePredicate (blockIndex 256 16 (by decide) 14 j.val))) = true := by
  decide +kernel

private theorem decode_block15 :
    checkFin 16 (fun j => decide (decodePredicate (blockIndex 256 16 (by decide) 15 j.val))) = true := by
  decide +kernel

theorem decode_normal (v : Fin 256) : decode (normalTable v) = v.val := by
  apply allBlocks (b := 16) (m := 16) (by decide) (by decide) (by decide) (P := decodePredicate)
  intro k
  fin_cases k
  · exact allFin _ _ decode_block0
  · exact allFin _ _ decode_block1
  · exact allFin _ _ decode_block2
  · exact allFin _ _ decode_block3
  · exact allFin _ _ decode_block4
  · exact allFin _ _ decode_block5
  · exact allFin _ _ decode_block6
  · exact allFin _ _ decode_block7
  · exact allFin _ _ decode_block8
  · exact allFin _ _ decode_block9
  · exact allFin _ _ decode_block10
  · exact allFin _ _ decode_block11
  · exact allFin _ _ decode_block12
  · exact allFin _ _ decode_block13
  · exact allFin _ _ decode_block14
  · exact allFin _ _ decode_block15

theorem wordGroup_card_lower : 256 ≤ Nat.card (ResidualRoots.group false 0) := by
  apply lower_bound _ 256 normalForm (fun x => decode (Held.representation x)) normalForm_mem
  intro v
  rw [← normalTable_eq]
  exact decode_normal v

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.PureCoreCount

namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile

theorem pureWordCore_card_lower : 256 ≤ Nat.card pureWordCore := by
  rw [show Nat.card pureWordCore = Nat.card
      (Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.group false 0) from
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe pureWordGroup_le).toEquiv]
  exact PureCoreCount.wordGroup_card_lower

theorem pure_inner_core_card_lower : 256 ≤ Nat.card (pCore 2 (innerLocal true)) :=
  pureWordCore_card_lower.trans (Subgroup.card_le_of_le pureWordCore_le_pCore)

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile
