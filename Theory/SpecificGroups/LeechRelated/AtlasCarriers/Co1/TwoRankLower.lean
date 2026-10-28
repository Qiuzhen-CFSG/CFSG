module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co1.CentralizerSection.Words
public import Theory.GroupTheory.PrimeRankWitness
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# An elementary eight in the actual Conway Co₁ carrier

Three concrete binary matrices come from the already certified centralizer
words. One is the central involution, a second is x, and the third is a
conjugate of x. Packed multiplication checks prove their squares and
commutation; their first rows distinguish all eight products.
Source: ATLAS Co1G1-max5W1; Aschbacher–Smith A.2.12, printed p.36.
-/
public noncomputable section
namespace Sporadic.LeechRelated.Co1.TwoRank
open CentralizerSection CentralizerSection.Packed
private abbrev Rows := Fin 24 → ℕ
private theorem product_witness {a b c : Rows}
    (ha : ∃ g : Carrier, g.val.val = decode a)
    (hb : ∃ g : Carrier, g.val.val = decode b)
    (h : product a b = c) : ∃ g : Carrier, g.val.val = decode c := by
  obtain ⟨g, hg⟩ := ha
  obtain ⟨f, hf⟩ := hb
  refine ⟨g * f, ?_⟩
  change g.val.val * f.val.val = decode c
  rw [hg, hf]
  exact mul_eq_of_certificate _ _ _ h
private def rows0 : Rows := Matrices.step05Rows
private def rows1 : Rows := Matrices.step12Rows
private def rows2 : Rows := Matrices.zRows
private theorem witness0 : ∃ g : Carrier, g.val.val = decode rows0 := ⟨x, x_matrix⟩
private theorem witness1 : ∃ g : Carrier, g.val.val = decode rows1 := ⟨y, y_matrix⟩
private theorem witness2 : ∃ g : Carrier, g.val.val = decode rows2 := ⟨z, z_matrix⟩

private def rows3 : Rows :=
  ![1000997, 2591101, 577019, 6303001, 6080747, 2774185, 10795057, 2206750, 3902981, 14125077, 4682292, 15009058, 15186069, 1813092, 6147404, 214046, 14686864, 5166039, 1887982, 15601763, 1701804, 11899389, 8487783, 7816246]
private theorem witness3 : ∃ g : Carrier, g.val.val = decode rows3 :=
  product_witness witness1 witness1 (by decide +kernel)

private def rows4 : Rows :=
  ![6515429, 8457148, 4845048, 13510303, 5376230, 7694960, 12384284, 2579054, 3364093, 12489776, 7598275, 15927497, 16652166, 7759930, 3091106, 2333091, 15101457, 15492276, 1981714, 15691281, 9491555, 2704386, 15668562, 7460311]
private theorem witness4 : ∃ g : Carrier, g.val.val = decode rows4 :=
  product_witness witness3 witness1 (by decide +kernel)

private def rows5 : Rows :=
  ![1886859, 7241821, 6128869, 2622285, 4621066, 2200283, 10162496, 7241951, 4798021, 6057585, 10584064, 15252608, 14023921, 6740337, 3855045, 9358833, 1282432, 2470111, 6632389, 1741184, 4957893, 16618975, 10327519, 6344110]
private theorem witness5 : ∃ g : Carrier, g.val.val = decode rows5 :=
  product_witness witness4 witness4 (by decide +kernel)

private def rows6 : Rows :=
  ![2864432, 15904316, 16570972, 1291072, 16529593, 4840788, 7724647, 5570542, 3502364, 1133823, 10315367, 5549805, 3004755, 16646186, 4689692, 808855, 5463664, 14086580, 9082957, 5922416, 2343395, 83783, 13047319, 2997859]
private theorem witness6 : ∃ g : Carrier, g.val.val = decode rows6 :=
  product_witness witness5 witness4 (by decide +kernel)

private def rows7 : Rows :=
  ![32325, 6758158, 11752261, 54821, 8991550, 6290529, 11735479, 8944025, 16698270, 11923633, 263349, 2182429, 1069186, 9133207, 4889055, 12499238, 2822949, 8111557, 1401053, 2431446, 16371763, 9574762, 5195780, 9166796]
private theorem witness7 : ∃ g : Carrier, g.val.val = decode rows7 :=
  product_witness witness6 witness3 (by decide +kernel)

private def rows8 : Rows :=
  ![348454, 4835981, 2973775, 5578976, 324779, 7317967, 8080605, 5216105, 9764064, 3253354, 5165252, 4441789, 1129445, 10314994, 8113527, 16065289, 2630457, 8575244, 6661278, 6326730, 4491131, 12225112, 2945877, 3368549]
private theorem witness8 : ∃ g : Carrier, g.val.val = decode rows8 :=
  product_witness witness1 witness0 (by decide +kernel)

private def rows9 : Rows :=
  ![12725335, 9672166, 5337488, 1198954, 14078702, 9585086, 11446249, 11908524, 13917662, 1062545, 946682, 8559080, 8633179, 4641545, 6344009, 8028589, 13065485, 15766489, 7090917, 16537019, 6617813, 2511340, 821566, 14301813]
private theorem witness9 : ∃ g : Carrier, g.val.val = decode rows9 :=
  product_witness witness8 witness5 (by decide +kernel)

private def rows10 : Rows :=
  ![12831434, 15206291, 7726129, 7249818, 15805782, 8014822, 11302185, 4515918, 6695420, 15809903, 15599092, 14246660, 12433019, 11708673, 7980215, 6789248, 2753593, 14074421, 2129330, 2897394, 9149642, 2511340, 611762, 1273741]
private theorem witness10 : ∃ g : Carrier, g.val.val = decode rows10 :=
  product_witness witness9 witness0 (by decide +kernel)

private def rows11 : Rows :=
  ![92809, 3270985, 14939579, 3256238, 2288774, 2245494, 9836028, 12764021, 12138363, 5690860, 2046482, 10124107, 927492, 13821514, 9138856, 14400101, 13865096, 4427770, 12357295, 2951131, 1919005, 5273368, 1682014, 876405]
private theorem witness11 : ∃ g : Carrier, g.val.val = decode rows11 :=
  product_witness witness10 witness4 (by decide +kernel)

private def rows12 : Rows :=
  ![3376844, 15616693, 7477876, 3617785, 10844845, 1672279, 5813550, 9484255, 12190502, 5397586, 15380490, 5549855, 2631852, 10671071, 14947773, 7842814, 14567124, 3906173, 11140953, 10880019, 6887901, 12436423, 2385989, 7947900]
private theorem witness12 : ∃ g : Carrier, g.val.val = decode rows12 :=
  product_witness witness11 witness0 (by decide +kernel)

private def rows13 : Rows :=
  ![4623385, 2463314, 5912295, 10817544, 5501767, 12035626, 15010187, 11943413, 16697443, 8113742, 2852415, 13512043, 12273789, 14877578, 11681778, 1251466, 740142, 5408157, 12332192, 6411435, 15594317, 2423291, 12492406, 4228863]
private theorem witness13 : ∃ g : Carrier, g.val.val = decode rows13 :=
  product_witness witness12 witness1 (by decide +kernel)

private def rows14 : Rows :=
  ![2911956, 8393162, 12171034, 25994, 7595006, 13719459, 2900541, 10492880, 9235426, 2284909, 6291033, 14117429, 7992708, 1640677, 13359978, 12752560, 13150224, 14913166, 8299700, 10659135, 8285402, 10360292, 9022159, 6301408]
private theorem witness14 : ∃ g : Carrier, g.val.val = decode rows14 :=
  product_witness witness7 witness0 (by decide +kernel)

private def rows15 : Rows :=
  ![9521493, 16067289, 8243304, 10779359, 7919985, 9241498, 16153432, 11315785, 10641680, 11915682, 4250404, 5814715, 7644040, 12713151, 16700761, 7399327, 15349741, 15969243, 9524927, 2351019, 11527370, 1679520, 8673365, 14452543]
private theorem witness15 : ∃ g : Carrier, g.val.val = decode rows15 :=
  product_witness witness14 witness6 (by decide +kernel)

private def rows16 : Rows :=
  ![5814671, 16339665, 4091464, 458179, 7625247, 496201, 8343862, 1516715, 14186483, 10738880, 5531277, 12298156, 6104924, 10442047, 5509212, 10195283, 10754517, 4298544, 15278387, 7380024, 9503745, 1964218, 3462261, 1659305]
private theorem witness16 : ∃ g : Carrier, g.val.val = decode rows16 :=
  product_witness witness15 witness0 (by decide +kernel)

private def rows17 : Rows :=
  ![3771791, 6222640, 1469128, 12609570, 5515185, 16487789, 9447623, 13285041, 7441117, 7747572, 1386726, 10229619, 12588152, 371887, 13560268, 12190829, 8274299, 457914, 3373469, 7780825, 8761440, 8847658, 11415013, 10446198]
private theorem witness17 : ∃ g : Carrier, g.val.val = decode rows17 :=
  product_witness witness16 witness5 (by decide +kernel)

private def rows18 : Rows :=
  ![326715, 10265610, 7122319, 5783906, 4230293, 10886717, 5490468, 16187436, 7939375, 13061060, 11643584, 11793558, 13241153, 15785425, 13628471, 20573, 4068399, 10035408, 4552061, 12068164, 11455670, 2654670, 11893051, 12959278]
private theorem witness18 : ∃ g : Carrier, g.val.val = decode rows18 :=
  product_witness witness17 witness0 (by decide +kernel)

private def rows19 : Rows :=
  ![15629736, 1335003, 6279760, 11280760, 6741805, 9616991, 11665040, 430509, 13631576, 2749811, 5322115, 978624, 4411931, 2263433, 13495595, 13832433, 12532202, 4522635, 9192656, 11853325, 649652, 1605700, 6360597, 12881429]
private theorem witness19 : ∃ g : Carrier, g.val.val = decode rows19 :=
  product_witness witness18 witness7 (by decide +kernel)

private def rows20 : Rows :=
  ![9514666, 13000701, 10610981, 7297014, 8751603, 8891810, 5014846, 3469832, 866733, 3893026, 15370030, 7825756, 13752269, 11462150, 10459521, 7877481, 3999691, 9631203, 6086655, 8196760, 8088810, 13063998, 13130351, 12531362]
private theorem witness20 : ∃ g : Carrier, g.val.val = decode rows20 :=
  product_witness witness19 witness0 (by decide +kernel)

private def rows21 : Rows :=
  ![5916041, 7839911, 11987204, 7431950, 26539, 6951254, 10212731, 5412063, 404723, 10263740, 3751499, 12219264, 4641141, 8834724, 4278041, 8011265, 2361276, 5528291, 14617339, 2195308, 10423802, 8579287, 15584141, 2209018]
private theorem witness21 : ∃ g : Carrier, g.val.val = decode rows21 :=
  product_witness witness20 witness13 (by decide +kernel)

private def generatorRows : Fin 3 → Rows := ![rows2, rows0, rows21]
private theorem exists_generators (i : Fin 3) :
    ∃ g : Carrier, g.val.val = decode (generatorRows i) := by
  fin_cases i
  · exact witness2
  · exact witness0
  · exact witness21

private def representation : Carrier →* Matrix (Fin 24) (Fin 24) (ZMod 2) where
  toFun g := g.val.val
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem representation_injective : Function.Injective representation := by
  intro a b h
  exact Subtype.ext (Units.ext h)

private def generators (i : Fin 3) : Carrier := (exists_generators i).choose

private theorem representation_generators (i : Fin 3) :
    representation (generators i) = decode (generatorRows i) :=
  (exists_generators i).choose_spec

private theorem square_certificate : ∀ i : Fin 3,
    product (generatorRows i) (generatorRows i) = Matrices.identityRows 24 := by decide +kernel
private theorem commute_certificate : ∀ i j : Fin 3,
    product (generatorRows i) (generatorRows j) =
      product (generatorRows j) (generatorRows i) := by decide +kernel
private theorem generators_square (i : Fin 3) : generators i ^ 2 = 1 := by
  apply representation_injective
  rw [map_pow, map_one, representation_generators, pow_two]
  rw [mul_eq_of_certificate _ _ _ (square_certificate i), Matrices.decode_identity]

private theorem generators_commute (i j : Fin 3) : Commute (generators i) (generators j) := by
  apply representation_injective
  simp only [map_mul, representation_generators, ← decode_product]
  exact congrArg decode (commute_certificate i j)

private def cycle (i : Fin 3) : Multiplicative (ZMod 2) →* Carrier where
  toFun a := generators i ^ a.toAdd.val
  map_one' := pow_zero _
  map_mul' a b := by
    change generators i ^ (a.toAdd + b.toAdd).val = _
    rw [ZMod.val_add, ← pow_add]
    exact pow_eq_pow_of_modEq (Nat.mod_mod _ _) (generators_square i)

private theorem cycles_commute : Pairwise (fun (i j : Fin 3) =>
    ∀ (a b : Multiplicative (ZMod 2)), Commute (cycle i a) (cycle j b)) := by
  intro i j _ a b
  change Commute (generators i ^ a.toAdd.val) (generators j ^ b.toAdd.val)
  exact @Commute.pow_pow Carrier (inferInstance : Monoid Carrier)
    (generators i) (generators j) (generators_commute i j) a.toAdd.val b.toAdd.val

/-- An actual elementary abelian subgroup of the actual Co₁ carrier. -/
def embedding : (Fin 3 → Multiplicative (ZMod 2)) →* Carrier :=
  MonoidHom.noncommPiCoprod cycle cycles_commute

private theorem embedding_apply (a : Fin 3 → Multiplicative (ZMod 2)) :
    embedding a = generators 0 ^ (a 0).toAdd.val *
      (generators 1 ^ (a 1).toAdd.val * generators 2 ^ (a 2).toAdd.val) := by
  rw [embedding, MonoidHom.noncommPiCoprod_apply]
  have h : (Finset.univ : Finset (Fin 3)) = [0, 1, 2].toFinset := by decide
  rw [h, Finset.noncommProd_toFinset _ _ _ (by decide)]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rfl

private def powerRows (i : Fin 3) (a : ZMod 2) : Rows :=
  if a = 0 then Matrices.identityRows 24 else generatorRows i

private theorem representation_cycle (i : Fin 3) (a : Multiplicative (ZMod 2)) :
    representation (cycle i a) = decode (powerRows i a.toAdd) := by
  change representation (generators i ^ a.toAdd.val) = _
  rw [map_pow, representation_generators]
  generalize a.toAdd = ha
  fin_cases ha
  · exact (Matrices.decode_identity 24).symm
  · exact pow_one _
private def wordRows (a b c : ZMod 2) : Rows :=
  product (powerRows 0 a) (product (powerRows 1 b) (powerRows 2 c))

-- The first row already separates the identity from the other seven products.
private theorem wordRows_kernel : ∀ a b c : ZMod 2,
    (∀ j : Fin 24, (decode (wordRows a b c) : Matrix (Fin 24) (Fin 24) (ZMod 2)) 0 j =
      (1 : Matrix (Fin 24) (Fin 24) (ZMod 2)) 0 j) → a = 0 ∧ b = 0 ∧ c = 0 := by
  decide +kernel

private theorem representation_embedding (a : Fin 3 → Multiplicative (ZMod 2)) :
    representation (embedding a) = decode (wordRows (a 0).toAdd (a 1).toAdd (a 2).toAdd) := by
  rw [embedding_apply]
  change representation (cycle 0 (a 0) * (cycle 1 (a 1) * cycle 2 (a 2))) = _
  simp only [map_mul, representation_cycle, wordRows, decode_product]

/-- Independence is checked in the faithful 24-dimensional representation. -/
theorem embedding_injective : Function.Injective embedding := by
  apply (injective_iff_map_eq_one embedding).mpr
  intro a ha
  have h := congrArg representation ha
  rw [representation_embedding, map_one] at h
  obtain ⟨h0, h1, h2⟩ := wordRows_kernel _ _ _ (fun j => congrArg (fun m => m 0 j) h)
  funext i
  apply Multiplicative.toAdd.injective
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- The actual Co₁ carrier has two-rank at least three. -/
theorem three_le_twoRank : 3 ≤ primeRank 2 Carrier := by
  apply primeRank_ge_of_elementary_embedding (f := embedding) (hf := embedding_injective)
  · intro a
    funext i
    change Multiplicative.ofAdd (2 • (a i).toAdd) = Multiplicative.ofAdd 0
    exact congrArg Multiplicative.ofAdd (ZModModule.char_nsmul_eq_zero 2 (a i).toAdd)
  · simp [Nat.card_eq_fintype_card]


end Sporadic.LeechRelated.Co1.TwoRank
