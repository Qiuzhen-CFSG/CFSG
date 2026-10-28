module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.PointParabolic.MathieuOverlap.Words3
/-!
# Certified words for the max4 point-parabolic Mathieu intersection

These are literal words in the ATLAS max4 outputs, evaluated in the existing
28-dimensional restriction and the actual S₅ × SL₃(2) quotient. The faithful
combination detects equality in the native subgroup. Packed multiplication
identities are checked by the Lean kernel.

Source: ATLAS J4G1-max4W1 and J4G1-f2r112B0, with attribution in Model.Data
and SymmetricLinear.Model; Aschbacher–Smith 12.5.3–4, printed pp.818–819.
-/

public noncomputable section
namespace Janko4.LocalStructure.SymmetricLinear
open Subgroup CharacteristicTwo SylowTwoPart SylowTwoPart.KernelCardinality
namespace MathieuOverlap
@[expose] def elementaryGenerator : Fin 11 → max4Subgroup :=
  ![g082, g110, g121, g015, g125, g147, g153, g157, g019, g018, g017]

@[expose] def elementary : Subgroup max4Subgroup := Subgroup.closure (Set.range elementaryGenerator)

lemma generator_square_0 : elementaryGenerator 0 * elementaryGenerator 0 = 1 :=
  eq_of_small_and_quotient g178 g000
    (image_g178.trans image_g000.symm) (quotient_g178.trans quotient_g000.symm)

lemma generator_square_1 : elementaryGenerator 1 * elementaryGenerator 1 = 1 :=
  eq_of_small_and_quotient g179 g000
    (image_g179.trans image_g000.symm) (quotient_g179.trans quotient_g000.symm)

lemma generator_square_2 : elementaryGenerator 2 * elementaryGenerator 2 = 1 :=
  eq_of_small_and_quotient g180 g000
    (image_g180.trans image_g000.symm) (quotient_g180.trans quotient_g000.symm)

lemma generator_square_3 : elementaryGenerator 3 * elementaryGenerator 3 = 1 :=
  eq_of_small_and_quotient g181 g000
    (image_g181.trans image_g000.symm) (quotient_g181.trans quotient_g000.symm)

lemma generator_square_4 : elementaryGenerator 4 * elementaryGenerator 4 = 1 :=
  eq_of_small_and_quotient g182 g000
    (image_g182.trans image_g000.symm) (quotient_g182.trans quotient_g000.symm)

lemma generator_square_5 : elementaryGenerator 5 * elementaryGenerator 5 = 1 :=
  eq_of_small_and_quotient g183 g000
    (image_g183.trans image_g000.symm) (quotient_g183.trans quotient_g000.symm)

lemma generator_square_6 : elementaryGenerator 6 * elementaryGenerator 6 = 1 :=
  eq_of_small_and_quotient g184 g000
    (image_g184.trans image_g000.symm) (quotient_g184.trans quotient_g000.symm)

lemma generator_square_7 : elementaryGenerator 7 * elementaryGenerator 7 = 1 :=
  eq_of_small_and_quotient g185 g000
    (image_g185.trans image_g000.symm) (quotient_g185.trans quotient_g000.symm)

lemma generator_square_8 : elementaryGenerator 8 * elementaryGenerator 8 = 1 :=
  eq_of_small_and_quotient g186 g000
    (image_g186.trans image_g000.symm) (quotient_g186.trans quotient_g000.symm)

lemma generator_square_9 : elementaryGenerator 9 * elementaryGenerator 9 = 1 :=
  eq_of_small_and_quotient g187 g000
    (image_g187.trans image_g000.symm) (quotient_g187.trans quotient_g000.symm)

lemma generator_square_10 : elementaryGenerator 10 * elementaryGenerator 10 = 1 :=
  eq_of_small_and_quotient g188 g000
    (image_g188.trans image_g000.symm) (quotient_g188.trans quotient_g000.symm)

lemma generator_comm_0_1 : elementaryGenerator 0 * elementaryGenerator 1 = elementaryGenerator 1 * elementaryGenerator 0 :=
  eq_of_small_and_quotient g189 g190
    (image_g189.trans image_g190.symm) (quotient_g189.trans quotient_g190.symm)

lemma generator_comm_0_2 : elementaryGenerator 0 * elementaryGenerator 2 = elementaryGenerator 2 * elementaryGenerator 0 :=
  eq_of_small_and_quotient g191 g192
    (image_g191.trans image_g192.symm) (quotient_g191.trans quotient_g192.symm)

lemma generator_comm_0_3 : elementaryGenerator 0 * elementaryGenerator 3 = elementaryGenerator 3 * elementaryGenerator 0 :=
  eq_of_small_and_quotient g193 g194
    (image_g193.trans image_g194.symm) (quotient_g193.trans quotient_g194.symm)

lemma generator_comm_0_4 : elementaryGenerator 0 * elementaryGenerator 4 = elementaryGenerator 4 * elementaryGenerator 0 :=
  eq_of_small_and_quotient g195 g196
    (image_g195.trans image_g196.symm) (quotient_g195.trans quotient_g196.symm)

lemma generator_comm_0_5 : elementaryGenerator 0 * elementaryGenerator 5 = elementaryGenerator 5 * elementaryGenerator 0 :=
  eq_of_small_and_quotient g197 g198
    (image_g197.trans image_g198.symm) (quotient_g197.trans quotient_g198.symm)

lemma generator_comm_0_6 : elementaryGenerator 0 * elementaryGenerator 6 = elementaryGenerator 6 * elementaryGenerator 0 :=
  eq_of_small_and_quotient g199 g200
    (image_g199.trans image_g200.symm) (quotient_g199.trans quotient_g200.symm)

lemma generator_comm_0_7 : elementaryGenerator 0 * elementaryGenerator 7 = elementaryGenerator 7 * elementaryGenerator 0 :=
  eq_of_small_and_quotient g201 g202
    (image_g201.trans image_g202.symm) (quotient_g201.trans quotient_g202.symm)

lemma generator_comm_0_8 : elementaryGenerator 0 * elementaryGenerator 8 = elementaryGenerator 8 * elementaryGenerator 0 :=
  eq_of_small_and_quotient g203 g204
    (image_g203.trans image_g204.symm) (quotient_g203.trans quotient_g204.symm)

lemma generator_comm_0_9 : elementaryGenerator 0 * elementaryGenerator 9 = elementaryGenerator 9 * elementaryGenerator 0 :=
  eq_of_small_and_quotient g205 g206
    (image_g205.trans image_g206.symm) (quotient_g205.trans quotient_g206.symm)

lemma generator_comm_0_10 : elementaryGenerator 0 * elementaryGenerator 10 = elementaryGenerator 10 * elementaryGenerator 0 :=
  eq_of_small_and_quotient g207 g208
    (image_g207.trans image_g208.symm) (quotient_g207.trans quotient_g208.symm)

lemma generator_comm_1_2 : elementaryGenerator 1 * elementaryGenerator 2 = elementaryGenerator 2 * elementaryGenerator 1 :=
  eq_of_small_and_quotient g209 g210
    (image_g209.trans image_g210.symm) (quotient_g209.trans quotient_g210.symm)

lemma generator_comm_1_3 : elementaryGenerator 1 * elementaryGenerator 3 = elementaryGenerator 3 * elementaryGenerator 1 :=
  eq_of_small_and_quotient g211 g212
    (image_g211.trans image_g212.symm) (quotient_g211.trans quotient_g212.symm)

lemma generator_comm_1_4 : elementaryGenerator 1 * elementaryGenerator 4 = elementaryGenerator 4 * elementaryGenerator 1 :=
  eq_of_small_and_quotient g213 g214
    (image_g213.trans image_g214.symm) (quotient_g213.trans quotient_g214.symm)

lemma generator_comm_1_5 : elementaryGenerator 1 * elementaryGenerator 5 = elementaryGenerator 5 * elementaryGenerator 1 :=
  eq_of_small_and_quotient g215 g216
    (image_g215.trans image_g216.symm) (quotient_g215.trans quotient_g216.symm)

lemma generator_comm_1_6 : elementaryGenerator 1 * elementaryGenerator 6 = elementaryGenerator 6 * elementaryGenerator 1 :=
  eq_of_small_and_quotient g217 g218
    (image_g217.trans image_g218.symm) (quotient_g217.trans quotient_g218.symm)

lemma generator_comm_1_7 : elementaryGenerator 1 * elementaryGenerator 7 = elementaryGenerator 7 * elementaryGenerator 1 :=
  eq_of_small_and_quotient g219 g220
    (image_g219.trans image_g220.symm) (quotient_g219.trans quotient_g220.symm)

lemma generator_comm_1_8 : elementaryGenerator 1 * elementaryGenerator 8 = elementaryGenerator 8 * elementaryGenerator 1 :=
  eq_of_small_and_quotient g221 g222
    (image_g221.trans image_g222.symm) (quotient_g221.trans quotient_g222.symm)

lemma generator_comm_1_9 : elementaryGenerator 1 * elementaryGenerator 9 = elementaryGenerator 9 * elementaryGenerator 1 :=
  eq_of_small_and_quotient g223 g224
    (image_g223.trans image_g224.symm) (quotient_g223.trans quotient_g224.symm)

lemma generator_comm_1_10 : elementaryGenerator 1 * elementaryGenerator 10 = elementaryGenerator 10 * elementaryGenerator 1 :=
  eq_of_small_and_quotient g225 g226
    (image_g225.trans image_g226.symm) (quotient_g225.trans quotient_g226.symm)

lemma generator_comm_2_3 : elementaryGenerator 2 * elementaryGenerator 3 = elementaryGenerator 3 * elementaryGenerator 2 :=
  eq_of_small_and_quotient g227 g228
    (image_g227.trans image_g228.symm) (quotient_g227.trans quotient_g228.symm)

lemma generator_comm_2_4 : elementaryGenerator 2 * elementaryGenerator 4 = elementaryGenerator 4 * elementaryGenerator 2 :=
  eq_of_small_and_quotient g229 g230
    (image_g229.trans image_g230.symm) (quotient_g229.trans quotient_g230.symm)

lemma generator_comm_2_5 : elementaryGenerator 2 * elementaryGenerator 5 = elementaryGenerator 5 * elementaryGenerator 2 :=
  eq_of_small_and_quotient g231 g232
    (image_g231.trans image_g232.symm) (quotient_g231.trans quotient_g232.symm)

lemma generator_comm_2_6 : elementaryGenerator 2 * elementaryGenerator 6 = elementaryGenerator 6 * elementaryGenerator 2 :=
  eq_of_small_and_quotient g233 g234
    (image_g233.trans image_g234.symm) (quotient_g233.trans quotient_g234.symm)

lemma generator_comm_2_7 : elementaryGenerator 2 * elementaryGenerator 7 = elementaryGenerator 7 * elementaryGenerator 2 :=
  eq_of_small_and_quotient g235 g236
    (image_g235.trans image_g236.symm) (quotient_g235.trans quotient_g236.symm)

lemma generator_comm_2_8 : elementaryGenerator 2 * elementaryGenerator 8 = elementaryGenerator 8 * elementaryGenerator 2 :=
  eq_of_small_and_quotient g237 g238
    (image_g237.trans image_g238.symm) (quotient_g237.trans quotient_g238.symm)

lemma generator_comm_2_9 : elementaryGenerator 2 * elementaryGenerator 9 = elementaryGenerator 9 * elementaryGenerator 2 :=
  eq_of_small_and_quotient g239 g240
    (image_g239.trans image_g240.symm) (quotient_g239.trans quotient_g240.symm)

lemma generator_comm_2_10 : elementaryGenerator 2 * elementaryGenerator 10 = elementaryGenerator 10 * elementaryGenerator 2 :=
  eq_of_small_and_quotient g241 g242
    (image_g241.trans image_g242.symm) (quotient_g241.trans quotient_g242.symm)

lemma generator_comm_3_4 : elementaryGenerator 3 * elementaryGenerator 4 = elementaryGenerator 4 * elementaryGenerator 3 :=
  eq_of_small_and_quotient g243 g244
    (image_g243.trans image_g244.symm) (quotient_g243.trans quotient_g244.symm)

lemma generator_comm_3_5 : elementaryGenerator 3 * elementaryGenerator 5 = elementaryGenerator 5 * elementaryGenerator 3 :=
  eq_of_small_and_quotient g245 g246
    (image_g245.trans image_g246.symm) (quotient_g245.trans quotient_g246.symm)

lemma generator_comm_3_6 : elementaryGenerator 3 * elementaryGenerator 6 = elementaryGenerator 6 * elementaryGenerator 3 :=
  eq_of_small_and_quotient g247 g248
    (image_g247.trans image_g248.symm) (quotient_g247.trans quotient_g248.symm)

lemma generator_comm_3_7 : elementaryGenerator 3 * elementaryGenerator 7 = elementaryGenerator 7 * elementaryGenerator 3 :=
  eq_of_small_and_quotient g249 g250
    (image_g249.trans image_g250.symm) (quotient_g249.trans quotient_g250.symm)

lemma generator_comm_3_8 : elementaryGenerator 3 * elementaryGenerator 8 = elementaryGenerator 8 * elementaryGenerator 3 :=
  eq_of_small_and_quotient g251 g252
    (image_g251.trans image_g252.symm) (quotient_g251.trans quotient_g252.symm)

lemma generator_comm_3_9 : elementaryGenerator 3 * elementaryGenerator 9 = elementaryGenerator 9 * elementaryGenerator 3 :=
  eq_of_small_and_quotient g253 g254
    (image_g253.trans image_g254.symm) (quotient_g253.trans quotient_g254.symm)

lemma generator_comm_3_10 : elementaryGenerator 3 * elementaryGenerator 10 = elementaryGenerator 10 * elementaryGenerator 3 :=
  eq_of_small_and_quotient g255 g256
    (image_g255.trans image_g256.symm) (quotient_g255.trans quotient_g256.symm)

lemma generator_comm_4_5 : elementaryGenerator 4 * elementaryGenerator 5 = elementaryGenerator 5 * elementaryGenerator 4 :=
  eq_of_small_and_quotient g257 g258
    (image_g257.trans image_g258.symm) (quotient_g257.trans quotient_g258.symm)

lemma generator_comm_4_6 : elementaryGenerator 4 * elementaryGenerator 6 = elementaryGenerator 6 * elementaryGenerator 4 :=
  eq_of_small_and_quotient g259 g260
    (image_g259.trans image_g260.symm) (quotient_g259.trans quotient_g260.symm)

lemma generator_comm_4_7 : elementaryGenerator 4 * elementaryGenerator 7 = elementaryGenerator 7 * elementaryGenerator 4 :=
  eq_of_small_and_quotient g261 g262
    (image_g261.trans image_g262.symm) (quotient_g261.trans quotient_g262.symm)

lemma generator_comm_4_8 : elementaryGenerator 4 * elementaryGenerator 8 = elementaryGenerator 8 * elementaryGenerator 4 :=
  eq_of_small_and_quotient g263 g264
    (image_g263.trans image_g264.symm) (quotient_g263.trans quotient_g264.symm)

lemma generator_comm_4_9 : elementaryGenerator 4 * elementaryGenerator 9 = elementaryGenerator 9 * elementaryGenerator 4 :=
  eq_of_small_and_quotient g265 g266
    (image_g265.trans image_g266.symm) (quotient_g265.trans quotient_g266.symm)

lemma generator_comm_4_10 : elementaryGenerator 4 * elementaryGenerator 10 = elementaryGenerator 10 * elementaryGenerator 4 :=
  eq_of_small_and_quotient g267 g268
    (image_g267.trans image_g268.symm) (quotient_g267.trans quotient_g268.symm)

lemma generator_comm_5_6 : elementaryGenerator 5 * elementaryGenerator 6 = elementaryGenerator 6 * elementaryGenerator 5 :=
  eq_of_small_and_quotient g269 g270
    (image_g269.trans image_g270.symm) (quotient_g269.trans quotient_g270.symm)

lemma generator_comm_5_7 : elementaryGenerator 5 * elementaryGenerator 7 = elementaryGenerator 7 * elementaryGenerator 5 :=
  eq_of_small_and_quotient g271 g272
    (image_g271.trans image_g272.symm) (quotient_g271.trans quotient_g272.symm)

lemma generator_comm_5_8 : elementaryGenerator 5 * elementaryGenerator 8 = elementaryGenerator 8 * elementaryGenerator 5 :=
  eq_of_small_and_quotient g273 g274
    (image_g273.trans image_g274.symm) (quotient_g273.trans quotient_g274.symm)

lemma generator_comm_5_9 : elementaryGenerator 5 * elementaryGenerator 9 = elementaryGenerator 9 * elementaryGenerator 5 :=
  eq_of_small_and_quotient g275 g276
    (image_g275.trans image_g276.symm) (quotient_g275.trans quotient_g276.symm)

lemma generator_comm_5_10 : elementaryGenerator 5 * elementaryGenerator 10 = elementaryGenerator 10 * elementaryGenerator 5 :=
  eq_of_small_and_quotient g277 g278
    (image_g277.trans image_g278.symm) (quotient_g277.trans quotient_g278.symm)

lemma generator_comm_6_7 : elementaryGenerator 6 * elementaryGenerator 7 = elementaryGenerator 7 * elementaryGenerator 6 :=
  eq_of_small_and_quotient g279 g280
    (image_g279.trans image_g280.symm) (quotient_g279.trans quotient_g280.symm)

lemma generator_comm_6_8 : elementaryGenerator 6 * elementaryGenerator 8 = elementaryGenerator 8 * elementaryGenerator 6 :=
  eq_of_small_and_quotient g281 g282
    (image_g281.trans image_g282.symm) (quotient_g281.trans quotient_g282.symm)

lemma generator_comm_6_9 : elementaryGenerator 6 * elementaryGenerator 9 = elementaryGenerator 9 * elementaryGenerator 6 :=
  eq_of_small_and_quotient g283 g284
    (image_g283.trans image_g284.symm) (quotient_g283.trans quotient_g284.symm)

lemma generator_comm_6_10 : elementaryGenerator 6 * elementaryGenerator 10 = elementaryGenerator 10 * elementaryGenerator 6 :=
  eq_of_small_and_quotient g285 g286
    (image_g285.trans image_g286.symm) (quotient_g285.trans quotient_g286.symm)

lemma generator_comm_7_8 : elementaryGenerator 7 * elementaryGenerator 8 = elementaryGenerator 8 * elementaryGenerator 7 :=
  eq_of_small_and_quotient g287 g288
    (image_g287.trans image_g288.symm) (quotient_g287.trans quotient_g288.symm)

lemma generator_comm_7_9 : elementaryGenerator 7 * elementaryGenerator 9 = elementaryGenerator 9 * elementaryGenerator 7 :=
  eq_of_small_and_quotient g289 g290
    (image_g289.trans image_g290.symm) (quotient_g289.trans quotient_g290.symm)

lemma generator_comm_7_10 : elementaryGenerator 7 * elementaryGenerator 10 = elementaryGenerator 10 * elementaryGenerator 7 :=
  eq_of_small_and_quotient g291 g292
    (image_g291.trans image_g292.symm) (quotient_g291.trans quotient_g292.symm)

lemma generator_comm_8_9 : elementaryGenerator 8 * elementaryGenerator 9 = elementaryGenerator 9 * elementaryGenerator 8 :=
  eq_of_small_and_quotient g293 g294
    (image_g293.trans image_g294.symm) (quotient_g293.trans quotient_g294.symm)

lemma generator_comm_8_10 : elementaryGenerator 8 * elementaryGenerator 10 = elementaryGenerator 10 * elementaryGenerator 8 :=
  eq_of_small_and_quotient g295 g296
    (image_g295.trans image_g296.symm) (quotient_g295.trans quotient_g296.symm)

lemma generator_comm_9_10 : elementaryGenerator 9 * elementaryGenerator 10 = elementaryGenerator 10 * elementaryGenerator 9 :=
  eq_of_small_and_quotient g297 g298
    (image_g297.trans image_g298.symm) (quotient_g297.trans quotient_g298.symm)

end MathieuOverlap
end Janko4.LocalStructure.SymmetricLinear
