module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.NormalFour.Evaluation

/-!
# Propagating commutation along the certified cyclic words

Source: ATLAS `J4G1-f2r112B0` and `J4G1-max4W1`, as attributed in
`Model/Data.lean` and `SymmetricLinear/Model.lean`. Reproduce using
`NormalFour/source/generate.py`. All numerical equalities are kernel checked.
-/

@[expose] public section
namespace Janko4.LocalStructure.SymmetricLinear.NormalFour.Certificate
open GeneratorCertificates Simplicity.Elevens.BridgeCertificate Matrix

set_option maxRecDepth 10000

theorem commutes_w000 (T : BinaryMatrix) : T * m000 = m000 * T := by
  rw [identity_matrix, mul_one, one_mul]

theorem commutes_w001 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (_hd : T * dMatrix = dMatrix * T) :
    T * m029 = m029 * T := by
  rw [← product037]
  exact (show Commute T m000 from commutes_w000 T).mul_right (show Commute T cMatrix from hc)

theorem commutes_w002 (T : BinaryMatrix)
    (_hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m030 = m030 * T := by
  rw [← product038]
  exact (show Commute T m000 from commutes_w000 T).mul_right (show Commute T dMatrix from hd)

theorem commutes_w003 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m031 = m031 * T := by
  rw [← product028]
  exact (show Commute T m029 from commutes_w001 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w004 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m039 = m039 * T := by
  rw [← product039]
  exact (show Commute T m029 from commutes_w001 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w005 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m040 = m040 * T := by
  rw [← product040]
  exact (show Commute T m030 from commutes_w002 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w006 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m041 = m041 * T := by
  rw [← product041]
  exact (show Commute T m030 from commutes_w002 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w007 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m034 = m034 * T := by
  rw [← product042]
  exact (show Commute T m031 from commutes_w003 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w008 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m042 = m042 * T := by
  rw [← product043]
  exact (show Commute T m031 from commutes_w003 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w009 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m043 = m043 * T := by
  rw [← product044]
  exact (show Commute T m039 from commutes_w004 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w010 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m044 = m044 * T := by
  rw [← product045]
  exact (show Commute T m039 from commutes_w004 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w011 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m045 = m045 * T := by
  rw [← product046]
  exact (show Commute T m040 from commutes_w005 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w012 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m046 = m046 * T := by
  rw [← product047]
  exact (show Commute T m040 from commutes_w005 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w013 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m047 = m047 * T := by
  rw [← product048]
  exact (show Commute T m041 from commutes_w006 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w014 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m048 = m048 * T := by
  rw [← product049]
  exact (show Commute T m041 from commutes_w006 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w015 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m032 = m032 * T := by
  rw [← product050]
  exact (show Commute T m034 from commutes_w007 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w016 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m049 = m049 * T := by
  rw [← product051]
  exact (show Commute T m034 from commutes_w007 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w017 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m050 = m050 * T := by
  rw [← product052]
  exact (show Commute T m042 from commutes_w008 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w018 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m051 = m051 * T := by
  rw [← product053]
  exact (show Commute T m042 from commutes_w008 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w019 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m052 = m052 * T := by
  rw [← product054]
  exact (show Commute T m043 from commutes_w009 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w020 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m053 = m053 * T := by
  rw [← product055]
  exact (show Commute T m044 from commutes_w010 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w021 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m054 = m054 * T := by
  rw [← product056]
  exact (show Commute T m044 from commutes_w010 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w022 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m055 = m055 * T := by
  rw [← product057]
  exact (show Commute T m045 from commutes_w011 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w023 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m056 = m056 * T := by
  rw [← product058]
  exact (show Commute T m045 from commutes_w011 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w024 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m057 = m057 * T := by
  rw [← product059]
  exact (show Commute T m046 from commutes_w012 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w025 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m058 = m058 * T := by
  rw [← product060]
  exact (show Commute T m047 from commutes_w013 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w026 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m059 = m059 * T := by
  rw [← product061]
  exact (show Commute T m047 from commutes_w013 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w027 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m060 = m060 * T := by
  rw [← product062]
  exact (show Commute T m048 from commutes_w014 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w028 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m061 = m061 * T := by
  rw [← product063]
  exact (show Commute T m048 from commutes_w014 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w029 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m035 = m035 * T := by
  rw [← product064]
  exact (show Commute T m032 from commutes_w015 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w030 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m062 = m062 * T := by
  rw [← product065]
  exact (show Commute T m032 from commutes_w015 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w031 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m063 = m063 * T := by
  rw [← product066]
  exact (show Commute T m049 from commutes_w016 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w032 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m064 = m064 * T := by
  rw [← product067]
  exact (show Commute T m049 from commutes_w016 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w033 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m065 = m065 * T := by
  rw [← product068]
  exact (show Commute T m050 from commutes_w017 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w034 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m066 = m066 * T := by
  rw [← product069]
  exact (show Commute T m051 from commutes_w018 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w035 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m067 = m067 * T := by
  rw [← product070]
  exact (show Commute T m051 from commutes_w018 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w036 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m068 = m068 * T := by
  rw [← product071]
  exact (show Commute T m052 from commutes_w019 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w037 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m069 = m069 * T := by
  rw [← product072]
  exact (show Commute T m052 from commutes_w019 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w038 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m070 = m070 * T := by
  rw [← product073]
  exact (show Commute T m053 from commutes_w020 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w039 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m071 = m071 * T := by
  rw [← product074]
  exact (show Commute T m053 from commutes_w020 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w040 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m072 = m072 * T := by
  rw [← product075]
  exact (show Commute T m054 from commutes_w021 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w041 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m073 = m073 * T := by
  rw [← product076]
  exact (show Commute T m054 from commutes_w021 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w042 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m074 = m074 * T := by
  rw [← product077]
  exact (show Commute T m055 from commutes_w022 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w043 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m075 = m075 * T := by
  rw [← product078]
  exact (show Commute T m055 from commutes_w022 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w044 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m076 = m076 * T := by
  rw [← product079]
  exact (show Commute T m056 from commutes_w023 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w045 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m077 = m077 * T := by
  rw [← product080]
  exact (show Commute T m056 from commutes_w023 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w046 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m078 = m078 * T := by
  rw [← product081]
  exact (show Commute T m057 from commutes_w024 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w047 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m079 = m079 * T := by
  rw [← product082]
  exact (show Commute T m057 from commutes_w024 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w048 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m080 = m080 * T := by
  rw [← product083]
  exact (show Commute T m058 from commutes_w025 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w049 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m081 = m081 * T := by
  rw [← product084]
  exact (show Commute T m058 from commutes_w025 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w050 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m082 = m082 * T := by
  rw [← product085]
  exact (show Commute T m059 from commutes_w026 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w051 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m083 = m083 * T := by
  rw [← product086]
  exact (show Commute T m060 from commutes_w027 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w052 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m084 = m084 * T := by
  rw [← product087]
  exact (show Commute T m060 from commutes_w027 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w053 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m085 = m085 * T := by
  rw [← product088]
  exact (show Commute T m061 from commutes_w028 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w054 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m086 = m086 * T := by
  rw [← product089]
  exact (show Commute T m061 from commutes_w028 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w055 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m087 = m087 * T := by
  rw [← product090]
  exact (show Commute T m035 from commutes_w029 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w056 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m088 = m088 * T := by
  rw [← product091]
  exact (show Commute T m035 from commutes_w029 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w057 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m089 = m089 * T := by
  rw [← product092]
  exact (show Commute T m062 from commutes_w030 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w058 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m090 = m090 * T := by
  rw [← product093]
  exact (show Commute T m062 from commutes_w030 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w059 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m091 = m091 * T := by
  rw [← product094]
  exact (show Commute T m063 from commutes_w031 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w060 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m092 = m092 * T := by
  rw [← product095]
  exact (show Commute T m064 from commutes_w032 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w061 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m093 = m093 * T := by
  rw [← product096]
  exact (show Commute T m064 from commutes_w032 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w062 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m094 = m094 * T := by
  rw [← product097]
  exact (show Commute T m065 from commutes_w033 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w063 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m095 = m095 * T := by
  rw [← product098]
  exact (show Commute T m065 from commutes_w033 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w064 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m096 = m096 * T := by
  rw [← product099]
  exact (show Commute T m066 from commutes_w034 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w065 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m097 = m097 * T := by
  rw [← product100]
  exact (show Commute T m066 from commutes_w034 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w066 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m098 = m098 * T := by
  rw [← product101]
  exact (show Commute T m067 from commutes_w035 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w067 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m099 = m099 * T := by
  rw [← product102]
  exact (show Commute T m067 from commutes_w035 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w068 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m100 = m100 * T := by
  rw [← product103]
  exact (show Commute T m068 from commutes_w036 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w069 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m101 = m101 * T := by
  rw [← product104]
  exact (show Commute T m068 from commutes_w036 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w070 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m102 = m102 * T := by
  rw [← product105]
  exact (show Commute T m069 from commutes_w037 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w071 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m103 = m103 * T := by
  rw [← product106]
  exact (show Commute T m069 from commutes_w037 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w072 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m104 = m104 * T := by
  rw [← product107]
  exact (show Commute T m070 from commutes_w038 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w073 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m105 = m105 * T := by
  rw [← product108]
  exact (show Commute T m070 from commutes_w038 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w074 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m106 = m106 * T := by
  rw [← product109]
  exact (show Commute T m071 from commutes_w039 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w075 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m107 = m107 * T := by
  rw [← product110]
  exact (show Commute T m072 from commutes_w040 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w076 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m108 = m108 * T := by
  rw [← product111]
  exact (show Commute T m072 from commutes_w040 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w077 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m109 = m109 * T := by
  rw [← product112]
  exact (show Commute T m073 from commutes_w041 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w078 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m110 = m110 * T := by
  rw [← product113]
  exact (show Commute T m073 from commutes_w041 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w079 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m111 = m111 * T := by
  rw [← product114]
  exact (show Commute T m074 from commutes_w042 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w080 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m112 = m112 * T := by
  rw [← product115]
  exact (show Commute T m074 from commutes_w042 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w081 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m113 = m113 * T := by
  rw [← product116]
  exact (show Commute T m075 from commutes_w043 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w082 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m114 = m114 * T := by
  rw [← product117]
  exact (show Commute T m075 from commutes_w043 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w083 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m115 = m115 * T := by
  rw [← product118]
  exact (show Commute T m076 from commutes_w044 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w084 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m116 = m116 * T := by
  rw [← product119]
  exact (show Commute T m077 from commutes_w045 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w085 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m117 = m117 * T := by
  rw [← product120]
  exact (show Commute T m077 from commutes_w045 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w086 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m118 = m118 * T := by
  rw [← product121]
  exact (show Commute T m078 from commutes_w046 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w087 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m119 = m119 * T := by
  rw [← product122]
  exact (show Commute T m078 from commutes_w046 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w088 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m120 = m120 * T := by
  rw [← product123]
  exact (show Commute T m079 from commutes_w047 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w089 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m121 = m121 * T := by
  rw [← product124]
  exact (show Commute T m079 from commutes_w047 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w090 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m122 = m122 * T := by
  rw [← product125]
  exact (show Commute T m080 from commutes_w048 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w091 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m123 = m123 * T := by
  rw [← product126]
  exact (show Commute T m080 from commutes_w048 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w092 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m124 = m124 * T := by
  rw [← product127]
  exact (show Commute T m081 from commutes_w049 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w093 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m125 = m125 * T := by
  rw [← product128]
  exact (show Commute T m081 from commutes_w049 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w094 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m126 = m126 * T := by
  rw [← product129]
  exact (show Commute T m082 from commutes_w050 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w095 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m127 = m127 * T := by
  rw [← product130]
  exact (show Commute T m082 from commutes_w050 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w096 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m128 = m128 * T := by
  rw [← product131]
  exact (show Commute T m083 from commutes_w051 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w097 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m129 = m129 * T := by
  rw [← product132]
  exact (show Commute T m083 from commutes_w051 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w098 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m130 = m130 * T := by
  rw [← product133]
  exact (show Commute T m084 from commutes_w052 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w099 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m131 = m131 * T := by
  rw [← product134]
  exact (show Commute T m085 from commutes_w053 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w100 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m132 = m132 * T := by
  rw [← product135]
  exact (show Commute T m085 from commutes_w053 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w101 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m133 = m133 * T := by
  rw [← product136]
  exact (show Commute T m086 from commutes_w054 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w102 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m134 = m134 * T := by
  rw [← product137]
  exact (show Commute T m086 from commutes_w054 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w103 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m135 = m135 * T := by
  rw [← product138]
  exact (show Commute T m087 from commutes_w055 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w104 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m136 = m136 * T := by
  rw [← product139]
  exact (show Commute T m087 from commutes_w055 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w105 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m137 = m137 * T := by
  rw [← product140]
  exact (show Commute T m088 from commutes_w056 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w106 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m138 = m138 * T := by
  rw [← product141]
  exact (show Commute T m088 from commutes_w056 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w107 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m139 = m139 * T := by
  rw [← product142]
  exact (show Commute T m089 from commutes_w057 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w108 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m140 = m140 * T := by
  rw [← product143]
  exact (show Commute T m090 from commutes_w058 T hc hd).mul_right (show Commute T cMatrix from hc)

theorem commutes_w109 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m141 = m141 * T := by
  rw [← product144]
  exact (show Commute T m090 from commutes_w058 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w110 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m142 = m142 * T := by
  rw [← product145]
  exact (show Commute T m091 from commutes_w059 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem commutes_w111 (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m143 = m143 * T := by
  rw [← product146]
  exact (show Commute T m092 from commutes_w060 T hc hd).mul_right (show Commute T dMatrix from hd)

theorem word_commutation (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    ∀ i : Fin 112, T * decodeRows (wordRows.get i) = decodeRows (wordRows.get i) * T :=
  (Fin.cases (commutes_w000 T)
    (Fin.cases (commutes_w001 T hc hd)
    (Fin.cases (commutes_w002 T hc hd)
    (Fin.cases (commutes_w003 T hc hd)
    (Fin.cases (commutes_w004 T hc hd)
    (Fin.cases (commutes_w005 T hc hd)
    (Fin.cases (commutes_w006 T hc hd)
    (Fin.cases (commutes_w007 T hc hd)
    (Fin.cases (commutes_w008 T hc hd)
    (Fin.cases (commutes_w009 T hc hd)
    (Fin.cases (commutes_w010 T hc hd)
    (Fin.cases (commutes_w011 T hc hd)
    (Fin.cases (commutes_w012 T hc hd)
    (Fin.cases (commutes_w013 T hc hd)
    (Fin.cases (commutes_w014 T hc hd)
    (Fin.cases (commutes_w015 T hc hd)
    (Fin.cases (commutes_w016 T hc hd)
    (Fin.cases (commutes_w017 T hc hd)
    (Fin.cases (commutes_w018 T hc hd)
    (Fin.cases (commutes_w019 T hc hd)
    (Fin.cases (commutes_w020 T hc hd)
    (Fin.cases (commutes_w021 T hc hd)
    (Fin.cases (commutes_w022 T hc hd)
    (Fin.cases (commutes_w023 T hc hd)
    (Fin.cases (commutes_w024 T hc hd)
    (Fin.cases (commutes_w025 T hc hd)
    (Fin.cases (commutes_w026 T hc hd)
    (Fin.cases (commutes_w027 T hc hd)
    (Fin.cases (commutes_w028 T hc hd)
    (Fin.cases (commutes_w029 T hc hd)
    (Fin.cases (commutes_w030 T hc hd)
    (Fin.cases (commutes_w031 T hc hd)
    (Fin.cases (commutes_w032 T hc hd)
    (Fin.cases (commutes_w033 T hc hd)
    (Fin.cases (commutes_w034 T hc hd)
    (Fin.cases (commutes_w035 T hc hd)
    (Fin.cases (commutes_w036 T hc hd)
    (Fin.cases (commutes_w037 T hc hd)
    (Fin.cases (commutes_w038 T hc hd)
    (Fin.cases (commutes_w039 T hc hd)
    (Fin.cases (commutes_w040 T hc hd)
    (Fin.cases (commutes_w041 T hc hd)
    (Fin.cases (commutes_w042 T hc hd)
    (Fin.cases (commutes_w043 T hc hd)
    (Fin.cases (commutes_w044 T hc hd)
    (Fin.cases (commutes_w045 T hc hd)
    (Fin.cases (commutes_w046 T hc hd)
    (Fin.cases (commutes_w047 T hc hd)
    (Fin.cases (commutes_w048 T hc hd)
    (Fin.cases (commutes_w049 T hc hd)
    (Fin.cases (commutes_w050 T hc hd)
    (Fin.cases (commutes_w051 T hc hd)
    (Fin.cases (commutes_w052 T hc hd)
    (Fin.cases (commutes_w053 T hc hd)
    (Fin.cases (commutes_w054 T hc hd)
    (Fin.cases (commutes_w055 T hc hd)
    (Fin.cases (commutes_w056 T hc hd)
    (Fin.cases (commutes_w057 T hc hd)
    (Fin.cases (commutes_w058 T hc hd)
    (Fin.cases (commutes_w059 T hc hd)
    (Fin.cases (commutes_w060 T hc hd)
    (Fin.cases (commutes_w061 T hc hd)
    (Fin.cases (commutes_w062 T hc hd)
    (Fin.cases (commutes_w063 T hc hd)
    (Fin.cases (commutes_w064 T hc hd)
    (Fin.cases (commutes_w065 T hc hd)
    (Fin.cases (commutes_w066 T hc hd)
    (Fin.cases (commutes_w067 T hc hd)
    (Fin.cases (commutes_w068 T hc hd)
    (Fin.cases (commutes_w069 T hc hd)
    (Fin.cases (commutes_w070 T hc hd)
    (Fin.cases (commutes_w071 T hc hd)
    (Fin.cases (commutes_w072 T hc hd)
    (Fin.cases (commutes_w073 T hc hd)
    (Fin.cases (commutes_w074 T hc hd)
    (Fin.cases (commutes_w075 T hc hd)
    (Fin.cases (commutes_w076 T hc hd)
    (Fin.cases (commutes_w077 T hc hd)
    (Fin.cases (commutes_w078 T hc hd)
    (Fin.cases (commutes_w079 T hc hd)
    (Fin.cases (commutes_w080 T hc hd)
    (Fin.cases (commutes_w081 T hc hd)
    (Fin.cases (commutes_w082 T hc hd)
    (Fin.cases (commutes_w083 T hc hd)
    (Fin.cases (commutes_w084 T hc hd)
    (Fin.cases (commutes_w085 T hc hd)
    (Fin.cases (commutes_w086 T hc hd)
    (Fin.cases (commutes_w087 T hc hd)
    (Fin.cases (commutes_w088 T hc hd)
    (Fin.cases (commutes_w089 T hc hd)
    (Fin.cases (commutes_w090 T hc hd)
    (Fin.cases (commutes_w091 T hc hd)
    (Fin.cases (commutes_w092 T hc hd)
    (Fin.cases (commutes_w093 T hc hd)
    (Fin.cases (commutes_w094 T hc hd)
    (Fin.cases (commutes_w095 T hc hd)
    (Fin.cases (commutes_w096 T hc hd)
    (Fin.cases (commutes_w097 T hc hd)
    (Fin.cases (commutes_w098 T hc hd)
    (Fin.cases (commutes_w099 T hc hd)
    (Fin.cases (commutes_w100 T hc hd)
    (Fin.cases (commutes_w101 T hc hd)
    (Fin.cases (commutes_w102 T hc hd)
    (Fin.cases (commutes_w103 T hc hd)
    (Fin.cases (commutes_w104 T hc hd)
    (Fin.cases (commutes_w105 T hc hd)
    (Fin.cases (commutes_w106 T hc hd)
    (Fin.cases (commutes_w107 T hc hd)
    (Fin.cases (commutes_w108 T hc hd)
    (Fin.cases (commutes_w109 T hc hd)
    (Fin.cases (commutes_w110 T hc hd)
    (Fin.cases (commutes_w111 T hc hd)
    (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem commutes_extra (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * m144 = m144 * T := by
  rw [← product147]
  exact (show Commute T m131 from commutes_w099 T hc hd).mul_right
    (show Commute T dMatrix from hd)

theorem polynomial_commutation (T : BinaryMatrix)
    (hc : T * cMatrix = cMatrix * T) (hd : T * dMatrix = dMatrix * T) :
    T * (polynomialRows.map decodeRows).sum = (polynomialRows.map decodeRows).sum * T := by
  change Commute T ([m144, m029, m030, m031, m040, m041, m034, m042, m044, m047, m048, m032, m050, m051, m052, m054, m035, m063, m067, m068, m069, m074, m078, m083, m084, m088, m089, m092, m093, m095, m096, m098, m099, m101, m105, m106, m107, m108, m109, m111, m114, m116, m119, m120, m123, m126, m128, m130, m134, m135, m137, m140, m141, m142] : List BinaryMatrix).sum
  apply Commute.list_sum_right
  intro S hS
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact commutes_extra T hc hd
  · exact commutes_w001 T hc hd
  · exact commutes_w002 T hc hd
  · exact commutes_w003 T hc hd
  · exact commutes_w005 T hc hd
  · exact commutes_w006 T hc hd
  · exact commutes_w007 T hc hd
  · exact commutes_w008 T hc hd
  · exact commutes_w010 T hc hd
  · exact commutes_w013 T hc hd
  · exact commutes_w014 T hc hd
  · exact commutes_w015 T hc hd
  · exact commutes_w017 T hc hd
  · exact commutes_w018 T hc hd
  · exact commutes_w019 T hc hd
  · exact commutes_w021 T hc hd
  · exact commutes_w029 T hc hd
  · exact commutes_w031 T hc hd
  · exact commutes_w035 T hc hd
  · exact commutes_w036 T hc hd
  · exact commutes_w037 T hc hd
  · exact commutes_w042 T hc hd
  · exact commutes_w046 T hc hd
  · exact commutes_w051 T hc hd
  · exact commutes_w052 T hc hd
  · exact commutes_w056 T hc hd
  · exact commutes_w057 T hc hd
  · exact commutes_w060 T hc hd
  · exact commutes_w061 T hc hd
  · exact commutes_w063 T hc hd
  · exact commutes_w064 T hc hd
  · exact commutes_w066 T hc hd
  · exact commutes_w067 T hc hd
  · exact commutes_w069 T hc hd
  · exact commutes_w073 T hc hd
  · exact commutes_w074 T hc hd
  · exact commutes_w075 T hc hd
  · exact commutes_w076 T hc hd
  · exact commutes_w077 T hc hd
  · exact commutes_w079 T hc hd
  · exact commutes_w082 T hc hd
  · exact commutes_w084 T hc hd
  · exact commutes_w087 T hc hd
  · exact commutes_w088 T hc hd
  · exact commutes_w091 T hc hd
  · exact commutes_w094 T hc hd
  · exact commutes_w096 T hc hd
  · exact commutes_w098 T hc hd
  · exact commutes_w102 T hc hd
  · exact commutes_w103 T hc hd
  · exact commutes_w105 T hc hd
  · exact commutes_w108 T hc hd
  · exact commutes_w109 T hc hd
  · exact commutes_w110 T hc hd

theorem cyclic_left_inverse : qiMatrix * qMatrix = 1 := product148.trans identity_matrix

theorem annihilator_projection : rMatrix * uMatrix = pMatrix := product149

end Janko4.LocalStructure.SymmetricLinear.NormalFour.Certificate
