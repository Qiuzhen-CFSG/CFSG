module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalCommutant.Products00
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalCommutant.Products01
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalCommutant.Products02
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalCommutant.Products03
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalCommutant.Products04
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalCommutant.Products05
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalCommutant.Products06
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalCommutant.Products07
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalCommutant.Products08
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalCommutant.Products09
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalCommutant.Products10
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalCommutant.Products11
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalCommutant.Products12
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalCommutant.Products13
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalCommutant.Products14
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalCommutant.Products15
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalCommutant.Products16
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalCommutant.Products17

/-!
# Eight actual elements of the involution centralizer

The conjugator words and their Bray exponents are retained explicitly.
Their powers and commutation with the involution are checked on matrices.
Membership uses only products and inverses of the two certified generators.

Source matrices: `Janko4/Model/Data.lean` (ATLAS J4G1-f2r112B0).
Reproduction: `LocalCommutant/source/generate.py`; candidate data are untrusted.
Every numerical identity below is checked by the Lean kernel.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.CommutantCertificate
open GeneratorCertificates Janko4.Simplicity.Elevens.BridgeCertificate

set_option maxRecDepth 10000

def g000 : Model := 1

theorem image_g000 : toMatrix g000 = m000 := by
  change toMatrix (1) = _
  rw [map_one, identity_matrix]

def g001 : Model := a

theorem image_g001 : toMatrix g001 = m001 := by
  change toMatrix (a) = _
  rw [toMatrix_a, generator_a_matrix]

def g002 : Model := b

theorem image_g002 : toMatrix g002 = m002 := by
  change toMatrix (b) = _
  rw [toMatrix_b, generator_b_matrix]

def g003 : Model := g000 * g002

theorem image_g003 : toMatrix g003 = m002 := by
  change toMatrix (g000 * g002) = _
  rw [map_mul, image_g000, image_g002]
  exact product000

def g004 : Model := g003⁻¹

theorem image_g004 : toMatrix g004 = m003 := by
  change toMatrix (g003⁻¹) = _
  apply inv_certificate g003 v002 v003 image_g003
  exact product001.trans identity_matrix

def g005 : Model := g001 * g004

theorem image_g005 : toMatrix g005 = m004 := by
  change toMatrix (g001 * g004) = _
  rw [map_mul, image_g001, image_g004]
  exact product002

def g006 : Model := g005 * g001

theorem image_g006 : toMatrix g006 = m005 := by
  change toMatrix (g005 * g001) = _
  rw [map_mul, image_g005, image_g001]
  exact product003

def g007 : Model := g006 * g003

theorem image_g007 : toMatrix g007 = m006 := by
  change toMatrix (g006 * g003) = _
  rw [map_mul, image_g006, image_g003]
  exact product004

def g008 : Model := g007 ^ 2

theorem image_g008 : toMatrix g008 = m007 := by
  change toMatrix (g007 ^ 2) = _
  have hp : g007 ^ 2 = g007 * g007 := by
    simpa only [pow_one] using (pow_add g007 1 1)
  rw [hp, map_mul, image_g007]
  exact product005

def g009 : Model := g007 ^ 3

theorem image_g009 : toMatrix g009 = m008 := by
  change toMatrix (g007 ^ 3) = _
  have hp : g007 ^ 3 = g007 * g008 := by
    simpa only [g008, pow_one] using (pow_add g007 1 2)
  rw [hp, map_mul, image_g007, image_g008]
  exact product006

def g010 : Model := g007 ^ 5

theorem image_g010 : toMatrix g010 = m009 := by
  change toMatrix (g007 ^ 5) = _
  have hp : g007 ^ 5 = g008 * g009 := by
    simpa only [g008, g009, pow_one] using (pow_add g007 2 3)
  rw [hp, map_mul, image_g008, image_g009]
  exact product007

def g011 : Model := g007 ^ 10

theorem image_g011 : toMatrix g011 = m000 := by
  change toMatrix (g007 ^ 10) = _
  have hp : g007 ^ 10 = g010 * g010 := by
    simpa only [g010, pow_one] using (pow_add g007 5 5)
  rw [hp, map_mul, image_g010]
  exact product008

def g012 : Model := g003 * g002

theorem image_g012 : toMatrix g012 = m011 := by
  change toMatrix (g003 * g002) = _
  rw [map_mul, image_g003, image_g002]
  exact product011

def g013 : Model := g012⁻¹

theorem image_g013 : toMatrix g013 = m011 := by
  change toMatrix (g012⁻¹) = _
  apply inv_certificate g012 v011 v011 image_g012
  exact product012.trans identity_matrix

def g014 : Model := g001 * g013

theorem image_g014 : toMatrix g014 = m012 := by
  change toMatrix (g001 * g013) = _
  rw [map_mul, image_g001, image_g013]
  exact product013

def g015 : Model := g014 * g001

theorem image_g015 : toMatrix g015 = m013 := by
  change toMatrix (g014 * g001) = _
  rw [map_mul, image_g014, image_g001]
  exact product014

def g016 : Model := g015 * g012

theorem image_g016 : toMatrix g016 = m014 := by
  change toMatrix (g015 * g012) = _
  rw [map_mul, image_g015, image_g012]
  exact product015

def g017 : Model := g016 ^ 2

theorem image_g017 : toMatrix g017 = m015 := by
  change toMatrix (g016 ^ 2) = _
  have hp : g016 ^ 2 = g016 * g016 := by
    simpa only [pow_one] using (pow_add g016 1 1)
  rw [hp, map_mul, image_g016]
  exact product016

def g018 : Model := g016 ^ 3

theorem image_g018 : toMatrix g018 = m016 := by
  change toMatrix (g016 ^ 3) = _
  have hp : g016 ^ 3 = g016 * g017 := by
    simpa only [g017, pow_one] using (pow_add g016 1 2)
  rw [hp, map_mul, image_g016, image_g017]
  exact product017

def g019 : Model := g016 ^ 6

theorem image_g019 : toMatrix g019 = m000 := by
  change toMatrix (g016 ^ 6) = _
  have hp : g016 ^ 6 = g018 * g018 := by
    simpa only [g018, pow_one] using (pow_add g016 3 3)
  rw [hp, map_mul, image_g018]
  exact product018

def g020 : Model := g003 * g001

theorem image_g020 : toMatrix g020 = m018 := by
  change toMatrix (g003 * g001) = _
  rw [map_mul, image_g003, image_g001]
  exact product021

def g021 : Model := g020 * g002

theorem image_g021 : toMatrix g021 = m019 := by
  change toMatrix (g020 * g002) = _
  rw [map_mul, image_g020, image_g002]
  exact product022

def g022 : Model := g021⁻¹

theorem image_g022 : toMatrix g022 = m020 := by
  change toMatrix (g021⁻¹) = _
  apply inv_certificate g021 v019 v020 image_g021
  exact product023.trans identity_matrix

def g023 : Model := g001 * g022

theorem image_g023 : toMatrix g023 = m021 := by
  change toMatrix (g001 * g022) = _
  rw [map_mul, image_g001, image_g022]
  exact product024

def g024 : Model := g023 * g001

theorem image_g024 : toMatrix g024 = m022 := by
  change toMatrix (g023 * g001) = _
  rw [map_mul, image_g023, image_g001]
  exact product025

def g025 : Model := g024 * g021

theorem image_g025 : toMatrix g025 = m023 := by
  change toMatrix (g024 * g021) = _
  rw [map_mul, image_g024, image_g021]
  exact product026

def g026 : Model := g025 ^ 2

theorem image_g026 : toMatrix g026 = m024 := by
  change toMatrix (g025 ^ 2) = _
  have hp : g025 ^ 2 = g025 * g025 := by
    simpa only [pow_one] using (pow_add g025 1 1)
  rw [hp, map_mul, image_g025]
  exact product027

def g027 : Model := g025 ^ 4

theorem image_g027 : toMatrix g027 = m025 := by
  change toMatrix (g025 ^ 4) = _
  have hp : g025 ^ 4 = g026 * g026 := by
    simpa only [g026, pow_one] using (pow_add g025 2 2)
  rw [hp, map_mul, image_g026]
  exact product028

def g028 : Model := g025 ^ 8

theorem image_g028 : toMatrix g028 = m000 := by
  change toMatrix (g025 ^ 8) = _
  have hp : g025 ^ 8 = g027 * g027 := by
    simpa only [g027, pow_one] using (pow_add g025 4 4)
  rw [hp, map_mul, image_g027]
  exact product029

def g029 : Model := g021 * g002

theorem image_g029 : toMatrix g029 = m027 := by
  change toMatrix (g021 * g002) = _
  rw [map_mul, image_g021, image_g002]
  exact product032

def g030 : Model := g029⁻¹

theorem image_g030 : toMatrix g030 = m028 := by
  change toMatrix (g029⁻¹) = _
  apply inv_certificate g029 v027 v028 image_g029
  exact product033.trans identity_matrix

def g031 : Model := g001 * g030

theorem image_g031 : toMatrix g031 = m029 := by
  change toMatrix (g001 * g030) = _
  rw [map_mul, image_g001, image_g030]
  exact product034

def g032 : Model := g031 * g001

theorem image_g032 : toMatrix g032 = m030 := by
  change toMatrix (g031 * g001) = _
  rw [map_mul, image_g031, image_g001]
  exact product035

def g033 : Model := g032 * g029

theorem image_g033 : toMatrix g033 = m031 := by
  change toMatrix (g032 * g029) = _
  rw [map_mul, image_g032, image_g029]
  exact product036

def g034 : Model := g033 ^ 2

theorem image_g034 : toMatrix g034 = m032 := by
  change toMatrix (g033 ^ 2) = _
  have hp : g033 ^ 2 = g033 * g033 := by
    simpa only [pow_one] using (pow_add g033 1 1)
  rw [hp, map_mul, image_g033]
  exact product037

def g035 : Model := g033 ^ 3

theorem image_g035 : toMatrix g035 = m033 := by
  change toMatrix (g033 ^ 3) = _
  have hp : g033 ^ 3 = g033 * g034 := by
    simpa only [g034, pow_one] using (pow_add g033 1 2)
  rw [hp, map_mul, image_g033, image_g034]
  exact product038

def g036 : Model := g033 ^ 6

theorem image_g036 : toMatrix g036 = m034 := by
  change toMatrix (g033 ^ 6) = _
  have hp : g033 ^ 6 = g035 * g035 := by
    simpa only [g035, pow_one] using (pow_add g033 3 3)
  rw [hp, map_mul, image_g035]
  exact product039

def g037 : Model := g033 ^ 12

theorem image_g037 : toMatrix g037 = m000 := by
  change toMatrix (g033 ^ 12) = _
  have hp : g033 ^ 12 = g036 * g036 := by
    simpa only [g036, pow_one] using (pow_add g033 6 6)
  rw [hp, map_mul, image_g036]
  exact product040

def g038 : Model := g012 * g001

theorem image_g038 : toMatrix g038 = m036 := by
  change toMatrix (g012 * g001) = _
  rw [map_mul, image_g012, image_g001]
  exact product043

def g039 : Model := g038 * g002

theorem image_g039 : toMatrix g039 = m037 := by
  change toMatrix (g038 * g002) = _
  rw [map_mul, image_g038, image_g002]
  exact product044

def g040 : Model := g039 * g002

theorem image_g040 : toMatrix g040 = m038 := by
  change toMatrix (g039 * g002) = _
  rw [map_mul, image_g039, image_g002]
  exact product045

def g041 : Model := g040⁻¹

theorem image_g041 : toMatrix g041 = m038 := by
  change toMatrix (g040⁻¹) = _
  apply inv_certificate g040 v038 v038 image_g040
  exact product046.trans identity_matrix

def g042 : Model := g001 * g041

theorem image_g042 : toMatrix g042 = m014 := by
  change toMatrix (g001 * g041) = _
  rw [map_mul, image_g001, image_g041]
  exact product047

def g043 : Model := g042 * g001

theorem image_g043 : toMatrix g043 = m039 := by
  change toMatrix (g042 * g001) = _
  rw [map_mul, image_g042, image_g001]
  exact product048

def g044 : Model := g043 * g040

theorem image_g044 : toMatrix g044 = m015 := by
  change toMatrix (g043 * g040) = _
  rw [map_mul, image_g043, image_g040]
  exact product049

def g045 : Model := g044 ^ 2

theorem image_g045 : toMatrix g045 = m040 := by
  change toMatrix (g044 ^ 2) = _
  have hp : g044 ^ 2 = g044 * g044 := by
    simpa only [pow_one] using (pow_add g044 1 1)
  rw [hp, map_mul, image_g044]
  exact product050

def g046 : Model := g044 ^ 3

theorem image_g046 : toMatrix g046 = m000 := by
  change toMatrix (g044 ^ 3) = _
  have hp : g044 ^ 3 = g044 * g045 := by
    simpa only [g045, pow_one] using (pow_add g044 1 2)
  rw [hp, map_mul, image_g044, image_g045]
  exact product051

def g047 : Model := g040 * g044

theorem image_g047 : toMatrix g047 = m017 := by
  change toMatrix (g040 * g044) = _
  rw [map_mul, image_g040, image_g044]
  exact product052

def g048 : Model := g029 * g001

theorem image_g048 : toMatrix g048 = m041 := by
  change toMatrix (g029 * g001) = _
  rw [map_mul, image_g029, image_g001]
  exact product055

def g049 : Model := g048 * g002

theorem image_g049 : toMatrix g049 = m042 := by
  change toMatrix (g048 * g002) = _
  rw [map_mul, image_g048, image_g002]
  exact product056

def g050 : Model := g049⁻¹

theorem image_g050 : toMatrix g050 = m043 := by
  change toMatrix (g049⁻¹) = _
  apply inv_certificate g049 v042 v043 image_g049
  exact product057.trans identity_matrix

def g051 : Model := g001 * g050

theorem image_g051 : toMatrix g051 = m044 := by
  change toMatrix (g001 * g050) = _
  rw [map_mul, image_g001, image_g050]
  exact product058

def g052 : Model := g051 * g001

theorem image_g052 : toMatrix g052 = m045 := by
  change toMatrix (g051 * g001) = _
  rw [map_mul, image_g051, image_g001]
  exact product059

def g053 : Model := g052 * g049

theorem image_g053 : toMatrix g053 = m046 := by
  change toMatrix (g052 * g049) = _
  rw [map_mul, image_g052, image_g049]
  exact product060

def g054 : Model := g053 ^ 2

theorem image_g054 : toMatrix g054 = m047 := by
  change toMatrix (g053 ^ 2) = _
  have hp : g053 ^ 2 = g053 * g053 := by
    simpa only [pow_one] using (pow_add g053 1 1)
  rw [hp, map_mul, image_g053]
  exact product061

def g055 : Model := g053 ^ 3

theorem image_g055 : toMatrix g055 = m048 := by
  change toMatrix (g053 ^ 3) = _
  have hp : g053 ^ 3 = g053 * g054 := by
    simpa only [g054, pow_one] using (pow_add g053 1 2)
  rw [hp, map_mul, image_g053, image_g054]
  exact product062

def g056 : Model := g053 ^ 5

theorem image_g056 : toMatrix g056 = m049 := by
  change toMatrix (g053 ^ 5) = _
  have hp : g053 ^ 5 = g054 * g055 := by
    simpa only [g054, g055, pow_one] using (pow_add g053 2 3)
  rw [hp, map_mul, image_g054, image_g055]
  exact product063

def g057 : Model := g053 ^ 6

theorem image_g057 : toMatrix g057 = m050 := by
  change toMatrix (g053 ^ 6) = _
  have hp : g053 ^ 6 = g055 * g055 := by
    simpa only [g055, pow_one] using (pow_add g053 3 3)
  rw [hp, map_mul, image_g055]
  exact product064

def g058 : Model := g053 ^ 11

theorem image_g058 : toMatrix g058 = m000 := by
  change toMatrix (g053 ^ 11) = _
  have hp : g053 ^ 11 = g056 * g057 := by
    simpa only [g056, g057, pow_one] using (pow_add g053 5 6)
  rw [hp, map_mul, image_g056, image_g057]
  exact product065

def g059 : Model := g049 * g056

theorem image_g059 : toMatrix g059 = m051 := by
  change toMatrix (g049 * g056) = _
  rw [map_mul, image_g049, image_g056]
  exact product066

def g060 : Model := g049 * g002

theorem image_g060 : toMatrix g060 = m053 := by
  change toMatrix (g049 * g002) = _
  rw [map_mul, image_g049, image_g002]
  exact product069

def g061 : Model := g060⁻¹

theorem image_g061 : toMatrix g061 = m054 := by
  change toMatrix (g060⁻¹) = _
  apply inv_certificate g060 v053 v054 image_g060
  exact product070.trans identity_matrix

def g062 : Model := g001 * g061

theorem image_g062 : toMatrix g062 = m055 := by
  change toMatrix (g001 * g061) = _
  rw [map_mul, image_g001, image_g061]
  exact product071

def g063 : Model := g062 * g001

theorem image_g063 : toMatrix g063 = m056 := by
  change toMatrix (g062 * g001) = _
  rw [map_mul, image_g062, image_g001]
  exact product072

def g064 : Model := g063 * g060

theorem image_g064 : toMatrix g064 = m057 := by
  change toMatrix (g063 * g060) = _
  rw [map_mul, image_g063, image_g060]
  exact product073

def g065 : Model := g064 ^ 2

theorem image_g065 : toMatrix g065 = m058 := by
  change toMatrix (g064 ^ 2) = _
  have hp : g064 ^ 2 = g064 * g064 := by
    simpa only [pow_one] using (pow_add g064 1 1)
  rw [hp, map_mul, image_g064]
  exact product074

def g066 : Model := g064 ^ 3

theorem image_g066 : toMatrix g066 = m059 := by
  change toMatrix (g064 ^ 3) = _
  have hp : g064 ^ 3 = g064 * g065 := by
    simpa only [g065, pow_one] using (pow_add g064 1 2)
  rw [hp, map_mul, image_g064, image_g065]
  exact product075

def g067 : Model := g064 ^ 5

theorem image_g067 : toMatrix g067 = m060 := by
  change toMatrix (g064 ^ 5) = _
  have hp : g064 ^ 5 = g065 * g066 := by
    simpa only [g065, g066, pow_one] using (pow_add g064 2 3)
  rw [hp, map_mul, image_g065, image_g066]
  exact product076

def g068 : Model := g064 ^ 6

theorem image_g068 : toMatrix g068 = m061 := by
  change toMatrix (g064 ^ 6) = _
  have hp : g064 ^ 6 = g066 * g066 := by
    simpa only [g066, pow_one] using (pow_add g064 3 3)
  rw [hp, map_mul, image_g066]
  exact product077

def g069 : Model := g064 ^ 11

theorem image_g069 : toMatrix g069 = m000 := by
  change toMatrix (g064 ^ 11) = _
  have hp : g064 ^ 11 = g067 * g068 := by
    simpa only [g067, g068, pow_one] using (pow_add g064 5 6)
  rw [hp, map_mul, image_g067, image_g068]
  exact product078

def g070 : Model := g060 * g067

theorem image_g070 : toMatrix g070 = m062 := by
  change toMatrix (g060 * g067) = _
  rw [map_mul, image_g060, image_g067]
  exact product079

def g071 : Model := g021 * g001

theorem image_g071 : toMatrix g071 = m064 := by
  change toMatrix (g021 * g001) = _
  rw [map_mul, image_g021, image_g001]
  exact product082

def g072 : Model := g071 * g002

theorem image_g072 : toMatrix g072 = m065 := by
  change toMatrix (g071 * g002) = _
  rw [map_mul, image_g071, image_g002]
  exact product083

def g073 : Model := g072 * g001

theorem image_g073 : toMatrix g073 = m066 := by
  change toMatrix (g072 * g001) = _
  rw [map_mul, image_g072, image_g001]
  exact product084

def g074 : Model := g073 * g002

theorem image_g074 : toMatrix g074 = m067 := by
  change toMatrix (g073 * g002) = _
  rw [map_mul, image_g073, image_g002]
  exact product085

def g075 : Model := g074 * g002

theorem image_g075 : toMatrix g075 = m068 := by
  change toMatrix (g074 * g002) = _
  rw [map_mul, image_g074, image_g002]
  exact product086

def g076 : Model := g075⁻¹

theorem image_g076 : toMatrix g076 = m069 := by
  change toMatrix (g075⁻¹) = _
  apply inv_certificate g075 v068 v069 image_g075
  exact product087.trans identity_matrix

def g077 : Model := g001 * g076

theorem image_g077 : toMatrix g077 = m070 := by
  change toMatrix (g001 * g076) = _
  rw [map_mul, image_g001, image_g076]
  exact product088

def g078 : Model := g077 * g001

theorem image_g078 : toMatrix g078 = m071 := by
  change toMatrix (g077 * g001) = _
  rw [map_mul, image_g077, image_g001]
  exact product089

def g079 : Model := g078 * g075

theorem image_g079 : toMatrix g079 = m072 := by
  change toMatrix (g078 * g075) = _
  rw [map_mul, image_g078, image_g075]
  exact product090

def g080 : Model := g079 ^ 2

theorem image_g080 : toMatrix g080 = m073 := by
  change toMatrix (g079 ^ 2) = _
  have hp : g079 ^ 2 = g079 * g079 := by
    simpa only [pow_one] using (pow_add g079 1 1)
  rw [hp, map_mul, image_g079]
  exact product091

def g081 : Model := g079 ^ 3

theorem image_g081 : toMatrix g081 = m074 := by
  change toMatrix (g079 ^ 3) = _
  have hp : g079 ^ 3 = g079 * g080 := by
    simpa only [g080, pow_one] using (pow_add g079 1 2)
  rw [hp, map_mul, image_g079, image_g080]
  exact product092

def g082 : Model := g079 ^ 6

theorem image_g082 : toMatrix g082 = m075 := by
  change toMatrix (g079 ^ 6) = _
  have hp : g079 ^ 6 = g081 * g081 := by
    simpa only [g081, pow_one] using (pow_add g079 3 3)
  rw [hp, map_mul, image_g081]
  exact product093

def g083 : Model := g079 ^ 12

theorem image_g083 : toMatrix g083 = m000 := by
  change toMatrix (g079 ^ 12) = _
  have hp : g079 ^ 12 = g082 * g082 := by
    simpa only [g082, pow_one] using (pow_add g079 6 6)
  rw [hp, map_mul, image_g082]
  exact product094

/-- The conjugator is `b` and the checked exponent is 10. -/
theorem bray_power0 : g007 ^ 10 = 1 := by
  apply toMatrix_injective
  exact image_g011.trans (identity_matrix.trans (map_one toMatrix).symm)

theorem bray_commutes0 : toAmbient g010 * matrixUnitA =
    matrixUnitA * toAmbient g010 := by
  apply Units.ext
  change toMatrix g010 * matrixA = matrixA * toMatrix g010
  rw [image_g010, generator_a_matrix, product009, product010]

def c0 : involutionCentralizer :=
  ⟨toAmbient g010, (mem_involutionCentralizer_iff _).mpr
    ⟨g010.property, bray_commutes0⟩⟩

theorem image_c0 : ((c0 : BinaryMatrixˣ) : BinaryMatrix) = m009 :=
  image_g010

/-- The conjugator is `bb` and the checked exponent is 6. -/
theorem bray_power1 : g016 ^ 6 = 1 := by
  apply toMatrix_injective
  exact image_g019.trans (identity_matrix.trans (map_one toMatrix).symm)

theorem bray_commutes1 : toAmbient g018 * matrixUnitA =
    matrixUnitA * toAmbient g018 := by
  apply Units.ext
  change toMatrix g018 * matrixA = matrixA * toMatrix g018
  rw [image_g018, generator_a_matrix, product019, product020]

def c1 : involutionCentralizer :=
  ⟨toAmbient g018, (mem_involutionCentralizer_iff _).mpr
    ⟨g018.property, bray_commutes1⟩⟩

theorem image_c1 : ((c1 : BinaryMatrixˣ) : BinaryMatrix) = m016 :=
  image_g018

/-- The conjugator is `bab` and the checked exponent is 8. -/
theorem bray_power2 : g025 ^ 8 = 1 := by
  apply toMatrix_injective
  exact image_g028.trans (identity_matrix.trans (map_one toMatrix).symm)

theorem bray_commutes2 : toAmbient g027 * matrixUnitA =
    matrixUnitA * toAmbient g027 := by
  apply Units.ext
  change toMatrix g027 * matrixA = matrixA * toMatrix g027
  rw [image_g027, generator_a_matrix, product030, product031]

def c2 : involutionCentralizer :=
  ⟨toAmbient g027, (mem_involutionCentralizer_iff _).mpr
    ⟨g027.property, bray_commutes2⟩⟩

theorem image_c2 : ((c2 : BinaryMatrixˣ) : BinaryMatrix) = m025 :=
  image_g027

/-- The conjugator is `babb` and the checked exponent is 12. -/
theorem bray_power3 : g033 ^ 12 = 1 := by
  apply toMatrix_injective
  exact image_g037.trans (identity_matrix.trans (map_one toMatrix).symm)

theorem bray_commutes3 : toAmbient g036 * matrixUnitA =
    matrixUnitA * toAmbient g036 := by
  apply Units.ext
  change toMatrix g036 * matrixA = matrixA * toMatrix g036
  rw [image_g036, generator_a_matrix, product041, product042]

def c3 : involutionCentralizer :=
  ⟨toAmbient g036, (mem_involutionCentralizer_iff _).mpr
    ⟨g036.property, bray_commutes3⟩⟩

theorem image_c3 : ((c3 : BinaryMatrixˣ) : BinaryMatrix) = m034 :=
  image_g036

/-- The conjugator is `bbabb` and the checked exponent is 3. -/
theorem bray_power4 : g044 ^ 3 = 1 := by
  apply toMatrix_injective
  exact image_g046.trans (identity_matrix.trans (map_one toMatrix).symm)

theorem bray_commutes4 : toAmbient g047 * matrixUnitA =
    matrixUnitA * toAmbient g047 := by
  apply Units.ext
  change toMatrix g047 * matrixA = matrixA * toMatrix g047
  rw [image_g047, generator_a_matrix, product053, product054]

def c4 : involutionCentralizer :=
  ⟨toAmbient g047, (mem_involutionCentralizer_iff _).mpr
    ⟨g047.property, bray_commutes4⟩⟩

theorem image_c4 : ((c4 : BinaryMatrixˣ) : BinaryMatrix) = m017 :=
  image_g047

/-- The conjugator is `babbab` and the checked exponent is 11. -/
theorem bray_power5 : g053 ^ 11 = 1 := by
  apply toMatrix_injective
  exact image_g058.trans (identity_matrix.trans (map_one toMatrix).symm)

theorem bray_commutes5 : toAmbient g059 * matrixUnitA =
    matrixUnitA * toAmbient g059 := by
  apply Units.ext
  change toMatrix g059 * matrixA = matrixA * toMatrix g059
  rw [image_g059, generator_a_matrix, product067, product068]

def c5 : involutionCentralizer :=
  ⟨toAmbient g059, (mem_involutionCentralizer_iff _).mpr
    ⟨g059.property, bray_commutes5⟩⟩

theorem image_c5 : ((c5 : BinaryMatrixˣ) : BinaryMatrix) = m051 :=
  image_g059

/-- The conjugator is `babbabb` and the checked exponent is 11. -/
theorem bray_power6 : g064 ^ 11 = 1 := by
  apply toMatrix_injective
  exact image_g069.trans (identity_matrix.trans (map_one toMatrix).symm)

theorem bray_commutes6 : toAmbient g070 * matrixUnitA =
    matrixUnitA * toAmbient g070 := by
  apply Units.ext
  change toMatrix g070 * matrixA = matrixA * toMatrix g070
  rw [image_g070, generator_a_matrix, product080, product081]

def c6 : involutionCentralizer :=
  ⟨toAmbient g070, (mem_involutionCentralizer_iff _).mpr
    ⟨g070.property, bray_commutes6⟩⟩

theorem image_c6 : ((c6 : BinaryMatrixˣ) : BinaryMatrix) = m062 :=
  image_g070

/-- The conjugator is `babababb` and the checked exponent is 12. -/
theorem bray_power7 : g079 ^ 12 = 1 := by
  apply toMatrix_injective
  exact image_g083.trans (identity_matrix.trans (map_one toMatrix).symm)

theorem bray_commutes7 : toAmbient g082 * matrixUnitA =
    matrixUnitA * toAmbient g082 := by
  apply Units.ext
  change toMatrix g082 * matrixA = matrixA * toMatrix g082
  rw [image_g082, generator_a_matrix, product095, product096]

def c7 : involutionCentralizer :=
  ⟨toAmbient g082, (mem_involutionCentralizer_iff _).mpr
    ⟨g082.property, bray_commutes7⟩⟩

theorem image_c7 : ((c7 : BinaryMatrixˣ) : BinaryMatrix) = m075 :=
  image_g082

def w000 : involutionCentralizer := 1

theorem image_w000 : ((w000 : BinaryMatrixˣ) : BinaryMatrix) = m000 :=
  identity_matrix.symm

def w001 : involutionCentralizer := w000 * c0

theorem image_w001 : ((w001 : BinaryMatrixˣ) : BinaryMatrix) = m009 := by
  change ((w000 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c0 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w000, image_c0]
  exact product097

def w002 : involutionCentralizer := w000 * c1

theorem image_w002 : ((w002 : BinaryMatrixˣ) : BinaryMatrix) = m016 := by
  change ((w000 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c1 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w000, image_c1]
  exact product098

def w003 : involutionCentralizer := w000 * c2

theorem image_w003 : ((w003 : BinaryMatrixˣ) : BinaryMatrix) = m025 := by
  change ((w000 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c2 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w000, image_c2]
  exact product099

def w004 : involutionCentralizer := w000 * c3

theorem image_w004 : ((w004 : BinaryMatrixˣ) : BinaryMatrix) = m034 := by
  change ((w000 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c3 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w000, image_c3]
  exact product100

def w005 : involutionCentralizer := w000 * c4

theorem image_w005 : ((w005 : BinaryMatrixˣ) : BinaryMatrix) = m017 := by
  change ((w000 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c4 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w000, image_c4]
  exact product101

def w006 : involutionCentralizer := w000 * c5

theorem image_w006 : ((w006 : BinaryMatrixˣ) : BinaryMatrix) = m051 := by
  change ((w000 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c5 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w000, image_c5]
  exact product102

def w007 : involutionCentralizer := w000 * c6

theorem image_w007 : ((w007 : BinaryMatrixˣ) : BinaryMatrix) = m062 := by
  change ((w000 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c6 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w000, image_c6]
  exact product103

def w008 : involutionCentralizer := w000 * c7

theorem image_w008 : ((w008 : BinaryMatrixˣ) : BinaryMatrix) = m075 := by
  change ((w000 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c7 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w000, image_c7]
  exact product104

def w009 : involutionCentralizer := w001 * c1

theorem image_w009 : ((w009 : BinaryMatrixˣ) : BinaryMatrix) = m077 := by
  change ((w001 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c1 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w001, image_c1]
  exact product105

def w010 : involutionCentralizer := w001 * c2

theorem image_w010 : ((w010 : BinaryMatrixˣ) : BinaryMatrix) = m078 := by
  change ((w001 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c2 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w001, image_c2]
  exact product106

def w011 : involutionCentralizer := w001 * c3

theorem image_w011 : ((w011 : BinaryMatrixˣ) : BinaryMatrix) = m079 := by
  change ((w001 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c3 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w001, image_c3]
  exact product107

def w012 : involutionCentralizer := w001 * c4

theorem image_w012 : ((w012 : BinaryMatrixˣ) : BinaryMatrix) = m080 := by
  change ((w001 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c4 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w001, image_c4]
  exact product108

def w013 : involutionCentralizer := w001 * c5

theorem image_w013 : ((w013 : BinaryMatrixˣ) : BinaryMatrix) = m081 := by
  change ((w001 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c5 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w001, image_c5]
  exact product109

def w014 : involutionCentralizer := w001 * c6

theorem image_w014 : ((w014 : BinaryMatrixˣ) : BinaryMatrix) = m082 := by
  change ((w001 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c6 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w001, image_c6]
  exact product110

def w015 : involutionCentralizer := w001 * c7

theorem image_w015 : ((w015 : BinaryMatrixˣ) : BinaryMatrix) = m083 := by
  change ((w001 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c7 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w001, image_c7]
  exact product111

def w016 : involutionCentralizer := w002 * c0

theorem image_w016 : ((w016 : BinaryMatrixˣ) : BinaryMatrix) = m084 := by
  change ((w002 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c0 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w002, image_c0]
  exact product112

def w017 : involutionCentralizer := w002 * c2

theorem image_w017 : ((w017 : BinaryMatrixˣ) : BinaryMatrix) = m085 := by
  change ((w002 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c2 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w002, image_c2]
  exact product113

def w018 : involutionCentralizer := w002 * c3

theorem image_w018 : ((w018 : BinaryMatrixˣ) : BinaryMatrix) = m086 := by
  change ((w002 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c3 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w002, image_c3]
  exact product114

def w019 : involutionCentralizer := w002 * c4

theorem image_w019 : ((w019 : BinaryMatrixˣ) : BinaryMatrix) = m001 := by
  change ((w002 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c4 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w002, image_c4]
  exact product115

def w020 : involutionCentralizer := w002 * c5

theorem image_w020 : ((w020 : BinaryMatrixˣ) : BinaryMatrix) = m087 := by
  change ((w002 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c5 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w002, image_c5]
  exact product116

def w021 : involutionCentralizer := w002 * c6

theorem image_w021 : ((w021 : BinaryMatrixˣ) : BinaryMatrix) = m088 := by
  change ((w002 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c6 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w002, image_c6]
  exact product117

def w022 : involutionCentralizer := w002 * c7

theorem image_w022 : ((w022 : BinaryMatrixˣ) : BinaryMatrix) = m089 := by
  change ((w002 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c7 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w002, image_c7]
  exact product118

def w023 : involutionCentralizer := w003 * c0

theorem image_w023 : ((w023 : BinaryMatrixˣ) : BinaryMatrix) = m090 := by
  change ((w003 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c0 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w003, image_c0]
  exact product119

def w024 : involutionCentralizer := w003 * c1

theorem image_w024 : ((w024 : BinaryMatrixˣ) : BinaryMatrix) = m091 := by
  change ((w003 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c1 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w003, image_c1]
  exact product120

def w025 : involutionCentralizer := w003 * c3

theorem image_w025 : ((w025 : BinaryMatrixˣ) : BinaryMatrix) = m092 := by
  change ((w003 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c3 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w003, image_c3]
  exact product121

def w026 : involutionCentralizer := w003 * c4

theorem image_w026 : ((w026 : BinaryMatrixˣ) : BinaryMatrix) = m093 := by
  change ((w003 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c4 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w003, image_c4]
  exact product122

def w027 : involutionCentralizer := w003 * c5

theorem image_w027 : ((w027 : BinaryMatrixˣ) : BinaryMatrix) = m094 := by
  change ((w003 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c5 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w003, image_c5]
  exact product123

def w028 : involutionCentralizer := w003 * c6

theorem image_w028 : ((w028 : BinaryMatrixˣ) : BinaryMatrix) = m095 := by
  change ((w003 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c6 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w003, image_c6]
  exact product124

def w029 : involutionCentralizer := w003 * c7

theorem image_w029 : ((w029 : BinaryMatrixˣ) : BinaryMatrix) = m096 := by
  change ((w003 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c7 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w003, image_c7]
  exact product125

def w030 : involutionCentralizer := w004 * c0

theorem image_w030 : ((w030 : BinaryMatrixˣ) : BinaryMatrix) = m097 := by
  change ((w004 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c0 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w004, image_c0]
  exact product126

def w031 : involutionCentralizer := w004 * c1

theorem image_w031 : ((w031 : BinaryMatrixˣ) : BinaryMatrix) = m098 := by
  change ((w004 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c1 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w004, image_c1]
  exact product127

def w032 : involutionCentralizer := w004 * c2

theorem image_w032 : ((w032 : BinaryMatrixˣ) : BinaryMatrix) = m099 := by
  change ((w004 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c2 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w004, image_c2]
  exact product128

def w033 : involutionCentralizer := w004 * c4

theorem image_w033 : ((w033 : BinaryMatrixˣ) : BinaryMatrix) = m100 := by
  change ((w004 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c4 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w004, image_c4]
  exact product129

def w034 : involutionCentralizer := w004 * c5

theorem image_w034 : ((w034 : BinaryMatrixˣ) : BinaryMatrix) = m101 := by
  change ((w004 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c5 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w004, image_c5]
  exact product130

def w035 : involutionCentralizer := w004 * c6

theorem image_w035 : ((w035 : BinaryMatrixˣ) : BinaryMatrix) = m102 := by
  change ((w004 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c6 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w004, image_c6]
  exact product131

def w036 : involutionCentralizer := w004 * c7

theorem image_w036 : ((w036 : BinaryMatrixˣ) : BinaryMatrix) = m103 := by
  change ((w004 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c7 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w004, image_c7]
  exact product132

def w037 : involutionCentralizer := w005 * c0

theorem image_w037 : ((w037 : BinaryMatrixˣ) : BinaryMatrix) = m104 := by
  change ((w005 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c0 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w005, image_c0]
  exact product133

def w038 : involutionCentralizer := w005 * c2

theorem image_w038 : ((w038 : BinaryMatrixˣ) : BinaryMatrix) = m105 := by
  change ((w005 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c2 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w005, image_c2]
  exact product134

def w039 : involutionCentralizer := w005 * c3

theorem image_w039 : ((w039 : BinaryMatrixˣ) : BinaryMatrix) = m106 := by
  change ((w005 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c3 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w005, image_c3]
  exact product135

def w040 : involutionCentralizer := w005 * c5

theorem image_w040 : ((w040 : BinaryMatrixˣ) : BinaryMatrix) = m107 := by
  change ((w005 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c5 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w005, image_c5]
  exact product136

def w041 : involutionCentralizer := w005 * c6

theorem image_w041 : ((w041 : BinaryMatrixˣ) : BinaryMatrix) = m108 := by
  change ((w005 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c6 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w005, image_c6]
  exact product137

def w042 : involutionCentralizer := w005 * c7

theorem image_w042 : ((w042 : BinaryMatrixˣ) : BinaryMatrix) = m109 := by
  change ((w005 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c7 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w005, image_c7]
  exact product138

def w043 : involutionCentralizer := w006 * c0

theorem image_w043 : ((w043 : BinaryMatrixˣ) : BinaryMatrix) = m110 := by
  change ((w006 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c0 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w006, image_c0]
  exact product139

def w044 : involutionCentralizer := w006 * c2

theorem image_w044 : ((w044 : BinaryMatrixˣ) : BinaryMatrix) = m111 := by
  change ((w006 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c2 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w006, image_c2]
  exact product140

def w045 : involutionCentralizer := w006 * c3

theorem image_w045 : ((w045 : BinaryMatrixˣ) : BinaryMatrix) = m112 := by
  change ((w006 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c3 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w006, image_c3]
  exact product141

def w046 : involutionCentralizer := w006 * c6

theorem image_w046 : ((w046 : BinaryMatrixˣ) : BinaryMatrix) = m113 := by
  change ((w006 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c6 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w006, image_c6]
  exact product142

def w047 : involutionCentralizer := w006 * c7

theorem image_w047 : ((w047 : BinaryMatrixˣ) : BinaryMatrix) = m114 := by
  change ((w006 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c7 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w006, image_c7]
  exact product143

def w048 : involutionCentralizer := w007 * c0

theorem image_w048 : ((w048 : BinaryMatrixˣ) : BinaryMatrix) = m115 := by
  change ((w007 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c0 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w007, image_c0]
  exact product144

def w049 : involutionCentralizer := w007 * c1

theorem image_w049 : ((w049 : BinaryMatrixˣ) : BinaryMatrix) = m116 := by
  change ((w007 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c1 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w007, image_c1]
  exact product145

def w050 : involutionCentralizer := w007 * c2

theorem image_w050 : ((w050 : BinaryMatrixˣ) : BinaryMatrix) = m117 := by
  change ((w007 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c2 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w007, image_c2]
  exact product146

def w051 : involutionCentralizer := w007 * c3

theorem image_w051 : ((w051 : BinaryMatrixˣ) : BinaryMatrix) = m118 := by
  change ((w007 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c3 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w007, image_c3]
  exact product147

def w052 : involutionCentralizer := w007 * c4

theorem image_w052 : ((w052 : BinaryMatrixˣ) : BinaryMatrix) = m119 := by
  change ((w007 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c4 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w007, image_c4]
  exact product148

def w053 : involutionCentralizer := w007 * c5

theorem image_w053 : ((w053 : BinaryMatrixˣ) : BinaryMatrix) = m120 := by
  change ((w007 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c5 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w007, image_c5]
  exact product149

def w054 : involutionCentralizer := w007 * c6

theorem image_w054 : ((w054 : BinaryMatrixˣ) : BinaryMatrix) = m121 := by
  change ((w007 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c6 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w007, image_c6]
  exact product150

def w055 : involutionCentralizer := w007 * c7

theorem image_w055 : ((w055 : BinaryMatrixˣ) : BinaryMatrix) = m122 := by
  change ((w007 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c7 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w007, image_c7]
  exact product151

def w056 : involutionCentralizer := w008 * c0

theorem image_w056 : ((w056 : BinaryMatrixˣ) : BinaryMatrix) = m123 := by
  change ((w008 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c0 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w008, image_c0]
  exact product152

def w057 : involutionCentralizer := w008 * c1

theorem image_w057 : ((w057 : BinaryMatrixˣ) : BinaryMatrix) = m124 := by
  change ((w008 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c1 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w008, image_c1]
  exact product153

def w058 : involutionCentralizer := w008 * c2

theorem image_w058 : ((w058 : BinaryMatrixˣ) : BinaryMatrix) = m125 := by
  change ((w008 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c2 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w008, image_c2]
  exact product154

def w059 : involutionCentralizer := w008 * c3

theorem image_w059 : ((w059 : BinaryMatrixˣ) : BinaryMatrix) = m126 := by
  change ((w008 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c3 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w008, image_c3]
  exact product155

def w060 : involutionCentralizer := w008 * c4

theorem image_w060 : ((w060 : BinaryMatrixˣ) : BinaryMatrix) = m127 := by
  change ((w008 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c4 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w008, image_c4]
  exact product156

def w061 : involutionCentralizer := w008 * c5

theorem image_w061 : ((w061 : BinaryMatrixˣ) : BinaryMatrix) = m128 := by
  change ((w008 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c5 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w008, image_c5]
  exact product157

def w062 : involutionCentralizer := w008 * c6

theorem image_w062 : ((w062 : BinaryMatrixˣ) : BinaryMatrix) = m129 := by
  change ((w008 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c6 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w008, image_c6]
  exact product158

def w063 : involutionCentralizer := w009 * c0

theorem image_w063 : ((w063 : BinaryMatrixˣ) : BinaryMatrix) = m130 := by
  change ((w009 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c0 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w009, image_c0]
  exact product159

def w064 : involutionCentralizer := w009 * c2

theorem image_w064 : ((w064 : BinaryMatrixˣ) : BinaryMatrix) = m131 := by
  change ((w009 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c2 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w009, image_c2]
  exact product160

def w065 : involutionCentralizer := w009 * c3

theorem image_w065 : ((w065 : BinaryMatrixˣ) : BinaryMatrix) = m132 := by
  change ((w009 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c3 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w009, image_c3]
  exact product161

def w066 : involutionCentralizer := w009 * c4

theorem image_w066 : ((w066 : BinaryMatrixˣ) : BinaryMatrix) = m010 := by
  change ((w009 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c4 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w009, image_c4]
  exact product162

def w067 : involutionCentralizer := w009 * c5

theorem image_w067 : ((w067 : BinaryMatrixˣ) : BinaryMatrix) = m133 := by
  change ((w009 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c5 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w009, image_c5]
  exact product163

def w068 : involutionCentralizer := w009 * c6

theorem image_w068 : ((w068 : BinaryMatrixˣ) : BinaryMatrix) = m134 := by
  change ((w009 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c6 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w009, image_c6]
  exact product164

def w069 : involutionCentralizer := w009 * c7

theorem image_w069 : ((w069 : BinaryMatrixˣ) : BinaryMatrix) = m135 := by
  change ((w009 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c7 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w009, image_c7]
  exact product165

def w070 : involutionCentralizer := w010 * c0

theorem image_w070 : ((w070 : BinaryMatrixˣ) : BinaryMatrix) = m136 := by
  change ((w010 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c0 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w010, image_c0]
  exact product166

def w071 : involutionCentralizer := w010 * c1

theorem image_w071 : ((w071 : BinaryMatrixˣ) : BinaryMatrix) = m137 := by
  change ((w010 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c1 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w010, image_c1]
  exact product167

def w072 : involutionCentralizer := w010 * c3

theorem image_w072 : ((w072 : BinaryMatrixˣ) : BinaryMatrix) = m138 := by
  change ((w010 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c3 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w010, image_c3]
  exact product168

def w073 : involutionCentralizer := w010 * c4

theorem image_w073 : ((w073 : BinaryMatrixˣ) : BinaryMatrix) = m139 := by
  change ((w010 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c4 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w010, image_c4]
  exact product169

def w074 : involutionCentralizer := w010 * c5

theorem image_w074 : ((w074 : BinaryMatrixˣ) : BinaryMatrix) = m140 := by
  change ((w010 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c5 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w010, image_c5]
  exact product170

def w075 : involutionCentralizer := w010 * c6

theorem image_w075 : ((w075 : BinaryMatrixˣ) : BinaryMatrix) = m141 := by
  change ((w010 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c6 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w010, image_c6]
  exact product171

def w076 : involutionCentralizer := w010 * c7

theorem image_w076 : ((w076 : BinaryMatrixˣ) : BinaryMatrix) = m142 := by
  change ((w010 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c7 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w010, image_c7]
  exact product172

def w077 : involutionCentralizer := w011 * c0

theorem image_w077 : ((w077 : BinaryMatrixˣ) : BinaryMatrix) = m143 := by
  change ((w011 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c0 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w011, image_c0]
  exact product173

def w078 : involutionCentralizer := w011 * c1

theorem image_w078 : ((w078 : BinaryMatrixˣ) : BinaryMatrix) = m144 := by
  change ((w011 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c1 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w011, image_c1]
  exact product174

def w079 : involutionCentralizer := w011 * c2

theorem image_w079 : ((w079 : BinaryMatrixˣ) : BinaryMatrix) = m145 := by
  change ((w011 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c2 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w011, image_c2]
  exact product175

def w080 : involutionCentralizer := w011 * c4

theorem image_w080 : ((w080 : BinaryMatrixˣ) : BinaryMatrix) = m146 := by
  change ((w011 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c4 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w011, image_c4]
  exact product176

def w081 : involutionCentralizer := w011 * c5

theorem image_w081 : ((w081 : BinaryMatrixˣ) : BinaryMatrix) = m147 := by
  change ((w011 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c5 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w011, image_c5]
  exact product177

def w082 : involutionCentralizer := w011 * c6

theorem image_w082 : ((w082 : BinaryMatrixˣ) : BinaryMatrix) = m148 := by
  change ((w011 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c6 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w011, image_c6]
  exact product178

def w083 : involutionCentralizer := w011 * c7

theorem image_w083 : ((w083 : BinaryMatrixˣ) : BinaryMatrix) = m149 := by
  change ((w011 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c7 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w011, image_c7]
  exact product179

def w084 : involutionCentralizer := w012 * c0

theorem image_w084 : ((w084 : BinaryMatrixˣ) : BinaryMatrix) = m150 := by
  change ((w012 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c0 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w012, image_c0]
  exact product180

def w085 : involutionCentralizer := w012 * c2

theorem image_w085 : ((w085 : BinaryMatrixˣ) : BinaryMatrix) = m151 := by
  change ((w012 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c2 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w012, image_c2]
  exact product181

def w086 : involutionCentralizer := w012 * c3

theorem image_w086 : ((w086 : BinaryMatrixˣ) : BinaryMatrix) = m152 := by
  change ((w012 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c3 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w012, image_c3]
  exact product182

def w087 : involutionCentralizer := w012 * c5

theorem image_w087 : ((w087 : BinaryMatrixˣ) : BinaryMatrix) = m153 := by
  change ((w012 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c5 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w012, image_c5]
  exact product183

def w088 : involutionCentralizer := w012 * c6

theorem image_w088 : ((w088 : BinaryMatrixˣ) : BinaryMatrix) = m154 := by
  change ((w012 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c6 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w012, image_c6]
  exact product184

def w089 : involutionCentralizer := w012 * c7

theorem image_w089 : ((w089 : BinaryMatrixˣ) : BinaryMatrix) = m155 := by
  change ((w012 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c7 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w012, image_c7]
  exact product185

def w090 : involutionCentralizer := w013 * c0

theorem image_w090 : ((w090 : BinaryMatrixˣ) : BinaryMatrix) = m156 := by
  change ((w013 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c0 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w013, image_c0]
  exact product186

def w091 : involutionCentralizer := w013 * c2

theorem image_w091 : ((w091 : BinaryMatrixˣ) : BinaryMatrix) = m157 := by
  change ((w013 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c2 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w013, image_c2]
  exact product187

def w092 : involutionCentralizer := w013 * c3

theorem image_w092 : ((w092 : BinaryMatrixˣ) : BinaryMatrix) = m158 := by
  change ((w013 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c3 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w013, image_c3]
  exact product188

def w093 : involutionCentralizer := w013 * c6

theorem image_w093 : ((w093 : BinaryMatrixˣ) : BinaryMatrix) = m159 := by
  change ((w013 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c6 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w013, image_c6]
  exact product189

def w094 : involutionCentralizer := w013 * c7

theorem image_w094 : ((w094 : BinaryMatrixˣ) : BinaryMatrix) = m160 := by
  change ((w013 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c7 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w013, image_c7]
  exact product190

def w095 : involutionCentralizer := w014 * c0

theorem image_w095 : ((w095 : BinaryMatrixˣ) : BinaryMatrix) = m161 := by
  change ((w014 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c0 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w014, image_c0]
  exact product191

def w096 : involutionCentralizer := w014 * c1

theorem image_w096 : ((w096 : BinaryMatrixˣ) : BinaryMatrix) = m162 := by
  change ((w014 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c1 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w014, image_c1]
  exact product192

def w097 : involutionCentralizer := w014 * c2

theorem image_w097 : ((w097 : BinaryMatrixˣ) : BinaryMatrix) = m163 := by
  change ((w014 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c2 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w014, image_c2]
  exact product193

def w098 : involutionCentralizer := w014 * c3

theorem image_w098 : ((w098 : BinaryMatrixˣ) : BinaryMatrix) = m164 := by
  change ((w014 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c3 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w014, image_c3]
  exact product194

def w099 : involutionCentralizer := w014 * c4

theorem image_w099 : ((w099 : BinaryMatrixˣ) : BinaryMatrix) = m165 := by
  change ((w014 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c4 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w014, image_c4]
  exact product195

def w100 : involutionCentralizer := w014 * c5

theorem image_w100 : ((w100 : BinaryMatrixˣ) : BinaryMatrix) = m166 := by
  change ((w014 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c5 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w014, image_c5]
  exact product196

def w101 : involutionCentralizer := w014 * c6

theorem image_w101 : ((w101 : BinaryMatrixˣ) : BinaryMatrix) = m167 := by
  change ((w014 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c6 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w014, image_c6]
  exact product197

def w102 : involutionCentralizer := w014 * c7

theorem image_w102 : ((w102 : BinaryMatrixˣ) : BinaryMatrix) = m168 := by
  change ((w014 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c7 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w014, image_c7]
  exact product198

def w103 : involutionCentralizer := w015 * c0

theorem image_w103 : ((w103 : BinaryMatrixˣ) : BinaryMatrix) = m169 := by
  change ((w015 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c0 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w015, image_c0]
  exact product199

def w104 : involutionCentralizer := w015 * c1

theorem image_w104 : ((w104 : BinaryMatrixˣ) : BinaryMatrix) = m170 := by
  change ((w015 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c1 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w015, image_c1]
  exact product200

def w105 : involutionCentralizer := w015 * c2

theorem image_w105 : ((w105 : BinaryMatrixˣ) : BinaryMatrix) = m171 := by
  change ((w015 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c2 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w015, image_c2]
  exact product201

def w106 : involutionCentralizer := w015 * c3

theorem image_w106 : ((w106 : BinaryMatrixˣ) : BinaryMatrix) = m172 := by
  change ((w015 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c3 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w015, image_c3]
  exact product202

def w107 : involutionCentralizer := w015 * c4

theorem image_w107 : ((w107 : BinaryMatrixˣ) : BinaryMatrix) = m173 := by
  change ((w015 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c4 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w015, image_c4]
  exact product203

def w108 : involutionCentralizer := w015 * c5

theorem image_w108 : ((w108 : BinaryMatrixˣ) : BinaryMatrix) = m174 := by
  change ((w015 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c5 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w015, image_c5]
  exact product204

def w109 : involutionCentralizer := w015 * c6

theorem image_w109 : ((w109 : BinaryMatrixˣ) : BinaryMatrix) = m175 := by
  change ((w015 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c6 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w015, image_c6]
  exact product205

def w110 : involutionCentralizer := w016 * c3

theorem image_w110 : ((w110 : BinaryMatrixˣ) : BinaryMatrix) = m176 := by
  change ((w016 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c3 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w016, image_c3]
  exact product206

def w111 : involutionCentralizer := w016 * c4

theorem image_w111 : ((w111 : BinaryMatrixˣ) : BinaryMatrix) = m177 := by
  change ((w016 : BinaryMatrixˣ) : BinaryMatrix) *
    ((c4 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w016, image_c4]
  exact product207

def extraWord : involutionCentralizer := w016 * c1

theorem image_extraWord : ((extraWord : BinaryMatrixˣ) : BinaryMatrix) = m178 := by
  change ((w016 : BinaryMatrixˣ) : BinaryMatrix) * ((c1 : BinaryMatrixˣ) : BinaryMatrix) = _
  rw [image_w016, image_c1]
  exact product208

def wordElements : Vector involutionCentralizer 112 :=
  ⟨#[w000, w001, w002, w003, w004, w005, w006, w007, w008, w009, w010, w011, w012, w013, w014, w015, w016, w017, w018, w019, w020, w021, w022, w023, w024, w025, w026, w027, w028, w029, w030, w031, w032, w033, w034, w035, w036, w037, w038, w039, w040, w041, w042, w043, w044, w045, w046, w047, w048, w049, w050, w051, w052, w053, w054, w055, w056, w057, w058, w059, w060, w061, w062, w063, w064, w065, w066, w067, w068, w069, w070, w071, w072, w073, w074, w075, w076, w077, w078, w079, w080, w081, w082, w083, w084, w085, w086, w087, w088, w089, w090, w091, w092, w093, w094, w095, w096, w097, w098, w099, w100, w101, w102, w103, w104, w105, w106, w107, w108, w109, w110, w111], by decide⟩

theorem word_images : ∀ i : Fin 112,
    (((wordElements.get i) : BinaryMatrixˣ) : BinaryMatrix) = decodeRows (wordRows.get i) :=
  (Fin.cases image_w000
    (Fin.cases image_w001
    (Fin.cases image_w002
    (Fin.cases image_w003
    (Fin.cases image_w004
    (Fin.cases image_w005
    (Fin.cases image_w006
    (Fin.cases image_w007
    (Fin.cases image_w008
    (Fin.cases image_w009
    (Fin.cases image_w010
    (Fin.cases image_w011
    (Fin.cases image_w012
    (Fin.cases image_w013
    (Fin.cases image_w014
    (Fin.cases image_w015
    (Fin.cases image_w016
    (Fin.cases image_w017
    (Fin.cases image_w018
    (Fin.cases image_w019
    (Fin.cases image_w020
    (Fin.cases image_w021
    (Fin.cases image_w022
    (Fin.cases image_w023
    (Fin.cases image_w024
    (Fin.cases image_w025
    (Fin.cases image_w026
    (Fin.cases image_w027
    (Fin.cases image_w028
    (Fin.cases image_w029
    (Fin.cases image_w030
    (Fin.cases image_w031
    (Fin.cases image_w032
    (Fin.cases image_w033
    (Fin.cases image_w034
    (Fin.cases image_w035
    (Fin.cases image_w036
    (Fin.cases image_w037
    (Fin.cases image_w038
    (Fin.cases image_w039
    (Fin.cases image_w040
    (Fin.cases image_w041
    (Fin.cases image_w042
    (Fin.cases image_w043
    (Fin.cases image_w044
    (Fin.cases image_w045
    (Fin.cases image_w046
    (Fin.cases image_w047
    (Fin.cases image_w048
    (Fin.cases image_w049
    (Fin.cases image_w050
    (Fin.cases image_w051
    (Fin.cases image_w052
    (Fin.cases image_w053
    (Fin.cases image_w054
    (Fin.cases image_w055
    (Fin.cases image_w056
    (Fin.cases image_w057
    (Fin.cases image_w058
    (Fin.cases image_w059
    (Fin.cases image_w060
    (Fin.cases image_w061
    (Fin.cases image_w062
    (Fin.cases image_w063
    (Fin.cases image_w064
    (Fin.cases image_w065
    (Fin.cases image_w066
    (Fin.cases image_w067
    (Fin.cases image_w068
    (Fin.cases image_w069
    (Fin.cases image_w070
    (Fin.cases image_w071
    (Fin.cases image_w072
    (Fin.cases image_w073
    (Fin.cases image_w074
    (Fin.cases image_w075
    (Fin.cases image_w076
    (Fin.cases image_w077
    (Fin.cases image_w078
    (Fin.cases image_w079
    (Fin.cases image_w080
    (Fin.cases image_w081
    (Fin.cases image_w082
    (Fin.cases image_w083
    (Fin.cases image_w084
    (Fin.cases image_w085
    (Fin.cases image_w086
    (Fin.cases image_w087
    (Fin.cases image_w088
    (Fin.cases image_w089
    (Fin.cases image_w090
    (Fin.cases image_w091
    (Fin.cases image_w092
    (Fin.cases image_w093
    (Fin.cases image_w094
    (Fin.cases image_w095
    (Fin.cases image_w096
    (Fin.cases image_w097
    (Fin.cases image_w098
    (Fin.cases image_w099
    (Fin.cases image_w100
    (Fin.cases image_w101
    (Fin.cases image_w102
    (Fin.cases image_w103
    (Fin.cases image_w104
    (Fin.cases image_w105
    (Fin.cases image_w106
    (Fin.cases image_w107
    (Fin.cases image_w108
    (Fin.cases image_w109
    (Fin.cases image_w110
    (Fin.cases image_w111
    (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

def polynomialElements : List involutionCentralizer :=
  [extraWord, w000, w006, w008, w012, w013, w015, w018, w021, w022, w023, w025, w027, w028, w029, w030, w032, w034, w037, w039, w041, w043, w044, w046, w047, w049, w050, w051, w052, w055, w056, w059, w061, w064, w065, w068, w069, w071, w072, w076, w077, w078, w079, w081, w082, w085, w086, w088, w089, w091, w092, w093, w094, w096, w097, w098, w099, w100, w102, w104, w106, w108, w109]

theorem polynomial_images :
    polynomialElements.map (fun c => ((c : BinaryMatrixˣ) : BinaryMatrix)) =
      polynomialRows.map decodeRows := by
  change [((extraWord : BinaryMatrixˣ) : BinaryMatrix), ((w000 : BinaryMatrixˣ) : BinaryMatrix), ((w006 : BinaryMatrixˣ) : BinaryMatrix), ((w008 : BinaryMatrixˣ) : BinaryMatrix), ((w012 : BinaryMatrixˣ) : BinaryMatrix), ((w013 : BinaryMatrixˣ) : BinaryMatrix), ((w015 : BinaryMatrixˣ) : BinaryMatrix), ((w018 : BinaryMatrixˣ) : BinaryMatrix), ((w021 : BinaryMatrixˣ) : BinaryMatrix), ((w022 : BinaryMatrixˣ) : BinaryMatrix), ((w023 : BinaryMatrixˣ) : BinaryMatrix), ((w025 : BinaryMatrixˣ) : BinaryMatrix), ((w027 : BinaryMatrixˣ) : BinaryMatrix), ((w028 : BinaryMatrixˣ) : BinaryMatrix), ((w029 : BinaryMatrixˣ) : BinaryMatrix), ((w030 : BinaryMatrixˣ) : BinaryMatrix), ((w032 : BinaryMatrixˣ) : BinaryMatrix), ((w034 : BinaryMatrixˣ) : BinaryMatrix), ((w037 : BinaryMatrixˣ) : BinaryMatrix), ((w039 : BinaryMatrixˣ) : BinaryMatrix), ((w041 : BinaryMatrixˣ) : BinaryMatrix), ((w043 : BinaryMatrixˣ) : BinaryMatrix), ((w044 : BinaryMatrixˣ) : BinaryMatrix), ((w046 : BinaryMatrixˣ) : BinaryMatrix), ((w047 : BinaryMatrixˣ) : BinaryMatrix), ((w049 : BinaryMatrixˣ) : BinaryMatrix), ((w050 : BinaryMatrixˣ) : BinaryMatrix), ((w051 : BinaryMatrixˣ) : BinaryMatrix), ((w052 : BinaryMatrixˣ) : BinaryMatrix), ((w055 : BinaryMatrixˣ) : BinaryMatrix), ((w056 : BinaryMatrixˣ) : BinaryMatrix), ((w059 : BinaryMatrixˣ) : BinaryMatrix), ((w061 : BinaryMatrixˣ) : BinaryMatrix), ((w064 : BinaryMatrixˣ) : BinaryMatrix), ((w065 : BinaryMatrixˣ) : BinaryMatrix), ((w068 : BinaryMatrixˣ) : BinaryMatrix), ((w069 : BinaryMatrixˣ) : BinaryMatrix), ((w071 : BinaryMatrixˣ) : BinaryMatrix), ((w072 : BinaryMatrixˣ) : BinaryMatrix), ((w076 : BinaryMatrixˣ) : BinaryMatrix), ((w077 : BinaryMatrixˣ) : BinaryMatrix), ((w078 : BinaryMatrixˣ) : BinaryMatrix), ((w079 : BinaryMatrixˣ) : BinaryMatrix), ((w081 : BinaryMatrixˣ) : BinaryMatrix), ((w082 : BinaryMatrixˣ) : BinaryMatrix), ((w085 : BinaryMatrixˣ) : BinaryMatrix), ((w086 : BinaryMatrixˣ) : BinaryMatrix), ((w088 : BinaryMatrixˣ) : BinaryMatrix), ((w089 : BinaryMatrixˣ) : BinaryMatrix), ((w091 : BinaryMatrixˣ) : BinaryMatrix), ((w092 : BinaryMatrixˣ) : BinaryMatrix), ((w093 : BinaryMatrixˣ) : BinaryMatrix), ((w094 : BinaryMatrixˣ) : BinaryMatrix), ((w096 : BinaryMatrixˣ) : BinaryMatrix), ((w097 : BinaryMatrixˣ) : BinaryMatrix), ((w098 : BinaryMatrixˣ) : BinaryMatrix), ((w099 : BinaryMatrixˣ) : BinaryMatrix), ((w100 : BinaryMatrixˣ) : BinaryMatrix), ((w102 : BinaryMatrixˣ) : BinaryMatrix), ((w104 : BinaryMatrixˣ) : BinaryMatrix), ((w106 : BinaryMatrixˣ) : BinaryMatrix), ((w108 : BinaryMatrixˣ) : BinaryMatrix), ((w109 : BinaryMatrixˣ) : BinaryMatrix)] = _
  simp only [polynomialRows, List.map_cons, List.map_nil,
    image_extraWord, image_w000, image_w006, image_w008, image_w012, image_w013, image_w015, image_w018, image_w021, image_w022, image_w023, image_w025, image_w027, image_w028, image_w029, image_w030, image_w032, image_w034, image_w037, image_w039, image_w041, image_w043, image_w044, image_w046, image_w047, image_w049, image_w050, image_w051, image_w052, image_w055, image_w056, image_w059, image_w061, image_w064, image_w065, image_w068, image_w069, image_w071, image_w072, image_w076, image_w077, image_w078, image_w079, image_w081, image_w082, image_w085, image_w086, image_w088, image_w089, image_w091, image_w092, image_w093, image_w094, image_w096, image_w097, image_w098, image_w099, image_w100, image_w102, image_w104, image_w106, image_w108, image_w109]
  rfl

theorem cyclic_right_inverse : qMatrix * qiMatrix = 1 := product209.trans identity_matrix

theorem cyclic_left_inverse : qiMatrix * qMatrix = 1 := product210.trans identity_matrix

theorem annihilator_projection : rMatrix * dMatrix = pMatrix := product211

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.CommutantCertificate
