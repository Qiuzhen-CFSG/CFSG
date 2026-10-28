module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.NormalFour.Products00
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.NormalFour.Products01
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.NormalFour.Products02
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.NormalFour.Products03
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.NormalFour.Products04
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.NormalFour.Products05
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.NormalFour.Products06
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.NormalFour.Products07
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.NormalFour.Products08
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.NormalFour.Products09
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.NormalFour.Products10
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.NormalFour.Products11
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.NormalFour.Products12

/-!
# Literal program evaluation and the order-35 relation

Source: ATLAS `J4G1-f2r112B0` and `J4G1-max4W1`, as attributed in
`Model/Data.lean` and `SymmetricLinear/Model.lean`. Reproduce using
`NormalFour/source/generate.py`. All numerical equalities are kernel checked.
-/

@[expose] public section
namespace Janko4.LocalStructure.SymmetricLinear.NormalFour.Certificate
open GeneratorCertificates Simplicity.Elevens.BridgeCertificate Matrix

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

def g003 : Model := g001 * g002

theorem image_g003 : toMatrix g003 = m003 := by
  change toMatrix (g001 * g002) = _
  rw [map_mul, image_g001, image_g002]
  exact product000

def g004 : Model := g003 ^ 2

theorem image_g004 : toMatrix g004 = m004 := by
  change toMatrix (g003 ^ 2) = _
  have hp : g003 ^ 2 = g003 * g003 := by
    simpa only [pow_one] using (pow_add g003 1 1)
  rw [hp, map_mul, image_g003]
  exact product001

def g005 : Model := g003 ^ 3

theorem image_g005 : toMatrix g005 = m005 := by
  change toMatrix (g003 ^ 3) = _
  have hp : g003 ^ 3 = g003 * g004 := by
    simpa only [g004, pow_one] using (pow_add g003 1 2)
  rw [hp, map_mul, image_g003, image_g004]
  exact product002

def g006 : Model := g005 * g002

theorem image_g006 : toMatrix g006 = m006 := by
  change toMatrix (g005 * g002) = _
  rw [map_mul, image_g005, image_g002]
  exact product003

def g007 : Model := g002 * g001

theorem image_g007 : toMatrix g007 = m007 := by
  change toMatrix (g002 * g001) = _
  rw [map_mul, image_g002, image_g001]
  exact product004

def g008 : Model := g006 * g002

theorem image_g008 : toMatrix g008 = m008 := by
  change toMatrix (g006 * g002) = _
  rw [map_mul, image_g006, image_g002]
  exact product005

def g009 : Model := g008 ^ 2

theorem image_g009 : toMatrix g009 = m009 := by
  change toMatrix (g008 ^ 2) = _
  have hp : g008 ^ 2 = g008 * g008 := by
    simpa only [pow_one] using (pow_add g008 1 1)
  rw [hp, map_mul, image_g008]
  exact product006

def g010 : Model := g008 ^ 3

theorem image_g010 : toMatrix g010 = m010 := by
  change toMatrix (g008 ^ 3) = _
  have hp : g008 ^ 3 = g008 * g009 := by
    simpa only [g009, pow_one] using (pow_add g008 1 2)
  rw [hp, map_mul, image_g008, image_g009]
  exact product007

def g011 : Model := g007 ^ 2

theorem image_g011 : toMatrix g011 = m011 := by
  change toMatrix (g007 ^ 2) = _
  have hp : g007 ^ 2 = g007 * g007 := by
    simpa only [pow_one] using (pow_add g007 1 1)
  rw [hp, map_mul, image_g007]
  exact product008

def g012 : Model := g007 ^ 3

theorem image_g012 : toMatrix g012 = m012 := by
  change toMatrix (g007 ^ 3) = _
  have hp : g007 ^ 3 = g007 * g011 := by
    simpa only [g011, pow_one] using (pow_add g007 1 2)
  rw [hp, map_mul, image_g007, image_g011]
  exact product009

def g013 : Model := g007 ^ 5

theorem image_g013 : toMatrix g013 = m013 := by
  change toMatrix (g007 ^ 5) = _
  have hp : g007 ^ 5 = g011 * g012 := by
    simpa only [g011, g012, pow_one] using (pow_add g007 2 3)
  rw [hp, map_mul, image_g011, image_g012]
  exact product010

def g014 : Model := g007 ^ 6

theorem image_g014 : toMatrix g014 = m014 := by
  change toMatrix (g007 ^ 6) = _
  have hp : g007 ^ 6 = g012 * g012 := by
    simpa only [g012, pow_one] using (pow_add g007 3 3)
  rw [hp, map_mul, image_g012]
  exact product011

def g015 : Model := g007 ^ 11

theorem image_g015 : toMatrix g015 = m015 := by
  change toMatrix (g007 ^ 11) = _
  have hp : g007 ^ 11 = g013 * g014 := by
    simpa only [g013, g014, pow_one] using (pow_add g007 5 6)
  rw [hp, map_mul, image_g013, image_g014]
  exact product012

def g016 : Model := g007 ^ 22

theorem image_g016 : toMatrix g016 = m016 := by
  change toMatrix (g007 ^ 22) = _
  have hp : g007 ^ 22 = g015 * g015 := by
    simpa only [g015, pow_one] using (pow_add g007 11 11)
  rw [hp, map_mul, image_g015]
  exact product013

def g017 : Model := g003 ^ 6

theorem image_g017 : toMatrix g017 = m017 := by
  change toMatrix (g003 ^ 6) = _
  have hp : g003 ^ 6 = g005 * g005 := by
    simpa only [g005, pow_one] using (pow_add g003 3 3)
  rw [hp, map_mul, image_g005]
  exact product014

def g018 : Model := g003 ^ 4

theorem image_g018 : toMatrix g018 = m018 := by
  change toMatrix (g003 ^ 4) = _
  have hp : g003 ^ 4 = g004 * g004 := by
    simpa only [g004, pow_one] using (pow_add g003 2 2)
  rw [hp, map_mul, image_g004]
  exact product015

def g019 : Model := g003 ^ 7

theorem image_g019 : toMatrix g019 = m019 := by
  change toMatrix (g003 ^ 7) = _
  have hp : g003 ^ 7 = g005 * g018 := by
    simpa only [g005, g018, pow_one] using (pow_add g003 3 4)
  rw [hp, map_mul, image_g005, image_g018]
  exact product016

def g020 : Model := g003 ^ 13

theorem image_g020 : toMatrix g020 = m020 := by
  change toMatrix (g003 ^ 13) = _
  have hp : g003 ^ 13 = g017 * g019 := by
    simpa only [g017, g019, pow_one] using (pow_add g003 6 7)
  rw [hp, map_mul, image_g017, image_g019]
  exact product017

def g021 : Model := g016 * g020

theorem image_g021 : toMatrix g021 = m021 := by
  change toMatrix (g016 * g020) = _
  rw [map_mul, image_g016, image_g020]
  exact product018

def g022 : Model := g007 * g007

theorem image_g022 : toMatrix g022 = m011 := by
  change toMatrix (g007 * g007) = _
  rw [map_mul, image_g007]
  exact product008

def g023 : Model := g021⁻¹

theorem image_g023 : toMatrix g023 = m022 := by
  change toMatrix (g021⁻¹) = _
  apply inv_certificate g021 v021 v022 image_g021
  exact product019.trans identity_matrix

def g024 : Model := g023 * g010

theorem image_g024 : toMatrix g024 = m023 := by
  change toMatrix (g023 * g010) = _
  rw [map_mul, image_g023, image_g010]
  exact product020

def g025 : Model := g010 * g010

theorem image_g025 : toMatrix g025 = m024 := by
  change toMatrix (g010 * g010) = _
  rw [map_mul, image_g010]
  exact product021

def g026 : Model := g024 * g021

theorem image_g026 : toMatrix g026 = m025 := by
  change toMatrix (g024 * g021) = _
  rw [map_mul, image_g024, image_g021]
  exact product022

def g027 : Model := g022⁻¹

theorem image_g027 : toMatrix g027 = m026 := by
  change toMatrix (g022⁻¹) = _
  apply inv_certificate g022 v011 v026 image_g022
  exact product023.trans identity_matrix

def g028 : Model := g027 * g025

theorem image_g028 : toMatrix g028 = m027 := by
  change toMatrix (g027 * g025) = _
  rw [map_mul, image_g027, image_g025]
  exact product024

def g029 : Model := g028 * g022

theorem image_g029 : toMatrix g029 = m028 := by
  change toMatrix (g028 * g022) = _
  rw [map_mul, image_g028, image_g022]
  exact product025

def g030 : Model := g029 * g026

theorem image_g030 : toMatrix g030 = m029 := by
  change toMatrix (g029 * g026) = _
  rw [map_mul, image_g029, image_g026]
  exact product026

def g031 : Model := g026 * g029

theorem image_g031 : toMatrix g031 = m030 := by
  change toMatrix (g026 * g029) = _
  rw [map_mul, image_g026, image_g029]
  exact product027

def g032 : Model := g030 ^ 2

theorem image_g032 : toMatrix g032 = m031 := by
  change toMatrix (g030 ^ 2) = _
  have hp : g030 ^ 2 = g030 * g030 := by
    simpa only [pow_one] using (pow_add g030 1 1)
  rw [hp, map_mul, image_g030]
  exact product028

def g033 : Model := g030 ^ 4

theorem image_g033 : toMatrix g033 = m032 := by
  change toMatrix (g030 ^ 4) = _
  have hp : g030 ^ 4 = g032 * g032 := by
    simpa only [g032, pow_one] using (pow_add g030 2 2)
  rw [hp, map_mul, image_g032]
  exact product029

def g034 : Model := g030 ^ 8

theorem image_g034 : toMatrix g034 = m033 := by
  change toMatrix (g030 ^ 8) = _
  have hp : g030 ^ 8 = g033 * g033 := by
    simpa only [g033, pow_one] using (pow_add g030 4 4)
  rw [hp, map_mul, image_g033]
  exact product030

def g035 : Model := g030 ^ 3

theorem image_g035 : toMatrix g035 = m034 := by
  change toMatrix (g030 ^ 3) = _
  have hp : g030 ^ 3 = g030 * g032 := by
    simpa only [g032, pow_one] using (pow_add g030 1 2)
  rw [hp, map_mul, image_g030, image_g032]
  exact product031

def g036 : Model := g030 ^ 5

theorem image_g036 : toMatrix g036 = m035 := by
  change toMatrix (g030 ^ 5) = _
  have hp : g030 ^ 5 = g032 * g035 := by
    simpa only [g032, g035, pow_one] using (pow_add g030 2 3)
  rw [hp, map_mul, image_g032, image_g035]
  exact product032

def g037 : Model := g030 ^ 9

theorem image_g037 : toMatrix g037 = m036 := by
  change toMatrix (g030 ^ 9) = _
  have hp : g030 ^ 9 = g033 * g036 := by
    simpa only [g033, g036, pow_one] using (pow_add g030 4 5)
  rw [hp, map_mul, image_g033, image_g036]
  exact product033

def g038 : Model := g030 ^ 17

theorem image_g038 : toMatrix g038 = m037 := by
  change toMatrix (g030 ^ 17) = _
  have hp : g030 ^ 17 = g034 * g037 := by
    simpa only [g034, g037, pow_one] using (pow_add g030 8 9)
  rw [hp, map_mul, image_g034, image_g037]
  exact product034

def g039 : Model := g030 ^ 18

theorem image_g039 : toMatrix g039 = m038 := by
  change toMatrix (g030 ^ 18) = _
  have hp : g030 ^ 18 = g037 * g037 := by
    simpa only [g037, pow_one] using (pow_add g030 9 9)
  rw [hp, map_mul, image_g037]
  exact product035

def g040 : Model := g030 ^ 35

theorem image_g040 : toMatrix g040 = m000 := by
  change toMatrix (g030 ^ 35) = _
  have hp : g030 ^ 35 = g038 * g039 := by
    simpa only [g038, g039, pow_one] using (pow_add g030 17 18)
  rw [hp, map_mul, image_g038, image_g039]
  exact product036

theorem image_cycle : matrix cycle = cMatrix := image_g030

theorem image_reverseCycle : matrix reverseCycle = dMatrix := image_g031

theorem cycle_pow : cycle ^ 35 = 1 := by
  apply Subtype.ext
  apply toMatrix_injective
  exact image_g040.trans (identity_matrix.trans (map_one toMatrix).symm)


end Janko4.LocalStructure.SymmetricLinear.NormalFour.Certificate
