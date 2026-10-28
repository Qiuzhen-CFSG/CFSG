module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerRigidity.TwistedCertificate.Products00
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerRigidity.TwistedCertificate.Products01
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerRigidity.TwistedCertificate.Products02
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerRigidity.TwistedCertificate.Products03
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerRigidity.TwistedCertificate.Products04
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerRigidity.TwistedCertificate.Products05
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerRigidity.TwistedCertificate.Products06
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerRigidity.TwistedCertificate.Basic
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Max2Bridge
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalCommutant.Reduction

/-!
# Propagation of the twist through the polynomial words

Source: the actual ATLAS matrices in `Janko4/Model/Data.lean` and the
certified local words in `NormalizerSquares/LocalAction/TwoCoreCentralizer`.
Reproduce with `TwistedCertificate/source/generate_certificate.py`.
All numerical identities are kernel-checked.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerRigidity.TwistedCertificate
open Janko4.GeneratorCertificates Janko4.Simplicity.Elevens.BridgeCertificate

open NormalizerSquares NormalizerSquares.TwoCoreCentralizerData

theorem x_matrix : ((localX : BinaryMatrixˣ) : BinaryMatrix) = m001 := eval_cx
theorem y_matrix : ((localY : BinaryMatrixˣ) : BinaryMatrix) = m002 := eval_cy

theorem commutes000 : m000 * matrixA = matrixA * m000 := by rw [identity_matrix, one_mul, mul_one]

theorem commutes001 : m001 * matrixA = matrixA * m001 := by
  rw [← x_matrix]
  exact NormalizerSquares.CommutantCertificate.localMatrix_commutes_a localX

theorem commutes002 : m002 * matrixA = matrixA * m002 := by
  rw [← y_matrix]
  exact NormalizerSquares.CommutantCertificate.localMatrix_commutes_a localY

theorem twist000 (M : BinaryMatrix)
    (_hx : M * m001 = (matrixA * m001) * M) (_hy : M * m002 = m002 * M) :
    M * m000 = m000 * M := by
  rw [identity_matrix, one_mul, mul_one]

theorem twist001 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (_hy : M * m002 = m002 * M) :
    M * m001 = (matrixA * m001) * M := by
  exact hx

theorem twist002 (M : BinaryMatrix)
    (_hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m002 = m002 * M := by
  exact hy

theorem commutes003 : m003 * matrixA = matrixA * m003 := by
  rw [← product000, mul_assoc, commutes002, ← mul_assoc, commutes001, mul_assoc]

theorem twist003 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m003 = (matrixA * m003) * M := by
  have h := intertwines_mul M matrixA m001 m002 true false
    matrixA_mul_self commutes001 (twist001 M hx hy) hy
  change M * (m001 * m002) = (matrixA * (m001 * m002)) * M at h
  simpa only [product000] using h

theorem commutes004 : m004 * matrixA = matrixA * m004 := by
  rw [← product001, mul_assoc, commutes001, ← mul_assoc, commutes002, mul_assoc]

theorem twist004 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m004 = (matrixA * m004) * M := by
  have h := intertwines_mul M matrixA m002 m001 false true
    matrixA_mul_self commutes002 (twist002 M hx hy) hx
  change M * (m002 * m001) = (matrixA * (m002 * m001)) * M at h
  simpa only [product001] using h

theorem commutes005 : m005 * matrixA = matrixA * m005 := by
  rw [← product002, mul_assoc, commutes002, ← mul_assoc, commutes002, mul_assoc]

theorem twist005 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m005 = m005 * M := by
  have h := intertwines_mul M matrixA m002 m002 false false
    matrixA_mul_self commutes002 (twist002 M hx hy) hy
  change M * (m002 * m002) = (m002 * m002) * M at h
  simpa only [product002] using h

theorem commutes006 : m006 * matrixA = matrixA * m006 := by
  rw [← product003, mul_assoc, commutes001, ← mul_assoc, commutes003, mul_assoc]

theorem twist006 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m006 = m006 * M := by
  have h := intertwines_mul M matrixA m003 m001 true true
    matrixA_mul_self commutes003 (twist003 M hx hy) hx
  change M * (m003 * m001) = (m003 * m001) * M at h
  simpa only [product003] using h

theorem commutes007 : m007 * matrixA = matrixA * m007 := by
  rw [← product004, mul_assoc, commutes002, ← mul_assoc, commutes003, mul_assoc]

theorem twist007 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m007 = (matrixA * m007) * M := by
  have h := intertwines_mul M matrixA m003 m002 true false
    matrixA_mul_self commutes003 (twist003 M hx hy) hy
  change M * (m003 * m002) = (matrixA * (m003 * m002)) * M at h
  simpa only [product004] using h

theorem commutes008 : m008 * matrixA = matrixA * m008 := by
  rw [← product005, mul_assoc, commutes002, ← mul_assoc, commutes004, mul_assoc]

theorem twist008 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m008 = (matrixA * m008) * M := by
  have h := intertwines_mul M matrixA m004 m002 true false
    matrixA_mul_self commutes004 (twist004 M hx hy) hy
  change M * (m004 * m002) = (matrixA * (m004 * m002)) * M at h
  simpa only [product005] using h

theorem commutes009 : m009 * matrixA = matrixA * m009 := by
  rw [← product006, mul_assoc, commutes001, ← mul_assoc, commutes005, mul_assoc]

theorem twist009 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m009 = (matrixA * m009) * M := by
  have h := intertwines_mul M matrixA m005 m001 false true
    matrixA_mul_self commutes005 (twist005 M hx hy) hx
  change M * (m005 * m001) = (matrixA * (m005 * m001)) * M at h
  simpa only [product006] using h

theorem commutes010 : m010 * matrixA = matrixA * m010 := by
  rw [← product007, mul_assoc, commutes002, ← mul_assoc, commutes006, mul_assoc]

theorem twist010 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m010 = m010 * M := by
  have h := intertwines_mul M matrixA m006 m002 false false
    matrixA_mul_self commutes006 (twist006 M hx hy) hy
  change M * (m006 * m002) = (m006 * m002) * M at h
  simpa only [product007] using h

theorem commutes011 : m011 * matrixA = matrixA * m011 := by
  rw [← product008, mul_assoc, commutes001, ← mul_assoc, commutes007, mul_assoc]

theorem twist011 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m011 = m011 * M := by
  have h := intertwines_mul M matrixA m007 m001 true true
    matrixA_mul_self commutes007 (twist007 M hx hy) hx
  change M * (m007 * m001) = (m007 * m001) * M at h
  simpa only [product008] using h

theorem commutes012 : m012 * matrixA = matrixA * m012 := by
  rw [← product009, mul_assoc, commutes001, ← mul_assoc, commutes008, mul_assoc]

theorem twist012 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m012 = m012 * M := by
  have h := intertwines_mul M matrixA m008 m001 true true
    matrixA_mul_self commutes008 (twist008 M hx hy) hx
  change M * (m008 * m001) = (m008 * m001) * M at h
  simpa only [product009] using h

theorem commutes013 : m013 * matrixA = matrixA * m013 := by
  rw [← product010, mul_assoc, commutes002, ← mul_assoc, commutes008, mul_assoc]

theorem twist013 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m013 = (matrixA * m013) * M := by
  have h := intertwines_mul M matrixA m008 m002 true false
    matrixA_mul_self commutes008 (twist008 M hx hy) hy
  change M * (m008 * m002) = (matrixA * (m008 * m002)) * M at h
  simpa only [product010] using h

theorem commutes014 : m014 * matrixA = matrixA * m014 := by
  rw [← product011, mul_assoc, commutes002, ← mul_assoc, commutes009, mul_assoc]

theorem twist014 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m014 = (matrixA * m014) * M := by
  have h := intertwines_mul M matrixA m009 m002 true false
    matrixA_mul_self commutes009 (twist009 M hx hy) hy
  change M * (m009 * m002) = (matrixA * (m009 * m002)) * M at h
  simpa only [product011] using h

theorem commutes015 : m015 * matrixA = matrixA * m015 := by
  rw [← product012, mul_assoc, commutes001, ← mul_assoc, commutes010, mul_assoc]

theorem twist015 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m015 = (matrixA * m015) * M := by
  have h := intertwines_mul M matrixA m010 m001 false true
    matrixA_mul_self commutes010 (twist010 M hx hy) hx
  change M * (m010 * m001) = (matrixA * (m010 * m001)) * M at h
  simpa only [product012] using h

theorem commutes016 : m016 * matrixA = matrixA * m016 := by
  rw [← product013, mul_assoc, commutes002, ← mul_assoc, commutes010, mul_assoc]

theorem twist016 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m016 = m016 * M := by
  have h := intertwines_mul M matrixA m010 m002 false false
    matrixA_mul_self commutes010 (twist010 M hx hy) hy
  change M * (m010 * m002) = (m010 * m002) * M at h
  simpa only [product013] using h

theorem commutes017 : m017 * matrixA = matrixA * m017 := by
  rw [← product014, mul_assoc, commutes002, ← mul_assoc, commutes011, mul_assoc]

theorem twist017 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m017 = m017 * M := by
  have h := intertwines_mul M matrixA m011 m002 false false
    matrixA_mul_self commutes011 (twist011 M hx hy) hy
  change M * (m011 * m002) = (m011 * m002) * M at h
  simpa only [product014] using h

theorem commutes018 : m018 * matrixA = matrixA * m018 := by
  rw [← product015, mul_assoc, commutes002, ← mul_assoc, commutes012, mul_assoc]

theorem twist018 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m018 = m018 * M := by
  have h := intertwines_mul M matrixA m012 m002 false false
    matrixA_mul_self commutes012 (twist012 M hx hy) hy
  change M * (m012 * m002) = (m012 * m002) * M at h
  simpa only [product015] using h

theorem commutes019 : m019 * matrixA = matrixA * m019 := by
  rw [← product016, mul_assoc, commutes001, ← mul_assoc, commutes013, mul_assoc]

theorem twist019 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m019 = m019 * M := by
  have h := intertwines_mul M matrixA m013 m001 true true
    matrixA_mul_self commutes013 (twist013 M hx hy) hx
  change M * (m013 * m001) = (m013 * m001) * M at h
  simpa only [product016] using h

theorem commutes020 : m020 * matrixA = matrixA * m020 := by
  rw [← product017, mul_assoc, commutes001, ← mul_assoc, commutes014, mul_assoc]

theorem twist020 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m020 = m020 * M := by
  have h := intertwines_mul M matrixA m014 m001 true true
    matrixA_mul_self commutes014 (twist014 M hx hy) hx
  change M * (m014 * m001) = (m014 * m001) * M at h
  simpa only [product017] using h

theorem commutes021 : m021 * matrixA = matrixA * m021 := by
  rw [← product018, mul_assoc, commutes002, ← mul_assoc, commutes014, mul_assoc]

theorem twist021 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m021 = (matrixA * m021) * M := by
  have h := intertwines_mul M matrixA m014 m002 true false
    matrixA_mul_self commutes014 (twist014 M hx hy) hy
  change M * (m014 * m002) = (matrixA * (m014 * m002)) * M at h
  simpa only [product018] using h

theorem commutes022 : m022 * matrixA = matrixA * m022 := by
  rw [← product019, mul_assoc, commutes002, ← mul_assoc, commutes015, mul_assoc]

theorem twist022 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m022 = (matrixA * m022) * M := by
  have h := intertwines_mul M matrixA m015 m002 true false
    matrixA_mul_self commutes015 (twist015 M hx hy) hy
  change M * (m015 * m002) = (matrixA * (m015 * m002)) * M at h
  simpa only [product019] using h

theorem commutes023 : m023 * matrixA = matrixA * m023 := by
  rw [← product020, mul_assoc, commutes001, ← mul_assoc, commutes016, mul_assoc]

theorem twist023 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m023 = (matrixA * m023) * M := by
  have h := intertwines_mul M matrixA m016 m001 false true
    matrixA_mul_self commutes016 (twist016 M hx hy) hx
  change M * (m016 * m001) = (matrixA * (m016 * m001)) * M at h
  simpa only [product020] using h

theorem commutes024 : m024 * matrixA = matrixA * m024 := by
  rw [← product021, mul_assoc, commutes001, ← mul_assoc, commutes017, mul_assoc]

theorem twist024 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m024 = (matrixA * m024) * M := by
  have h := intertwines_mul M matrixA m017 m001 false true
    matrixA_mul_self commutes017 (twist017 M hx hy) hx
  change M * (m017 * m001) = (matrixA * (m017 * m001)) * M at h
  simpa only [product021] using h

theorem commutes025 : m025 * matrixA = matrixA * m025 := by
  rw [← product022, mul_assoc, commutes002, ← mul_assoc, commutes017, mul_assoc]

theorem twist025 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m025 = m025 * M := by
  have h := intertwines_mul M matrixA m017 m002 false false
    matrixA_mul_self commutes017 (twist017 M hx hy) hy
  change M * (m017 * m002) = (m017 * m002) * M at h
  simpa only [product022] using h

theorem commutes026 : m026 * matrixA = matrixA * m026 := by
  rw [← product023, mul_assoc, commutes001, ← mul_assoc, commutes018, mul_assoc]

theorem twist026 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m026 = (matrixA * m026) * M := by
  have h := intertwines_mul M matrixA m018 m001 false true
    matrixA_mul_self commutes018 (twist018 M hx hy) hx
  change M * (m018 * m001) = (matrixA * (m018 * m001)) * M at h
  simpa only [product023] using h

theorem commutes027 : m027 * matrixA = matrixA * m027 := by
  rw [← product024, mul_assoc, commutes002, ← mul_assoc, commutes018, mul_assoc]

theorem twist027 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m027 = m027 * M := by
  have h := intertwines_mul M matrixA m018 m002 false false
    matrixA_mul_self commutes018 (twist018 M hx hy) hy
  change M * (m018 * m002) = (m018 * m002) * M at h
  simpa only [product024] using h

theorem commutes028 : m028 * matrixA = matrixA * m028 := by
  rw [← product025, mul_assoc, commutes002, ← mul_assoc, commutes019, mul_assoc]

theorem twist028 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m028 = m028 * M := by
  have h := intertwines_mul M matrixA m019 m002 false false
    matrixA_mul_self commutes019 (twist019 M hx hy) hy
  change M * (m019 * m002) = (m019 * m002) * M at h
  simpa only [product025] using h

theorem commutes029 : m029 * matrixA = matrixA * m029 := by
  rw [← product026, mul_assoc, commutes002, ← mul_assoc, commutes020, mul_assoc]

theorem twist029 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m029 = m029 * M := by
  have h := intertwines_mul M matrixA m020 m002 false false
    matrixA_mul_self commutes020 (twist020 M hx hy) hy
  change M * (m020 * m002) = (m020 * m002) * M at h
  simpa only [product026] using h

theorem commutes030 : m030 * matrixA = matrixA * m030 := by
  rw [← product027, mul_assoc, commutes001, ← mul_assoc, commutes021, mul_assoc]

theorem twist030 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m030 = m030 * M := by
  have h := intertwines_mul M matrixA m021 m001 true true
    matrixA_mul_self commutes021 (twist021 M hx hy) hx
  change M * (m021 * m001) = (m021 * m001) * M at h
  simpa only [product027] using h

theorem commutes031 : m031 * matrixA = matrixA * m031 := by
  rw [← product028, mul_assoc, commutes001, ← mul_assoc, commutes022, mul_assoc]

theorem twist031 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m031 = m031 * M := by
  have h := intertwines_mul M matrixA m022 m001 true true
    matrixA_mul_self commutes022 (twist022 M hx hy) hx
  change M * (m022 * m001) = (m022 * m001) * M at h
  simpa only [product028] using h

theorem commutes032 : m032 * matrixA = matrixA * m032 := by
  rw [← product029, mul_assoc, commutes002, ← mul_assoc, commutes022, mul_assoc]

theorem twist032 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m032 = (matrixA * m032) * M := by
  have h := intertwines_mul M matrixA m022 m002 true false
    matrixA_mul_self commutes022 (twist022 M hx hy) hy
  change M * (m022 * m002) = (matrixA * (m022 * m002)) * M at h
  simpa only [product029] using h

theorem commutes033 : m033 * matrixA = matrixA * m033 := by
  rw [← product030, mul_assoc, commutes002, ← mul_assoc, commutes023, mul_assoc]

theorem twist033 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m033 = (matrixA * m033) * M := by
  have h := intertwines_mul M matrixA m023 m002 true false
    matrixA_mul_self commutes023 (twist023 M hx hy) hy
  change M * (m023 * m002) = (matrixA * (m023 * m002)) * M at h
  simpa only [product030] using h

theorem commutes034 : m034 * matrixA = matrixA * m034 := by
  rw [← product031, mul_assoc, commutes002, ← mul_assoc, commutes024, mul_assoc]

theorem twist034 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m034 = (matrixA * m034) * M := by
  have h := intertwines_mul M matrixA m024 m002 true false
    matrixA_mul_self commutes024 (twist024 M hx hy) hy
  change M * (m024 * m002) = (matrixA * (m024 * m002)) * M at h
  simpa only [product031] using h

theorem commutes035 : m035 * matrixA = matrixA * m035 := by
  rw [← product032, mul_assoc, commutes002, ← mul_assoc, commutes026, mul_assoc]

theorem twist035 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m035 = (matrixA * m035) * M := by
  have h := intertwines_mul M matrixA m026 m002 true false
    matrixA_mul_self commutes026 (twist026 M hx hy) hy
  change M * (m026 * m002) = (matrixA * (m026 * m002)) * M at h
  simpa only [product032] using h

theorem commutes036 : m036 * matrixA = matrixA * m036 := by
  rw [← product033, mul_assoc, commutes001, ← mul_assoc, commutes027, mul_assoc]

theorem twist036 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m036 = (matrixA * m036) * M := by
  have h := intertwines_mul M matrixA m027 m001 false true
    matrixA_mul_self commutes027 (twist027 M hx hy) hx
  change M * (m027 * m001) = (matrixA * (m027 * m001)) * M at h
  simpa only [product033] using h

theorem commutes037 : m037 * matrixA = matrixA * m037 := by
  rw [← product034, mul_assoc, commutes001, ← mul_assoc, commutes028, mul_assoc]

theorem twist037 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m037 = (matrixA * m037) * M := by
  have h := intertwines_mul M matrixA m028 m001 false true
    matrixA_mul_self commutes028 (twist028 M hx hy) hx
  change M * (m028 * m001) = (matrixA * (m028 * m001)) * M at h
  simpa only [product034] using h

theorem commutes038 : m038 * matrixA = matrixA * m038 := by
  rw [← product035, mul_assoc, commutes002, ← mul_assoc, commutes028, mul_assoc]

theorem twist038 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m038 = m038 * M := by
  have h := intertwines_mul M matrixA m028 m002 false false
    matrixA_mul_self commutes028 (twist028 M hx hy) hy
  change M * (m028 * m002) = (m028 * m002) * M at h
  simpa only [product035] using h

theorem commutes039 : m039 * matrixA = matrixA * m039 := by
  rw [← product036, mul_assoc, commutes001, ← mul_assoc, commutes029, mul_assoc]

theorem twist039 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m039 = (matrixA * m039) * M := by
  have h := intertwines_mul M matrixA m029 m001 false true
    matrixA_mul_self commutes029 (twist029 M hx hy) hx
  change M * (m029 * m001) = (matrixA * (m029 * m001)) * M at h
  simpa only [product036] using h

theorem commutes040 : m040 * matrixA = matrixA * m040 := by
  rw [← product037, mul_assoc, commutes002, ← mul_assoc, commutes029, mul_assoc]

theorem twist040 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m040 = m040 * M := by
  have h := intertwines_mul M matrixA m029 m002 false false
    matrixA_mul_self commutes029 (twist029 M hx hy) hy
  change M * (m029 * m002) = (m029 * m002) * M at h
  simpa only [product037] using h

theorem commutes041 : m041 * matrixA = matrixA * m041 := by
  rw [← product038, mul_assoc, commutes002, ← mul_assoc, commutes030, mul_assoc]

theorem twist041 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m041 = m041 * M := by
  have h := intertwines_mul M matrixA m030 m002 false false
    matrixA_mul_self commutes030 (twist030 M hx hy) hy
  change M * (m030 * m002) = (m030 * m002) * M at h
  simpa only [product038] using h

theorem commutes042 : m042 * matrixA = matrixA * m042 := by
  rw [← product039, mul_assoc, commutes002, ← mul_assoc, commutes031, mul_assoc]

theorem twist042 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m042 = m042 * M := by
  have h := intertwines_mul M matrixA m031 m002 false false
    matrixA_mul_self commutes031 (twist031 M hx hy) hy
  change M * (m031 * m002) = (m031 * m002) * M at h
  simpa only [product039] using h

theorem commutes043 : m043 * matrixA = matrixA * m043 := by
  rw [← product040, mul_assoc, commutes001, ← mul_assoc, commutes032, mul_assoc]

theorem twist043 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m043 = m043 * M := by
  have h := intertwines_mul M matrixA m032 m001 true true
    matrixA_mul_self commutes032 (twist032 M hx hy) hx
  change M * (m032 * m001) = (m032 * m001) * M at h
  simpa only [product040] using h

theorem commutes044 : m044 * matrixA = matrixA * m044 := by
  rw [← product041, mul_assoc, commutes001, ← mul_assoc, commutes033, mul_assoc]

theorem twist044 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m044 = m044 * M := by
  have h := intertwines_mul M matrixA m033 m001 true true
    matrixA_mul_self commutes033 (twist033 M hx hy) hx
  change M * (m033 * m001) = (m033 * m001) * M at h
  simpa only [product041] using h

theorem commutes045 : m045 * matrixA = matrixA * m045 := by
  rw [← product042, mul_assoc, commutes001, ← mul_assoc, commutes034, mul_assoc]

theorem twist045 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m045 = m045 * M := by
  have h := intertwines_mul M matrixA m034 m001 true true
    matrixA_mul_self commutes034 (twist034 M hx hy) hx
  change M * (m034 * m001) = (m034 * m001) * M at h
  simpa only [product042] using h

theorem commutes046 : m046 * matrixA = matrixA * m046 := by
  rw [← product043, mul_assoc, commutes002, ← mul_assoc, commutes034, mul_assoc]

theorem twist046 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m046 = (matrixA * m046) * M := by
  have h := intertwines_mul M matrixA m034 m002 true false
    matrixA_mul_self commutes034 (twist034 M hx hy) hy
  change M * (m034 * m002) = (matrixA * (m034 * m002)) * M at h
  simpa only [product043] using h

theorem commutes047 : m047 * matrixA = matrixA * m047 := by
  rw [← product044, mul_assoc, commutes001, ← mul_assoc, commutes035, mul_assoc]

theorem twist047 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m047 = m047 * M := by
  have h := intertwines_mul M matrixA m035 m001 true true
    matrixA_mul_self commutes035 (twist035 M hx hy) hx
  change M * (m035 * m001) = (m035 * m001) * M at h
  simpa only [product044] using h

theorem commutes048 : m048 * matrixA = matrixA * m048 := by
  rw [← product045, mul_assoc, commutes002, ← mul_assoc, commutes035, mul_assoc]

theorem twist048 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m048 = (matrixA * m048) * M := by
  have h := intertwines_mul M matrixA m035 m002 true false
    matrixA_mul_self commutes035 (twist035 M hx hy) hy
  change M * (m035 * m002) = (matrixA * (m035 * m002)) * M at h
  simpa only [product045] using h

theorem commutes049 : m049 * matrixA = matrixA * m049 := by
  rw [← product046, mul_assoc, commutes002, ← mul_assoc, commutes036, mul_assoc]

theorem twist049 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m049 = (matrixA * m049) * M := by
  have h := intertwines_mul M matrixA m036 m002 true false
    matrixA_mul_self commutes036 (twist036 M hx hy) hy
  change M * (m036 * m002) = (matrixA * (m036 * m002)) * M at h
  simpa only [product046] using h

theorem commutes050 : m050 * matrixA = matrixA * m050 := by
  rw [← product047, mul_assoc, commutes002, ← mul_assoc, commutes037, mul_assoc]

theorem twist050 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m050 = (matrixA * m050) * M := by
  have h := intertwines_mul M matrixA m037 m002 true false
    matrixA_mul_self commutes037 (twist037 M hx hy) hy
  change M * (m037 * m002) = (matrixA * (m037 * m002)) * M at h
  simpa only [product047] using h

theorem commutes051 : m051 * matrixA = matrixA * m051 := by
  rw [← product048, mul_assoc, commutes001, ← mul_assoc, commutes038, mul_assoc]

theorem twist051 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m051 = (matrixA * m051) * M := by
  have h := intertwines_mul M matrixA m038 m001 false true
    matrixA_mul_self commutes038 (twist038 M hx hy) hx
  change M * (m038 * m001) = (matrixA * (m038 * m001)) * M at h
  simpa only [product048] using h

theorem commutes052 : m052 * matrixA = matrixA * m052 := by
  rw [← product049, mul_assoc, commutes002, ← mul_assoc, commutes039, mul_assoc]

theorem twist052 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m052 = (matrixA * m052) * M := by
  have h := intertwines_mul M matrixA m039 m002 true false
    matrixA_mul_self commutes039 (twist039 M hx hy) hy
  change M * (m039 * m002) = (matrixA * (m039 * m002)) * M at h
  simpa only [product049] using h

theorem commutes053 : m053 * matrixA = matrixA * m053 := by
  rw [← product050, mul_assoc, commutes001, ← mul_assoc, commutes040, mul_assoc]

theorem twist053 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m053 = (matrixA * m053) * M := by
  have h := intertwines_mul M matrixA m040 m001 false true
    matrixA_mul_self commutes040 (twist040 M hx hy) hx
  change M * (m040 * m001) = (matrixA * (m040 * m001)) * M at h
  simpa only [product050] using h

theorem commutes054 : m054 * matrixA = matrixA * m054 := by
  rw [← product051, mul_assoc, commutes001, ← mul_assoc, commutes041, mul_assoc]

theorem twist054 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m054 = (matrixA * m054) * M := by
  have h := intertwines_mul M matrixA m041 m001 false true
    matrixA_mul_self commutes041 (twist041 M hx hy) hx
  change M * (m041 * m001) = (matrixA * (m041 * m001)) * M at h
  simpa only [product051] using h

theorem commutes055 : m055 * matrixA = matrixA * m055 := by
  rw [← product052, mul_assoc, commutes002, ← mul_assoc, commutes041, mul_assoc]

theorem twist055 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m055 = m055 * M := by
  have h := intertwines_mul M matrixA m041 m002 false false
    matrixA_mul_self commutes041 (twist041 M hx hy) hy
  change M * (m041 * m002) = (m041 * m002) * M at h
  simpa only [product052] using h

theorem commutes056 : m056 * matrixA = matrixA * m056 := by
  rw [← product053, mul_assoc, commutes002, ← mul_assoc, commutes042, mul_assoc]

theorem twist056 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m056 = m056 * M := by
  have h := intertwines_mul M matrixA m042 m002 false false
    matrixA_mul_self commutes042 (twist042 M hx hy) hy
  change M * (m042 * m002) = (m042 * m002) * M at h
  simpa only [product053] using h

theorem commutes057 : m057 * matrixA = matrixA * m057 := by
  rw [← product054, mul_assoc, commutes002, ← mul_assoc, commutes043, mul_assoc]

theorem twist057 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m057 = m057 * M := by
  have h := intertwines_mul M matrixA m043 m002 false false
    matrixA_mul_self commutes043 (twist043 M hx hy) hy
  change M * (m043 * m002) = (m043 * m002) * M at h
  simpa only [product054] using h

theorem commutes058 : m058 * matrixA = matrixA * m058 := by
  rw [← product055, mul_assoc, commutes001, ← mul_assoc, commutes046, mul_assoc]

theorem twist058 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m058 = m058 * M := by
  have h := intertwines_mul M matrixA m046 m001 true true
    matrixA_mul_self commutes046 (twist046 M hx hy) hx
  change M * (m046 * m001) = (m046 * m001) * M at h
  simpa only [product055] using h

theorem commutes059 : m059 * matrixA = matrixA * m059 := by
  rw [← product056, mul_assoc, commutes001, ← mul_assoc, commutes048, mul_assoc]

theorem twist059 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m059 = m059 * M := by
  have h := intertwines_mul M matrixA m048 m001 true true
    matrixA_mul_self commutes048 (twist048 M hx hy) hx
  change M * (m048 * m001) = (m048 * m001) * M at h
  simpa only [product056] using h

theorem commutes060 : m060 * matrixA = matrixA * m060 := by
  rw [← product057, mul_assoc, commutes001, ← mul_assoc, commutes049, mul_assoc]

theorem twist060 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m060 = m060 * M := by
  have h := intertwines_mul M matrixA m049 m001 true true
    matrixA_mul_self commutes049 (twist049 M hx hy) hx
  change M * (m049 * m001) = (m049 * m001) * M at h
  simpa only [product057] using h

theorem commutes061 : m061 * matrixA = matrixA * m061 := by
  rw [← product058, mul_assoc, commutes002, ← mul_assoc, commutes049, mul_assoc]

theorem twist061 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m061 = (matrixA * m061) * M := by
  have h := intertwines_mul M matrixA m049 m002 true false
    matrixA_mul_self commutes049 (twist049 M hx hy) hy
  change M * (m049 * m002) = (matrixA * (m049 * m002)) * M at h
  simpa only [product058] using h

theorem commutes062 : m062 * matrixA = matrixA * m062 := by
  rw [← product059, mul_assoc, commutes002, ← mul_assoc, commutes050, mul_assoc]

theorem twist062 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m062 = (matrixA * m062) * M := by
  have h := intertwines_mul M matrixA m050 m002 true false
    matrixA_mul_self commutes050 (twist050 M hx hy) hy
  change M * (m050 * m002) = (matrixA * (m050 * m002)) * M at h
  simpa only [product059] using h

theorem commutes063 : m063 * matrixA = matrixA * m063 := by
  rw [← product060, mul_assoc, commutes002, ← mul_assoc, commutes051, mul_assoc]

theorem twist063 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m063 = (matrixA * m063) * M := by
  have h := intertwines_mul M matrixA m051 m002 true false
    matrixA_mul_self commutes051 (twist051 M hx hy) hy
  change M * (m051 * m002) = (matrixA * (m051 * m002)) * M at h
  simpa only [product060] using h

theorem commutes064 : m064 * matrixA = matrixA * m064 := by
  rw [← product061, mul_assoc, commutes002, ← mul_assoc, commutes052, mul_assoc]

theorem twist064 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m064 = (matrixA * m064) * M := by
  have h := intertwines_mul M matrixA m052 m002 true false
    matrixA_mul_self commutes052 (twist052 M hx hy) hy
  change M * (m052 * m002) = (matrixA * (m052 * m002)) * M at h
  simpa only [product061] using h

theorem commutes065 : m065 * matrixA = matrixA * m065 := by
  rw [← product062, mul_assoc, commutes002, ← mul_assoc, commutes053, mul_assoc]

theorem twist065 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m065 = (matrixA * m065) * M := by
  have h := intertwines_mul M matrixA m053 m002 true false
    matrixA_mul_self commutes053 (twist053 M hx hy) hy
  change M * (m053 * m002) = (matrixA * (m053 * m002)) * M at h
  simpa only [product062] using h

theorem commutes066 : m066 * matrixA = matrixA * m066 := by
  rw [← product063, mul_assoc, commutes002, ← mul_assoc, commutes054, mul_assoc]

theorem twist066 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m066 = (matrixA * m066) * M := by
  have h := intertwines_mul M matrixA m054 m002 true false
    matrixA_mul_self commutes054 (twist054 M hx hy) hy
  change M * (m054 * m002) = (matrixA * (m054 * m002)) * M at h
  simpa only [product063] using h

theorem commutes067 : m067 * matrixA = matrixA * m067 := by
  rw [← product064, mul_assoc, commutes001, ← mul_assoc, commutes055, mul_assoc]

theorem twist067 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m067 = (matrixA * m067) * M := by
  have h := intertwines_mul M matrixA m055 m001 false true
    matrixA_mul_self commutes055 (twist055 M hx hy) hx
  change M * (m055 * m001) = (matrixA * (m055 * m001)) * M at h
  simpa only [product064] using h

theorem commutes068 : m068 * matrixA = matrixA * m068 := by
  rw [← product065, mul_assoc, commutes001, ← mul_assoc, commutes056, mul_assoc]

theorem twist068 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m068 = (matrixA * m068) * M := by
  have h := intertwines_mul M matrixA m056 m001 false true
    matrixA_mul_self commutes056 (twist056 M hx hy) hx
  change M * (m056 * m001) = (matrixA * (m056 * m001)) * M at h
  simpa only [product065] using h

theorem commutes069 : m069 * matrixA = matrixA * m069 := by
  rw [← product066, mul_assoc, commutes002, ← mul_assoc, commutes057, mul_assoc]

theorem twist069 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m069 = m069 * M := by
  have h := intertwines_mul M matrixA m057 m002 false false
    matrixA_mul_self commutes057 (twist057 M hx hy) hy
  change M * (m057 * m002) = (m057 * m002) * M at h
  simpa only [product066] using h

theorem commutes070 : m070 * matrixA = matrixA * m070 := by
  rw [← product067, mul_assoc, commutes002, ← mul_assoc, commutes058, mul_assoc]

theorem twist070 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m070 = m070 * M := by
  have h := intertwines_mul M matrixA m058 m002 false false
    matrixA_mul_self commutes058 (twist058 M hx hy) hy
  change M * (m058 * m002) = (m058 * m002) * M at h
  simpa only [product067] using h

theorem commutes071 : m071 * matrixA = matrixA * m071 := by
  rw [← product068, mul_assoc, commutes002, ← mul_assoc, commutes059, mul_assoc]

theorem twist071 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m071 = m071 * M := by
  have h := intertwines_mul M matrixA m059 m002 false false
    matrixA_mul_self commutes059 (twist059 M hx hy) hy
  change M * (m059 * m002) = (m059 * m002) * M at h
  simpa only [product068] using h

theorem commutes072 : m072 * matrixA = matrixA * m072 := by
  rw [← product069, mul_assoc, commutes002, ← mul_assoc, commutes060, mul_assoc]

theorem twist072 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m072 = m072 * M := by
  have h := intertwines_mul M matrixA m060 m002 false false
    matrixA_mul_self commutes060 (twist060 M hx hy) hy
  change M * (m060 * m002) = (m060 * m002) * M at h
  simpa only [product069] using h

theorem commutes073 : m073 * matrixA = matrixA * m073 := by
  rw [← product070, mul_assoc, commutes001, ← mul_assoc, commutes062, mul_assoc]

theorem twist073 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m073 = m073 * M := by
  have h := intertwines_mul M matrixA m062 m001 true true
    matrixA_mul_self commutes062 (twist062 M hx hy) hx
  change M * (m062 * m001) = (m062 * m001) * M at h
  simpa only [product070] using h

theorem commutes074 : m074 * matrixA = matrixA * m074 := by
  rw [← product071, mul_assoc, commutes002, ← mul_assoc, commutes063, mul_assoc]

theorem twist074 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m074 = (matrixA * m074) * M := by
  have h := intertwines_mul M matrixA m063 m002 true false
    matrixA_mul_self commutes063 (twist063 M hx hy) hy
  change M * (m063 * m002) = (matrixA * (m063 * m002)) * M at h
  simpa only [product071] using h

theorem commutes075 : m075 * matrixA = matrixA * m075 := by
  rw [← product072, mul_assoc, commutes001, ← mul_assoc, commutes064, mul_assoc]

theorem twist075 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m075 = m075 * M := by
  have h := intertwines_mul M matrixA m064 m001 true true
    matrixA_mul_self commutes064 (twist064 M hx hy) hx
  change M * (m064 * m001) = (m064 * m001) * M at h
  simpa only [product072] using h

theorem commutes076 : m076 * matrixA = matrixA * m076 := by
  rw [← product073, mul_assoc, commutes002, ← mul_assoc, commutes065, mul_assoc]

theorem twist076 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m076 = (matrixA * m076) * M := by
  have h := intertwines_mul M matrixA m065 m002 true false
    matrixA_mul_self commutes065 (twist065 M hx hy) hy
  change M * (m065 * m002) = (matrixA * (m065 * m002)) * M at h
  simpa only [product073] using h

theorem commutes077 : m077 * matrixA = matrixA * m077 := by
  rw [← product074, mul_assoc, commutes002, ← mul_assoc, commutes068, mul_assoc]

theorem twist077 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m077 = (matrixA * m077) * M := by
  have h := intertwines_mul M matrixA m068 m002 true false
    matrixA_mul_self commutes068 (twist068 M hx hy) hy
  change M * (m068 * m002) = (matrixA * (m068 * m002)) * M at h
  simpa only [product074] using h

theorem commutes078 : m078 * matrixA = matrixA * m078 := by
  rw [← product075, mul_assoc, commutes001, ← mul_assoc, commutes070, mul_assoc]

theorem twist078 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m078 = (matrixA * m078) * M := by
  have h := intertwines_mul M matrixA m070 m001 false true
    matrixA_mul_self commutes070 (twist070 M hx hy) hx
  change M * (m070 * m001) = (matrixA * (m070 * m001)) * M at h
  simpa only [product075] using h

theorem commutes079 : m079 * matrixA = matrixA * m079 := by
  rw [← product076, mul_assoc, commutes001, ← mul_assoc, commutes074, mul_assoc]

theorem twist079 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m079 = m079 * M := by
  have h := intertwines_mul M matrixA m074 m001 true true
    matrixA_mul_self commutes074 (twist074 M hx hy) hx
  change M * (m074 * m001) = (m074 * m001) * M at h
  simpa only [product076] using h

theorem commutes080 : m080 * matrixA = matrixA * m080 := by
  rw [← product077, mul_assoc, commutes001, ← mul_assoc, commutes076, mul_assoc]

theorem twist080 (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * m080 = m080 * M := by
  have h := intertwines_mul M matrixA m076 m001 true true
    matrixA_mul_self commutes076 (twist076 M hx hy) hx
  change M * (m076 * m001) = (m076 * m001) * M at h
  simpa only [product077] using h

theorem even_intertwines (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * evenPolynomial = evenPolynomial * M := by
  change M * (m010 + (m042 + (m056 + (m069 + (m016 + (m044 + (m045 + (m058 + (m025 + (m012 + (m047 + (m059 + (m071 + (m072 + (m019 + (m073 + (m079 + (m075 + (m040 + (m080 + 0)))))))))))))))))))) = (m010 + (m042 + (m056 + (m069 + (m016 + (m044 + (m045 + (m058 + (m025 + (m012 + (m047 + (m059 + (m071 + (m072 + (m019 + (m073 + (m079 + (m075 + (m040 + (m080 + 0)))))))))))))))))))) * M
  simp only [mul_add, add_mul, mul_zero, zero_mul, twist010 M hx hy, twist042 M hx hy, twist056 M hx hy, twist069 M hx hy, twist016 M hx hy, twist044 M hx hy, twist045 M hx hy, twist058 M hx hy, twist025 M hx hy, twist012 M hx hy, twist047 M hx hy, twist059 M hx hy, twist071 M hx hy, twist072 M hx hy, twist019 M hx hy, twist073 M hx hy, twist079 M hx hy, twist075 M hx hy, twist040 M hx hy, twist080 M hx hy]

theorem odd_intertwines (M : BinaryMatrix)
    (hx : M * m001 = (matrixA * m001) * M) (hy : M * m002 = m002 * M) :
    M * oddPolynomial = (matrixA * oddPolynomial) * M := by
  change M * (m022 + (m068 + (m077 + (m032 + (m033 + (m007 + (m024 + (m034 + (m046 + (m078 + (m008 + (m026 + (m048 + (m061 + (m013 + (m051 + (m063 + (m074 + (m009 + (m014 + (m039 + (m053 + (m065 + (m076 + (m021 + (m054 + (m066 + (m067 + 0)))))))))))))))))))))))))))) = (matrixA * (m022 + (m068 + (m077 + (m032 + (m033 + (m007 + (m024 + (m034 + (m046 + (m078 + (m008 + (m026 + (m048 + (m061 + (m013 + (m051 + (m063 + (m074 + (m009 + (m014 + (m039 + (m053 + (m065 + (m076 + (m021 + (m054 + (m066 + (m067 + 0))))))))))))))))))))))))))))) * M
  simp only [mul_add, add_mul, mul_zero, zero_mul, twist022 M hx hy, twist068 M hx hy, twist077 M hx hy, twist032 M hx hy, twist033 M hx hy, twist007 M hx hy, twist024 M hx hy, twist034 M hx hy, twist046 M hx hy, twist078 M hx hy, twist008 M hx hy, twist026 M hx hy, twist048 M hx hy, twist061 M hx hy, twist013 M hx hy, twist051 M hx hy, twist063 M hx hy, twist074 M hx hy, twist009 M hx hy, twist014 M hx hy, twist039 M hx hy, twist053 M hx hy, twist065 M hx hy, twist076 M hx hy, twist021 M hx hy, twist054 M hx hy, twist066 M hx hy, twist067 M hx hy]

end Janko4.OuterReduction.FixedGenerator.NormalizerRigidity.TwistedCertificate
