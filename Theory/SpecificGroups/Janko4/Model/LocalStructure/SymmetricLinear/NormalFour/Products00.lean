module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.NormalFour.Data

/-!
# Checked products for the max4 obstruction

Source: ATLAS `J4G1-f2r112B0` and `J4G1-max4W1`, as attributed in
`Model/Data.lean` and `SymmetricLinear/Model.lean`. Reproduce using
`NormalFour/source/generate.py`. All numerical equalities are kernel checked.
-/

@[expose] public section
namespace Janko4.LocalStructure.SymmetricLinear.NormalFour.Certificate
open GeneratorCertificates Simplicity.Elevens.BridgeCertificate Matrix

set_option maxRecDepth 10000 in
theorem product000 : m001 * m002 = m003 :=
  product_lists l001 l002 l003 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product001 : m003 * m003 = m004 :=
  product_lists l003 l003 l004 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product002 : m003 * m004 = m005 :=
  product_lists l003 l004 l005 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product003 : m005 * m002 = m006 :=
  product_lists l005 l002 l006 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product004 : m002 * m001 = m007 :=
  product_lists l002 l001 l007 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product005 : m006 * m002 = m008 :=
  product_lists l006 l002 l008 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product006 : m008 * m008 = m009 :=
  product_lists l008 l008 l009 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product007 : m008 * m009 = m010 :=
  product_lists l008 l009 l010 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product008 : m007 * m007 = m011 :=
  product_lists l007 l007 l011 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product009 : m007 * m011 = m012 :=
  product_lists l007 l011 l012 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product010 : m011 * m012 = m013 :=
  product_lists l011 l012 l013 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product011 : m012 * m012 = m014 :=
  product_lists l012 l012 l014 rfl rfl rfl (by decide +kernel)


end Janko4.LocalStructure.SymmetricLinear.NormalFour.Certificate
