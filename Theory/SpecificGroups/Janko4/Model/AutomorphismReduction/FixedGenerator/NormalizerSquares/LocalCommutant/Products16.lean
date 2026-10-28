module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalCommutant.Data

/-!
# Checked products for the J₄ local commutant

List row multiplication is transferred to ordinary matrix multiplication.

Source matrices: `Janko4/Model/Data.lean` (ATLAS J4G1-f2r112B0).
Reproduction: `LocalCommutant/source/generate.py`; candidate data are untrusted.
Every numerical identity below is checked by the Lean kernel.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.CommutantCertificate
open GeneratorCertificates Janko4.Simplicity.Elevens.BridgeCertificate

set_option Elab.async false

set_option maxRecDepth 10000 in
theorem product192 : m082 * m016 = m162 :=
  product_lists l082 l016 l162 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product193 : m082 * m025 = m163 :=
  product_lists l082 l025 l163 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product194 : m082 * m034 = m164 :=
  product_lists l082 l034 l164 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product195 : m082 * m017 = m165 :=
  product_lists l082 l017 l165 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product196 : m082 * m051 = m166 :=
  product_lists l082 l051 l166 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product197 : m082 * m062 = m167 :=
  product_lists l082 l062 l167 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product198 : m082 * m075 = m168 :=
  product_lists l082 l075 l168 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product199 : m083 * m009 = m169 :=
  product_lists l083 l009 l169 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product200 : m083 * m016 = m170 :=
  product_lists l083 l016 l170 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product201 : m083 * m025 = m171 :=
  product_lists l083 l025 l171 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product202 : m083 * m034 = m172 :=
  product_lists l083 l034 l172 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product203 : m083 * m017 = m173 :=
  product_lists l083 l017 l173 rfl rfl rfl (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.CommutantCertificate
