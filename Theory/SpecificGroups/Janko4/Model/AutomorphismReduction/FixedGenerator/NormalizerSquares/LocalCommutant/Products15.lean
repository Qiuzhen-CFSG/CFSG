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
theorem product180 : m080 * m009 = m150 :=
  product_lists l080 l009 l150 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product181 : m080 * m025 = m151 :=
  product_lists l080 l025 l151 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product182 : m080 * m034 = m152 :=
  product_lists l080 l034 l152 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product183 : m080 * m051 = m153 :=
  product_lists l080 l051 l153 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product184 : m080 * m062 = m154 :=
  product_lists l080 l062 l154 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product185 : m080 * m075 = m155 :=
  product_lists l080 l075 l155 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product186 : m081 * m009 = m156 :=
  product_lists l081 l009 l156 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product187 : m081 * m025 = m157 :=
  product_lists l081 l025 l157 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product188 : m081 * m034 = m158 :=
  product_lists l081 l034 l158 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product189 : m081 * m062 = m159 :=
  product_lists l081 l062 l159 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product190 : m081 * m075 = m160 :=
  product_lists l081 l075 l160 rfl rfl rfl (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product191 : m082 * m009 = m161 :=
  product_lists l082 l009 l161 rfl rfl rfl (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.CommutantCertificate
