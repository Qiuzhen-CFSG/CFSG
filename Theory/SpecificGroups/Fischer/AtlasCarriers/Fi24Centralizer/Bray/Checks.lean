module
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi24Centralizer.Bray.Tables
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi24Centralizer.Networks.BrayWords
/-!
# Kernel certificates for the literal Bray products

The checks use the certified switching networks for the original generators.
Checkpoint tables bound each reduction by a single Bray-product pass (at most
814 stages), whose measured peak is 6.3GB. Checks are elaborated serially to
avoid multiplying that memory use; no reduction or recursion limit is raised.
-/
@[expose] public section
namespace Sporadic.Fischer.Fi24Prime.CentralizerSection.Bray
open Theory.GroupAction.PackedPermutation Networks

set_option Elab.async false in
theorem runK0p1 : run 19 netK0 (ramp 19 524288) = tableK0p1 := by decide +kernel

set_option Elab.async false in
theorem runK0p2 : run 19 netK0 tableK0p1 = tableK0p2 := by decide +kernel

set_option Elab.async false in
theorem runK0p3 : run 19 netK0 tableK0p2 = tableK0p3 := by decide +kernel

set_option Elab.async false in
theorem runK0p4 : run 19 netK0 tableK0p3 = tableK0p4 := by decide +kernel

set_option Elab.async false in
theorem runK0p5 : run 19 netK0 tableK0p4 = ramp 19 524288 := by decide +kernel

set_option Elab.async false in
theorem runG0 : run 19 netG0 (ramp 19 524288) = tableG0 := by decide +kernel
set_option Elab.async false in
theorem runGK0 : run 19 netK0 tableG0 = tableGK0 := by decide +kernel
set_option Elab.async false in
theorem runH0 : run 19 netK0 tableGK0 = tableH0 := by decide +kernel

set_option Elab.async false in
theorem runK1p1 : run 19 netK1 (ramp 19 524288) = tableK1p1 := by decide +kernel

set_option Elab.async false in
theorem runK1p2 : run 19 netK1 tableK1p1 = tableK1p2 := by decide +kernel

set_option Elab.async false in
theorem runK1p3 : run 19 netK1 tableK1p2 = tableK1p3 := by decide +kernel

set_option Elab.async false in
theorem runK1p4 : run 19 netK1 tableK1p3 = tableK1p4 := by decide +kernel

set_option Elab.async false in
theorem runK1p5 : run 19 netK1 tableK1p4 = ramp 19 524288 := by decide +kernel

set_option Elab.async false in
theorem runG1 : run 19 netG1 (ramp 19 524288) = tableG1 := by decide +kernel
set_option Elab.async false in
theorem runGK1 : run 19 netK1 tableG1 = tableGK1 := by decide +kernel
set_option Elab.async false in
theorem runH1 : run 19 netK1 tableGK1 = tableH1 := by decide +kernel
end Sporadic.Fischer.Fi24Prime.CentralizerSection.Bray
