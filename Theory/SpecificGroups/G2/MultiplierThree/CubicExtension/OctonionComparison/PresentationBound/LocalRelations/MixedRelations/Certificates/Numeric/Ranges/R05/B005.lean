module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1114112, 1122304).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B005
private theorem c1114112 : checkChunk 1114112 128 = true := by decide +kernel
private theorem c1114240 : checkChunk 1114240 128 = true := by decide +kernel
private theorem c1114368 : checkChunk 1114368 128 = true := by decide +kernel
private theorem c1114496 : checkChunk 1114496 128 = true := by decide +kernel
private theorem c1114624 : checkChunk 1114624 128 = true := by decide +kernel
private theorem c1114752 : checkChunk 1114752 128 = true := by decide +kernel
private theorem c1114880 : checkChunk 1114880 128 = true := by decide +kernel
private theorem c1115008 : checkChunk 1115008 128 = true := by decide +kernel
private theorem c1115136 : checkChunk 1115136 128 = true := by decide +kernel
private theorem c1115264 : checkChunk 1115264 128 = true := by decide +kernel
private theorem c1115392 : checkChunk 1115392 128 = true := by decide +kernel
private theorem c1115520 : checkChunk 1115520 128 = true := by decide +kernel
private theorem c1115648 : checkChunk 1115648 128 = true := by decide +kernel
private theorem c1115776 : checkChunk 1115776 128 = true := by decide +kernel
private theorem c1115904 : checkChunk 1115904 128 = true := by decide +kernel
private theorem c1116032 : checkChunk 1116032 128 = true := by decide +kernel
private theorem c1116160 : checkChunk 1116160 128 = true := by decide +kernel
private theorem c1116288 : checkChunk 1116288 128 = true := by decide +kernel
private theorem c1116416 : checkChunk 1116416 128 = true := by decide +kernel
private theorem c1116544 : checkChunk 1116544 128 = true := by decide +kernel
private theorem c1116672 : checkChunk 1116672 128 = true := by decide +kernel
private theorem c1116800 : checkChunk 1116800 128 = true := by decide +kernel
private theorem c1116928 : checkChunk 1116928 128 = true := by decide +kernel
private theorem c1117056 : checkChunk 1117056 128 = true := by decide +kernel
private theorem c1117184 : checkChunk 1117184 128 = true := by decide +kernel
private theorem c1117312 : checkChunk 1117312 128 = true := by decide +kernel
private theorem c1117440 : checkChunk 1117440 128 = true := by decide +kernel
private theorem c1117568 : checkChunk 1117568 128 = true := by decide +kernel
private theorem c1117696 : checkChunk 1117696 128 = true := by decide +kernel
private theorem c1117824 : checkChunk 1117824 128 = true := by decide +kernel
private theorem c1117952 : checkChunk 1117952 128 = true := by decide +kernel
private theorem c1118080 : checkChunk 1118080 128 = true := by decide +kernel
private theorem c1118208 : checkChunk 1118208 128 = true := by decide +kernel
private theorem c1118336 : checkChunk 1118336 128 = true := by decide +kernel
private theorem c1118464 : checkChunk 1118464 128 = true := by decide +kernel
private theorem c1118592 : checkChunk 1118592 128 = true := by decide +kernel
private theorem c1118720 : checkChunk 1118720 128 = true := by decide +kernel
private theorem c1118848 : checkChunk 1118848 128 = true := by decide +kernel
private theorem c1118976 : checkChunk 1118976 128 = true := by decide +kernel
private theorem c1119104 : checkChunk 1119104 128 = true := by decide +kernel
private theorem c1119232 : checkChunk 1119232 128 = true := by decide +kernel
private theorem c1119360 : checkChunk 1119360 128 = true := by decide +kernel
private theorem c1119488 : checkChunk 1119488 128 = true := by decide +kernel
private theorem c1119616 : checkChunk 1119616 128 = true := by decide +kernel
private theorem c1119744 : checkChunk 1119744 128 = true := by decide +kernel
private theorem c1119872 : checkChunk 1119872 128 = true := by decide +kernel
private theorem c1120000 : checkChunk 1120000 128 = true := by decide +kernel
private theorem c1120128 : checkChunk 1120128 128 = true := by decide +kernel
private theorem c1120256 : checkChunk 1120256 128 = true := by decide +kernel
private theorem c1120384 : checkChunk 1120384 128 = true := by decide +kernel
private theorem c1120512 : checkChunk 1120512 128 = true := by decide +kernel
private theorem c1120640 : checkChunk 1120640 128 = true := by decide +kernel
private theorem c1120768 : checkChunk 1120768 128 = true := by decide +kernel
private theorem c1120896 : checkChunk 1120896 128 = true := by decide +kernel
private theorem c1121024 : checkChunk 1121024 128 = true := by decide +kernel
private theorem c1121152 : checkChunk 1121152 128 = true := by decide +kernel
private theorem c1121280 : checkChunk 1121280 128 = true := by decide +kernel
private theorem c1121408 : checkChunk 1121408 128 = true := by decide +kernel
private theorem c1121536 : checkChunk 1121536 128 = true := by decide +kernel
private theorem c1121664 : checkChunk 1121664 128 = true := by decide +kernel
private theorem c1121792 : checkChunk 1121792 128 = true := by decide +kernel
private theorem c1121920 : checkChunk 1121920 128 = true := by decide +kernel
private theorem c1122048 : checkChunk 1122048 128 = true := by decide +kernel
private theorem c1122176 : checkChunk 1122176 128 = true := by decide +kernel

public theorem checked : Checked 1114112 1122304 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1114112 128 c1114112) (checkChunk_sound 1114240 128 c1114240)) (Checked.append (checkChunk_sound 1114368 128 c1114368) (checkChunk_sound 1114496 128 c1114496))) (Checked.append (Checked.append (checkChunk_sound 1114624 128 c1114624) (checkChunk_sound 1114752 128 c1114752)) (Checked.append (checkChunk_sound 1114880 128 c1114880) (checkChunk_sound 1115008 128 c1115008)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1115136 128 c1115136) (checkChunk_sound 1115264 128 c1115264)) (Checked.append (checkChunk_sound 1115392 128 c1115392) (checkChunk_sound 1115520 128 c1115520))) (Checked.append (Checked.append (checkChunk_sound 1115648 128 c1115648) (checkChunk_sound 1115776 128 c1115776)) (Checked.append (checkChunk_sound 1115904 128 c1115904) (checkChunk_sound 1116032 128 c1116032))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1116160 128 c1116160) (checkChunk_sound 1116288 128 c1116288)) (Checked.append (checkChunk_sound 1116416 128 c1116416) (checkChunk_sound 1116544 128 c1116544))) (Checked.append (Checked.append (checkChunk_sound 1116672 128 c1116672) (checkChunk_sound 1116800 128 c1116800)) (Checked.append (checkChunk_sound 1116928 128 c1116928) (checkChunk_sound 1117056 128 c1117056)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1117184 128 c1117184) (checkChunk_sound 1117312 128 c1117312)) (Checked.append (checkChunk_sound 1117440 128 c1117440) (checkChunk_sound 1117568 128 c1117568))) (Checked.append (Checked.append (checkChunk_sound 1117696 128 c1117696) (checkChunk_sound 1117824 128 c1117824)) (Checked.append (checkChunk_sound 1117952 128 c1117952) (checkChunk_sound 1118080 128 c1118080)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1118208 128 c1118208) (checkChunk_sound 1118336 128 c1118336)) (Checked.append (checkChunk_sound 1118464 128 c1118464) (checkChunk_sound 1118592 128 c1118592))) (Checked.append (Checked.append (checkChunk_sound 1118720 128 c1118720) (checkChunk_sound 1118848 128 c1118848)) (Checked.append (checkChunk_sound 1118976 128 c1118976) (checkChunk_sound 1119104 128 c1119104)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1119232 128 c1119232) (checkChunk_sound 1119360 128 c1119360)) (Checked.append (checkChunk_sound 1119488 128 c1119488) (checkChunk_sound 1119616 128 c1119616))) (Checked.append (Checked.append (checkChunk_sound 1119744 128 c1119744) (checkChunk_sound 1119872 128 c1119872)) (Checked.append (checkChunk_sound 1120000 128 c1120000) (checkChunk_sound 1120128 128 c1120128))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1120256 128 c1120256) (checkChunk_sound 1120384 128 c1120384)) (Checked.append (checkChunk_sound 1120512 128 c1120512) (checkChunk_sound 1120640 128 c1120640))) (Checked.append (Checked.append (checkChunk_sound 1120768 128 c1120768) (checkChunk_sound 1120896 128 c1120896)) (Checked.append (checkChunk_sound 1121024 128 c1121024) (checkChunk_sound 1121152 128 c1121152)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1121280 128 c1121280) (checkChunk_sound 1121408 128 c1121408)) (Checked.append (checkChunk_sound 1121536 128 c1121536) (checkChunk_sound 1121664 128 c1121664))) (Checked.append (Checked.append (checkChunk_sound 1121792 128 c1121792) (checkChunk_sound 1121920 128 c1121920)) (Checked.append (checkChunk_sound 1122048 128 c1122048) (checkChunk_sound 1122176 128 c1122176)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B005
