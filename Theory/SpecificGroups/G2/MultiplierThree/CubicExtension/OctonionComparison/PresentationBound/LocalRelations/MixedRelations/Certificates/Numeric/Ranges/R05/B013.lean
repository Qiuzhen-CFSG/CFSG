module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1179648, 1187840).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B013
private theorem c1179648 : checkChunk 1179648 128 = true := by decide +kernel
private theorem c1179776 : checkChunk 1179776 128 = true := by decide +kernel
private theorem c1179904 : checkChunk 1179904 128 = true := by decide +kernel
private theorem c1180032 : checkChunk 1180032 128 = true := by decide +kernel
private theorem c1180160 : checkChunk 1180160 128 = true := by decide +kernel
private theorem c1180288 : checkChunk 1180288 128 = true := by decide +kernel
private theorem c1180416 : checkChunk 1180416 128 = true := by decide +kernel
private theorem c1180544 : checkChunk 1180544 128 = true := by decide +kernel
private theorem c1180672 : checkChunk 1180672 128 = true := by decide +kernel
private theorem c1180800 : checkChunk 1180800 128 = true := by decide +kernel
private theorem c1180928 : checkChunk 1180928 128 = true := by decide +kernel
private theorem c1181056 : checkChunk 1181056 128 = true := by decide +kernel
private theorem c1181184 : checkChunk 1181184 128 = true := by decide +kernel
private theorem c1181312 : checkChunk 1181312 128 = true := by decide +kernel
private theorem c1181440 : checkChunk 1181440 128 = true := by decide +kernel
private theorem c1181568 : checkChunk 1181568 128 = true := by decide +kernel
private theorem c1181696 : checkChunk 1181696 128 = true := by decide +kernel
private theorem c1181824 : checkChunk 1181824 128 = true := by decide +kernel
private theorem c1181952 : checkChunk 1181952 128 = true := by decide +kernel
private theorem c1182080 : checkChunk 1182080 128 = true := by decide +kernel
private theorem c1182208 : checkChunk 1182208 128 = true := by decide +kernel
private theorem c1182336 : checkChunk 1182336 128 = true := by decide +kernel
private theorem c1182464 : checkChunk 1182464 128 = true := by decide +kernel
private theorem c1182592 : checkChunk 1182592 128 = true := by decide +kernel
private theorem c1182720 : checkChunk 1182720 128 = true := by decide +kernel
private theorem c1182848 : checkChunk 1182848 128 = true := by decide +kernel
private theorem c1182976 : checkChunk 1182976 128 = true := by decide +kernel
private theorem c1183104 : checkChunk 1183104 128 = true := by decide +kernel
private theorem c1183232 : checkChunk 1183232 128 = true := by decide +kernel
private theorem c1183360 : checkChunk 1183360 128 = true := by decide +kernel
private theorem c1183488 : checkChunk 1183488 128 = true := by decide +kernel
private theorem c1183616 : checkChunk 1183616 128 = true := by decide +kernel
private theorem c1183744 : checkChunk 1183744 128 = true := by decide +kernel
private theorem c1183872 : checkChunk 1183872 128 = true := by decide +kernel
private theorem c1184000 : checkChunk 1184000 128 = true := by decide +kernel
private theorem c1184128 : checkChunk 1184128 128 = true := by decide +kernel
private theorem c1184256 : checkChunk 1184256 128 = true := by decide +kernel
private theorem c1184384 : checkChunk 1184384 128 = true := by decide +kernel
private theorem c1184512 : checkChunk 1184512 128 = true := by decide +kernel
private theorem c1184640 : checkChunk 1184640 128 = true := by decide +kernel
private theorem c1184768 : checkChunk 1184768 128 = true := by decide +kernel
private theorem c1184896 : checkChunk 1184896 128 = true := by decide +kernel
private theorem c1185024 : checkChunk 1185024 128 = true := by decide +kernel
private theorem c1185152 : checkChunk 1185152 128 = true := by decide +kernel
private theorem c1185280 : checkChunk 1185280 128 = true := by decide +kernel
private theorem c1185408 : checkChunk 1185408 128 = true := by decide +kernel
private theorem c1185536 : checkChunk 1185536 128 = true := by decide +kernel
private theorem c1185664 : checkChunk 1185664 128 = true := by decide +kernel
private theorem c1185792 : checkChunk 1185792 128 = true := by decide +kernel
private theorem c1185920 : checkChunk 1185920 128 = true := by decide +kernel
private theorem c1186048 : checkChunk 1186048 128 = true := by decide +kernel
private theorem c1186176 : checkChunk 1186176 128 = true := by decide +kernel
private theorem c1186304 : checkChunk 1186304 128 = true := by decide +kernel
private theorem c1186432 : checkChunk 1186432 128 = true := by decide +kernel
private theorem c1186560 : checkChunk 1186560 128 = true := by decide +kernel
private theorem c1186688 : checkChunk 1186688 128 = true := by decide +kernel
private theorem c1186816 : checkChunk 1186816 128 = true := by decide +kernel
private theorem c1186944 : checkChunk 1186944 128 = true := by decide +kernel
private theorem c1187072 : checkChunk 1187072 128 = true := by decide +kernel
private theorem c1187200 : checkChunk 1187200 128 = true := by decide +kernel
private theorem c1187328 : checkChunk 1187328 128 = true := by decide +kernel
private theorem c1187456 : checkChunk 1187456 128 = true := by decide +kernel
private theorem c1187584 : checkChunk 1187584 128 = true := by decide +kernel
private theorem c1187712 : checkChunk 1187712 128 = true := by decide +kernel

public theorem checked : Checked 1179648 1187840 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1179648 128 c1179648) (checkChunk_sound 1179776 128 c1179776)) (Checked.append (checkChunk_sound 1179904 128 c1179904) (checkChunk_sound 1180032 128 c1180032))) (Checked.append (Checked.append (checkChunk_sound 1180160 128 c1180160) (checkChunk_sound 1180288 128 c1180288)) (Checked.append (checkChunk_sound 1180416 128 c1180416) (checkChunk_sound 1180544 128 c1180544)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1180672 128 c1180672) (checkChunk_sound 1180800 128 c1180800)) (Checked.append (checkChunk_sound 1180928 128 c1180928) (checkChunk_sound 1181056 128 c1181056))) (Checked.append (Checked.append (checkChunk_sound 1181184 128 c1181184) (checkChunk_sound 1181312 128 c1181312)) (Checked.append (checkChunk_sound 1181440 128 c1181440) (checkChunk_sound 1181568 128 c1181568))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1181696 128 c1181696) (checkChunk_sound 1181824 128 c1181824)) (Checked.append (checkChunk_sound 1181952 128 c1181952) (checkChunk_sound 1182080 128 c1182080))) (Checked.append (Checked.append (checkChunk_sound 1182208 128 c1182208) (checkChunk_sound 1182336 128 c1182336)) (Checked.append (checkChunk_sound 1182464 128 c1182464) (checkChunk_sound 1182592 128 c1182592)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1182720 128 c1182720) (checkChunk_sound 1182848 128 c1182848)) (Checked.append (checkChunk_sound 1182976 128 c1182976) (checkChunk_sound 1183104 128 c1183104))) (Checked.append (Checked.append (checkChunk_sound 1183232 128 c1183232) (checkChunk_sound 1183360 128 c1183360)) (Checked.append (checkChunk_sound 1183488 128 c1183488) (checkChunk_sound 1183616 128 c1183616)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1183744 128 c1183744) (checkChunk_sound 1183872 128 c1183872)) (Checked.append (checkChunk_sound 1184000 128 c1184000) (checkChunk_sound 1184128 128 c1184128))) (Checked.append (Checked.append (checkChunk_sound 1184256 128 c1184256) (checkChunk_sound 1184384 128 c1184384)) (Checked.append (checkChunk_sound 1184512 128 c1184512) (checkChunk_sound 1184640 128 c1184640)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1184768 128 c1184768) (checkChunk_sound 1184896 128 c1184896)) (Checked.append (checkChunk_sound 1185024 128 c1185024) (checkChunk_sound 1185152 128 c1185152))) (Checked.append (Checked.append (checkChunk_sound 1185280 128 c1185280) (checkChunk_sound 1185408 128 c1185408)) (Checked.append (checkChunk_sound 1185536 128 c1185536) (checkChunk_sound 1185664 128 c1185664))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1185792 128 c1185792) (checkChunk_sound 1185920 128 c1185920)) (Checked.append (checkChunk_sound 1186048 128 c1186048) (checkChunk_sound 1186176 128 c1186176))) (Checked.append (Checked.append (checkChunk_sound 1186304 128 c1186304) (checkChunk_sound 1186432 128 c1186432)) (Checked.append (checkChunk_sound 1186560 128 c1186560) (checkChunk_sound 1186688 128 c1186688)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1186816 128 c1186816) (checkChunk_sound 1186944 128 c1186944)) (Checked.append (checkChunk_sound 1187072 128 c1187072) (checkChunk_sound 1187200 128 c1187200))) (Checked.append (Checked.append (checkChunk_sound 1187328 128 c1187328) (checkChunk_sound 1187456 128 c1187456)) (Checked.append (checkChunk_sound 1187584 128 c1187584) (checkChunk_sound 1187712 128 c1187712)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B013
