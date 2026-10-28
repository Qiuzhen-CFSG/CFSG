module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [106496, 114688).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B012
private theorem c106496 : checkChunk 106496 128 = true := by decide +kernel
private theorem c106624 : checkChunk 106624 128 = true := by decide +kernel
private theorem c106752 : checkChunk 106752 128 = true := by decide +kernel
private theorem c106880 : checkChunk 106880 128 = true := by decide +kernel
private theorem c107008 : checkChunk 107008 128 = true := by decide +kernel
private theorem c107136 : checkChunk 107136 128 = true := by decide +kernel
private theorem c107264 : checkChunk 107264 128 = true := by decide +kernel
private theorem c107392 : checkChunk 107392 128 = true := by decide +kernel
private theorem c107520 : checkChunk 107520 128 = true := by decide +kernel
private theorem c107648 : checkChunk 107648 128 = true := by decide +kernel
private theorem c107776 : checkChunk 107776 128 = true := by decide +kernel
private theorem c107904 : checkChunk 107904 128 = true := by decide +kernel
private theorem c108032 : checkChunk 108032 128 = true := by decide +kernel
private theorem c108160 : checkChunk 108160 128 = true := by decide +kernel
private theorem c108288 : checkChunk 108288 128 = true := by decide +kernel
private theorem c108416 : checkChunk 108416 128 = true := by decide +kernel
private theorem c108544 : checkChunk 108544 128 = true := by decide +kernel
private theorem c108672 : checkChunk 108672 128 = true := by decide +kernel
private theorem c108800 : checkChunk 108800 128 = true := by decide +kernel
private theorem c108928 : checkChunk 108928 128 = true := by decide +kernel
private theorem c109056 : checkChunk 109056 128 = true := by decide +kernel
private theorem c109184 : checkChunk 109184 128 = true := by decide +kernel
private theorem c109312 : checkChunk 109312 128 = true := by decide +kernel
private theorem c109440 : checkChunk 109440 128 = true := by decide +kernel
private theorem c109568 : checkChunk 109568 128 = true := by decide +kernel
private theorem c109696 : checkChunk 109696 128 = true := by decide +kernel
private theorem c109824 : checkChunk 109824 128 = true := by decide +kernel
private theorem c109952 : checkChunk 109952 128 = true := by decide +kernel
private theorem c110080 : checkChunk 110080 128 = true := by decide +kernel
private theorem c110208 : checkChunk 110208 128 = true := by decide +kernel
private theorem c110336 : checkChunk 110336 128 = true := by decide +kernel
private theorem c110464 : checkChunk 110464 128 = true := by decide +kernel
private theorem c110592 : checkChunk 110592 128 = true := by decide +kernel
private theorem c110720 : checkChunk 110720 128 = true := by decide +kernel
private theorem c110848 : checkChunk 110848 128 = true := by decide +kernel
private theorem c110976 : checkChunk 110976 128 = true := by decide +kernel
private theorem c111104 : checkChunk 111104 128 = true := by decide +kernel
private theorem c111232 : checkChunk 111232 128 = true := by decide +kernel
private theorem c111360 : checkChunk 111360 128 = true := by decide +kernel
private theorem c111488 : checkChunk 111488 128 = true := by decide +kernel
private theorem c111616 : checkChunk 111616 128 = true := by decide +kernel
private theorem c111744 : checkChunk 111744 128 = true := by decide +kernel
private theorem c111872 : checkChunk 111872 128 = true := by decide +kernel
private theorem c112000 : checkChunk 112000 128 = true := by decide +kernel
private theorem c112128 : checkChunk 112128 128 = true := by decide +kernel
private theorem c112256 : checkChunk 112256 128 = true := by decide +kernel
private theorem c112384 : checkChunk 112384 128 = true := by decide +kernel
private theorem c112512 : checkChunk 112512 128 = true := by decide +kernel
private theorem c112640 : checkChunk 112640 128 = true := by decide +kernel
private theorem c112768 : checkChunk 112768 128 = true := by decide +kernel
private theorem c112896 : checkChunk 112896 128 = true := by decide +kernel
private theorem c113024 : checkChunk 113024 128 = true := by decide +kernel
private theorem c113152 : checkChunk 113152 128 = true := by decide +kernel
private theorem c113280 : checkChunk 113280 128 = true := by decide +kernel
private theorem c113408 : checkChunk 113408 128 = true := by decide +kernel
private theorem c113536 : checkChunk 113536 128 = true := by decide +kernel
private theorem c113664 : checkChunk 113664 128 = true := by decide +kernel
private theorem c113792 : checkChunk 113792 128 = true := by decide +kernel
private theorem c113920 : checkChunk 113920 128 = true := by decide +kernel
private theorem c114048 : checkChunk 114048 128 = true := by decide +kernel
private theorem c114176 : checkChunk 114176 128 = true := by decide +kernel
private theorem c114304 : checkChunk 114304 128 = true := by decide +kernel
private theorem c114432 : checkChunk 114432 128 = true := by decide +kernel
private theorem c114560 : checkChunk 114560 128 = true := by decide +kernel

public theorem checked : Checked 106496 114688 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 106496 128 c106496) (checkChunk_sound 106624 128 c106624)) (Checked.append (checkChunk_sound 106752 128 c106752) (checkChunk_sound 106880 128 c106880))) (Checked.append (Checked.append (checkChunk_sound 107008 128 c107008) (checkChunk_sound 107136 128 c107136)) (Checked.append (checkChunk_sound 107264 128 c107264) (checkChunk_sound 107392 128 c107392)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 107520 128 c107520) (checkChunk_sound 107648 128 c107648)) (Checked.append (checkChunk_sound 107776 128 c107776) (checkChunk_sound 107904 128 c107904))) (Checked.append (Checked.append (checkChunk_sound 108032 128 c108032) (checkChunk_sound 108160 128 c108160)) (Checked.append (checkChunk_sound 108288 128 c108288) (checkChunk_sound 108416 128 c108416))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 108544 128 c108544) (checkChunk_sound 108672 128 c108672)) (Checked.append (checkChunk_sound 108800 128 c108800) (checkChunk_sound 108928 128 c108928))) (Checked.append (Checked.append (checkChunk_sound 109056 128 c109056) (checkChunk_sound 109184 128 c109184)) (Checked.append (checkChunk_sound 109312 128 c109312) (checkChunk_sound 109440 128 c109440)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 109568 128 c109568) (checkChunk_sound 109696 128 c109696)) (Checked.append (checkChunk_sound 109824 128 c109824) (checkChunk_sound 109952 128 c109952))) (Checked.append (Checked.append (checkChunk_sound 110080 128 c110080) (checkChunk_sound 110208 128 c110208)) (Checked.append (checkChunk_sound 110336 128 c110336) (checkChunk_sound 110464 128 c110464)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 110592 128 c110592) (checkChunk_sound 110720 128 c110720)) (Checked.append (checkChunk_sound 110848 128 c110848) (checkChunk_sound 110976 128 c110976))) (Checked.append (Checked.append (checkChunk_sound 111104 128 c111104) (checkChunk_sound 111232 128 c111232)) (Checked.append (checkChunk_sound 111360 128 c111360) (checkChunk_sound 111488 128 c111488)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 111616 128 c111616) (checkChunk_sound 111744 128 c111744)) (Checked.append (checkChunk_sound 111872 128 c111872) (checkChunk_sound 112000 128 c112000))) (Checked.append (Checked.append (checkChunk_sound 112128 128 c112128) (checkChunk_sound 112256 128 c112256)) (Checked.append (checkChunk_sound 112384 128 c112384) (checkChunk_sound 112512 128 c112512))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 112640 128 c112640) (checkChunk_sound 112768 128 c112768)) (Checked.append (checkChunk_sound 112896 128 c112896) (checkChunk_sound 113024 128 c113024))) (Checked.append (Checked.append (checkChunk_sound 113152 128 c113152) (checkChunk_sound 113280 128 c113280)) (Checked.append (checkChunk_sound 113408 128 c113408) (checkChunk_sound 113536 128 c113536)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 113664 128 c113664) (checkChunk_sound 113792 128 c113792)) (Checked.append (checkChunk_sound 113920 128 c113920) (checkChunk_sound 114048 128 c114048))) (Checked.append (Checked.append (checkChunk_sound 114176 128 c114176) (checkChunk_sound 114304 128 c114304)) (Checked.append (checkChunk_sound 114432 128 c114432) (checkChunk_sound 114560 128 c114560)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B012
