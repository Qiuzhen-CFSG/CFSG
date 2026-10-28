module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1622016, 1630208).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B015
private theorem c1622016 : checkChunk 1622016 128 = true := by decide +kernel
private theorem c1622144 : checkChunk 1622144 128 = true := by decide +kernel
private theorem c1622272 : checkChunk 1622272 128 = true := by decide +kernel
private theorem c1622400 : checkChunk 1622400 128 = true := by decide +kernel
private theorem c1622528 : checkChunk 1622528 128 = true := by decide +kernel
private theorem c1622656 : checkChunk 1622656 128 = true := by decide +kernel
private theorem c1622784 : checkChunk 1622784 128 = true := by decide +kernel
private theorem c1622912 : checkChunk 1622912 128 = true := by decide +kernel
private theorem c1623040 : checkChunk 1623040 128 = true := by decide +kernel
private theorem c1623168 : checkChunk 1623168 128 = true := by decide +kernel
private theorem c1623296 : checkChunk 1623296 128 = true := by decide +kernel
private theorem c1623424 : checkChunk 1623424 128 = true := by decide +kernel
private theorem c1623552 : checkChunk 1623552 128 = true := by decide +kernel
private theorem c1623680 : checkChunk 1623680 128 = true := by decide +kernel
private theorem c1623808 : checkChunk 1623808 128 = true := by decide +kernel
private theorem c1623936 : checkChunk 1623936 128 = true := by decide +kernel
private theorem c1624064 : checkChunk 1624064 128 = true := by decide +kernel
private theorem c1624192 : checkChunk 1624192 128 = true := by decide +kernel
private theorem c1624320 : checkChunk 1624320 128 = true := by decide +kernel
private theorem c1624448 : checkChunk 1624448 128 = true := by decide +kernel
private theorem c1624576 : checkChunk 1624576 128 = true := by decide +kernel
private theorem c1624704 : checkChunk 1624704 128 = true := by decide +kernel
private theorem c1624832 : checkChunk 1624832 128 = true := by decide +kernel
private theorem c1624960 : checkChunk 1624960 128 = true := by decide +kernel
private theorem c1625088 : checkChunk 1625088 128 = true := by decide +kernel
private theorem c1625216 : checkChunk 1625216 128 = true := by decide +kernel
private theorem c1625344 : checkChunk 1625344 128 = true := by decide +kernel
private theorem c1625472 : checkChunk 1625472 128 = true := by decide +kernel
private theorem c1625600 : checkChunk 1625600 128 = true := by decide +kernel
private theorem c1625728 : checkChunk 1625728 128 = true := by decide +kernel
private theorem c1625856 : checkChunk 1625856 128 = true := by decide +kernel
private theorem c1625984 : checkChunk 1625984 128 = true := by decide +kernel
private theorem c1626112 : checkChunk 1626112 128 = true := by decide +kernel
private theorem c1626240 : checkChunk 1626240 128 = true := by decide +kernel
private theorem c1626368 : checkChunk 1626368 128 = true := by decide +kernel
private theorem c1626496 : checkChunk 1626496 128 = true := by decide +kernel
private theorem c1626624 : checkChunk 1626624 128 = true := by decide +kernel
private theorem c1626752 : checkChunk 1626752 128 = true := by decide +kernel
private theorem c1626880 : checkChunk 1626880 128 = true := by decide +kernel
private theorem c1627008 : checkChunk 1627008 128 = true := by decide +kernel
private theorem c1627136 : checkChunk 1627136 128 = true := by decide +kernel
private theorem c1627264 : checkChunk 1627264 128 = true := by decide +kernel
private theorem c1627392 : checkChunk 1627392 128 = true := by decide +kernel
private theorem c1627520 : checkChunk 1627520 128 = true := by decide +kernel
private theorem c1627648 : checkChunk 1627648 128 = true := by decide +kernel
private theorem c1627776 : checkChunk 1627776 128 = true := by decide +kernel
private theorem c1627904 : checkChunk 1627904 128 = true := by decide +kernel
private theorem c1628032 : checkChunk 1628032 128 = true := by decide +kernel
private theorem c1628160 : checkChunk 1628160 128 = true := by decide +kernel
private theorem c1628288 : checkChunk 1628288 128 = true := by decide +kernel
private theorem c1628416 : checkChunk 1628416 128 = true := by decide +kernel
private theorem c1628544 : checkChunk 1628544 128 = true := by decide +kernel
private theorem c1628672 : checkChunk 1628672 128 = true := by decide +kernel
private theorem c1628800 : checkChunk 1628800 128 = true := by decide +kernel
private theorem c1628928 : checkChunk 1628928 128 = true := by decide +kernel
private theorem c1629056 : checkChunk 1629056 128 = true := by decide +kernel
private theorem c1629184 : checkChunk 1629184 128 = true := by decide +kernel
private theorem c1629312 : checkChunk 1629312 128 = true := by decide +kernel
private theorem c1629440 : checkChunk 1629440 128 = true := by decide +kernel
private theorem c1629568 : checkChunk 1629568 128 = true := by decide +kernel
private theorem c1629696 : checkChunk 1629696 128 = true := by decide +kernel
private theorem c1629824 : checkChunk 1629824 128 = true := by decide +kernel
private theorem c1629952 : checkChunk 1629952 128 = true := by decide +kernel
private theorem c1630080 : checkChunk 1630080 128 = true := by decide +kernel

public theorem checked : Checked 1622016 1630208 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1622016 128 c1622016) (checkChunk_sound 1622144 128 c1622144)) (Checked.append (checkChunk_sound 1622272 128 c1622272) (checkChunk_sound 1622400 128 c1622400))) (Checked.append (Checked.append (checkChunk_sound 1622528 128 c1622528) (checkChunk_sound 1622656 128 c1622656)) (Checked.append (checkChunk_sound 1622784 128 c1622784) (checkChunk_sound 1622912 128 c1622912)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1623040 128 c1623040) (checkChunk_sound 1623168 128 c1623168)) (Checked.append (checkChunk_sound 1623296 128 c1623296) (checkChunk_sound 1623424 128 c1623424))) (Checked.append (Checked.append (checkChunk_sound 1623552 128 c1623552) (checkChunk_sound 1623680 128 c1623680)) (Checked.append (checkChunk_sound 1623808 128 c1623808) (checkChunk_sound 1623936 128 c1623936))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1624064 128 c1624064) (checkChunk_sound 1624192 128 c1624192)) (Checked.append (checkChunk_sound 1624320 128 c1624320) (checkChunk_sound 1624448 128 c1624448))) (Checked.append (Checked.append (checkChunk_sound 1624576 128 c1624576) (checkChunk_sound 1624704 128 c1624704)) (Checked.append (checkChunk_sound 1624832 128 c1624832) (checkChunk_sound 1624960 128 c1624960)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1625088 128 c1625088) (checkChunk_sound 1625216 128 c1625216)) (Checked.append (checkChunk_sound 1625344 128 c1625344) (checkChunk_sound 1625472 128 c1625472))) (Checked.append (Checked.append (checkChunk_sound 1625600 128 c1625600) (checkChunk_sound 1625728 128 c1625728)) (Checked.append (checkChunk_sound 1625856 128 c1625856) (checkChunk_sound 1625984 128 c1625984)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1626112 128 c1626112) (checkChunk_sound 1626240 128 c1626240)) (Checked.append (checkChunk_sound 1626368 128 c1626368) (checkChunk_sound 1626496 128 c1626496))) (Checked.append (Checked.append (checkChunk_sound 1626624 128 c1626624) (checkChunk_sound 1626752 128 c1626752)) (Checked.append (checkChunk_sound 1626880 128 c1626880) (checkChunk_sound 1627008 128 c1627008)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1627136 128 c1627136) (checkChunk_sound 1627264 128 c1627264)) (Checked.append (checkChunk_sound 1627392 128 c1627392) (checkChunk_sound 1627520 128 c1627520))) (Checked.append (Checked.append (checkChunk_sound 1627648 128 c1627648) (checkChunk_sound 1627776 128 c1627776)) (Checked.append (checkChunk_sound 1627904 128 c1627904) (checkChunk_sound 1628032 128 c1628032))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1628160 128 c1628160) (checkChunk_sound 1628288 128 c1628288)) (Checked.append (checkChunk_sound 1628416 128 c1628416) (checkChunk_sound 1628544 128 c1628544))) (Checked.append (Checked.append (checkChunk_sound 1628672 128 c1628672) (checkChunk_sound 1628800 128 c1628800)) (Checked.append (checkChunk_sound 1628928 128 c1628928) (checkChunk_sound 1629056 128 c1629056)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1629184 128 c1629184) (checkChunk_sound 1629312 128 c1629312)) (Checked.append (checkChunk_sound 1629440 128 c1629440) (checkChunk_sound 1629568 128 c1629568))) (Checked.append (Checked.append (checkChunk_sound 1629696 128 c1629696) (checkChunk_sound 1629824 128 c1629824)) (Checked.append (checkChunk_sound 1629952 128 c1629952) (checkChunk_sound 1630080 128 c1630080)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B015
