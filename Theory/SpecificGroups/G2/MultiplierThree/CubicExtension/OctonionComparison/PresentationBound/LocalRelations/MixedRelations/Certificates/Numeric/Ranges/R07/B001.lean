module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1507328, 1515520).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B001
private theorem c1507328 : checkChunk 1507328 128 = true := by decide +kernel
private theorem c1507456 : checkChunk 1507456 128 = true := by decide +kernel
private theorem c1507584 : checkChunk 1507584 128 = true := by decide +kernel
private theorem c1507712 : checkChunk 1507712 128 = true := by decide +kernel
private theorem c1507840 : checkChunk 1507840 128 = true := by decide +kernel
private theorem c1507968 : checkChunk 1507968 128 = true := by decide +kernel
private theorem c1508096 : checkChunk 1508096 128 = true := by decide +kernel
private theorem c1508224 : checkChunk 1508224 128 = true := by decide +kernel
private theorem c1508352 : checkChunk 1508352 128 = true := by decide +kernel
private theorem c1508480 : checkChunk 1508480 128 = true := by decide +kernel
private theorem c1508608 : checkChunk 1508608 128 = true := by decide +kernel
private theorem c1508736 : checkChunk 1508736 128 = true := by decide +kernel
private theorem c1508864 : checkChunk 1508864 128 = true := by decide +kernel
private theorem c1508992 : checkChunk 1508992 128 = true := by decide +kernel
private theorem c1509120 : checkChunk 1509120 128 = true := by decide +kernel
private theorem c1509248 : checkChunk 1509248 128 = true := by decide +kernel
private theorem c1509376 : checkChunk 1509376 128 = true := by decide +kernel
private theorem c1509504 : checkChunk 1509504 128 = true := by decide +kernel
private theorem c1509632 : checkChunk 1509632 128 = true := by decide +kernel
private theorem c1509760 : checkChunk 1509760 128 = true := by decide +kernel
private theorem c1509888 : checkChunk 1509888 128 = true := by decide +kernel
private theorem c1510016 : checkChunk 1510016 128 = true := by decide +kernel
private theorem c1510144 : checkChunk 1510144 128 = true := by decide +kernel
private theorem c1510272 : checkChunk 1510272 128 = true := by decide +kernel
private theorem c1510400 : checkChunk 1510400 128 = true := by decide +kernel
private theorem c1510528 : checkChunk 1510528 128 = true := by decide +kernel
private theorem c1510656 : checkChunk 1510656 128 = true := by decide +kernel
private theorem c1510784 : checkChunk 1510784 128 = true := by decide +kernel
private theorem c1510912 : checkChunk 1510912 128 = true := by decide +kernel
private theorem c1511040 : checkChunk 1511040 128 = true := by decide +kernel
private theorem c1511168 : checkChunk 1511168 128 = true := by decide +kernel
private theorem c1511296 : checkChunk 1511296 128 = true := by decide +kernel
private theorem c1511424 : checkChunk 1511424 128 = true := by decide +kernel
private theorem c1511552 : checkChunk 1511552 128 = true := by decide +kernel
private theorem c1511680 : checkChunk 1511680 128 = true := by decide +kernel
private theorem c1511808 : checkChunk 1511808 128 = true := by decide +kernel
private theorem c1511936 : checkChunk 1511936 128 = true := by decide +kernel
private theorem c1512064 : checkChunk 1512064 128 = true := by decide +kernel
private theorem c1512192 : checkChunk 1512192 128 = true := by decide +kernel
private theorem c1512320 : checkChunk 1512320 128 = true := by decide +kernel
private theorem c1512448 : checkChunk 1512448 128 = true := by decide +kernel
private theorem c1512576 : checkChunk 1512576 128 = true := by decide +kernel
private theorem c1512704 : checkChunk 1512704 128 = true := by decide +kernel
private theorem c1512832 : checkChunk 1512832 128 = true := by decide +kernel
private theorem c1512960 : checkChunk 1512960 128 = true := by decide +kernel
private theorem c1513088 : checkChunk 1513088 128 = true := by decide +kernel
private theorem c1513216 : checkChunk 1513216 128 = true := by decide +kernel
private theorem c1513344 : checkChunk 1513344 128 = true := by decide +kernel
private theorem c1513472 : checkChunk 1513472 128 = true := by decide +kernel
private theorem c1513600 : checkChunk 1513600 128 = true := by decide +kernel
private theorem c1513728 : checkChunk 1513728 128 = true := by decide +kernel
private theorem c1513856 : checkChunk 1513856 128 = true := by decide +kernel
private theorem c1513984 : checkChunk 1513984 128 = true := by decide +kernel
private theorem c1514112 : checkChunk 1514112 128 = true := by decide +kernel
private theorem c1514240 : checkChunk 1514240 128 = true := by decide +kernel
private theorem c1514368 : checkChunk 1514368 128 = true := by decide +kernel
private theorem c1514496 : checkChunk 1514496 128 = true := by decide +kernel
private theorem c1514624 : checkChunk 1514624 128 = true := by decide +kernel
private theorem c1514752 : checkChunk 1514752 128 = true := by decide +kernel
private theorem c1514880 : checkChunk 1514880 128 = true := by decide +kernel
private theorem c1515008 : checkChunk 1515008 128 = true := by decide +kernel
private theorem c1515136 : checkChunk 1515136 128 = true := by decide +kernel
private theorem c1515264 : checkChunk 1515264 128 = true := by decide +kernel
private theorem c1515392 : checkChunk 1515392 128 = true := by decide +kernel

public theorem checked : Checked 1507328 1515520 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1507328 128 c1507328) (checkChunk_sound 1507456 128 c1507456)) (Checked.append (checkChunk_sound 1507584 128 c1507584) (checkChunk_sound 1507712 128 c1507712))) (Checked.append (Checked.append (checkChunk_sound 1507840 128 c1507840) (checkChunk_sound 1507968 128 c1507968)) (Checked.append (checkChunk_sound 1508096 128 c1508096) (checkChunk_sound 1508224 128 c1508224)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1508352 128 c1508352) (checkChunk_sound 1508480 128 c1508480)) (Checked.append (checkChunk_sound 1508608 128 c1508608) (checkChunk_sound 1508736 128 c1508736))) (Checked.append (Checked.append (checkChunk_sound 1508864 128 c1508864) (checkChunk_sound 1508992 128 c1508992)) (Checked.append (checkChunk_sound 1509120 128 c1509120) (checkChunk_sound 1509248 128 c1509248))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1509376 128 c1509376) (checkChunk_sound 1509504 128 c1509504)) (Checked.append (checkChunk_sound 1509632 128 c1509632) (checkChunk_sound 1509760 128 c1509760))) (Checked.append (Checked.append (checkChunk_sound 1509888 128 c1509888) (checkChunk_sound 1510016 128 c1510016)) (Checked.append (checkChunk_sound 1510144 128 c1510144) (checkChunk_sound 1510272 128 c1510272)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1510400 128 c1510400) (checkChunk_sound 1510528 128 c1510528)) (Checked.append (checkChunk_sound 1510656 128 c1510656) (checkChunk_sound 1510784 128 c1510784))) (Checked.append (Checked.append (checkChunk_sound 1510912 128 c1510912) (checkChunk_sound 1511040 128 c1511040)) (Checked.append (checkChunk_sound 1511168 128 c1511168) (checkChunk_sound 1511296 128 c1511296)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1511424 128 c1511424) (checkChunk_sound 1511552 128 c1511552)) (Checked.append (checkChunk_sound 1511680 128 c1511680) (checkChunk_sound 1511808 128 c1511808))) (Checked.append (Checked.append (checkChunk_sound 1511936 128 c1511936) (checkChunk_sound 1512064 128 c1512064)) (Checked.append (checkChunk_sound 1512192 128 c1512192) (checkChunk_sound 1512320 128 c1512320)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1512448 128 c1512448) (checkChunk_sound 1512576 128 c1512576)) (Checked.append (checkChunk_sound 1512704 128 c1512704) (checkChunk_sound 1512832 128 c1512832))) (Checked.append (Checked.append (checkChunk_sound 1512960 128 c1512960) (checkChunk_sound 1513088 128 c1513088)) (Checked.append (checkChunk_sound 1513216 128 c1513216) (checkChunk_sound 1513344 128 c1513344))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1513472 128 c1513472) (checkChunk_sound 1513600 128 c1513600)) (Checked.append (checkChunk_sound 1513728 128 c1513728) (checkChunk_sound 1513856 128 c1513856))) (Checked.append (Checked.append (checkChunk_sound 1513984 128 c1513984) (checkChunk_sound 1514112 128 c1514112)) (Checked.append (checkChunk_sound 1514240 128 c1514240) (checkChunk_sound 1514368 128 c1514368)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1514496 128 c1514496) (checkChunk_sound 1514624 128 c1514624)) (Checked.append (checkChunk_sound 1514752 128 c1514752) (checkChunk_sound 1514880 128 c1514880))) (Checked.append (Checked.append (checkChunk_sound 1515008 128 c1515008) (checkChunk_sound 1515136 128 c1515136)) (Checked.append (checkChunk_sound 1515264 128 c1515264) (checkChunk_sound 1515392 128 c1515392)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B001
