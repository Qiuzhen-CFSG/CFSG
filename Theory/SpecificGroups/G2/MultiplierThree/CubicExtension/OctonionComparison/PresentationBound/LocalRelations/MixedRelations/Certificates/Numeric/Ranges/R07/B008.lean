module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1564672, 1572864).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B008
private theorem c1564672 : checkChunk 1564672 128 = true := by decide +kernel
private theorem c1564800 : checkChunk 1564800 128 = true := by decide +kernel
private theorem c1564928 : checkChunk 1564928 128 = true := by decide +kernel
private theorem c1565056 : checkChunk 1565056 128 = true := by decide +kernel
private theorem c1565184 : checkChunk 1565184 128 = true := by decide +kernel
private theorem c1565312 : checkChunk 1565312 128 = true := by decide +kernel
private theorem c1565440 : checkChunk 1565440 128 = true := by decide +kernel
private theorem c1565568 : checkChunk 1565568 128 = true := by decide +kernel
private theorem c1565696 : checkChunk 1565696 128 = true := by decide +kernel
private theorem c1565824 : checkChunk 1565824 128 = true := by decide +kernel
private theorem c1565952 : checkChunk 1565952 128 = true := by decide +kernel
private theorem c1566080 : checkChunk 1566080 128 = true := by decide +kernel
private theorem c1566208 : checkChunk 1566208 128 = true := by decide +kernel
private theorem c1566336 : checkChunk 1566336 128 = true := by decide +kernel
private theorem c1566464 : checkChunk 1566464 128 = true := by decide +kernel
private theorem c1566592 : checkChunk 1566592 128 = true := by decide +kernel
private theorem c1566720 : checkChunk 1566720 128 = true := by decide +kernel
private theorem c1566848 : checkChunk 1566848 128 = true := by decide +kernel
private theorem c1566976 : checkChunk 1566976 128 = true := by decide +kernel
private theorem c1567104 : checkChunk 1567104 128 = true := by decide +kernel
private theorem c1567232 : checkChunk 1567232 128 = true := by decide +kernel
private theorem c1567360 : checkChunk 1567360 128 = true := by decide +kernel
private theorem c1567488 : checkChunk 1567488 128 = true := by decide +kernel
private theorem c1567616 : checkChunk 1567616 128 = true := by decide +kernel
private theorem c1567744 : checkChunk 1567744 128 = true := by decide +kernel
private theorem c1567872 : checkChunk 1567872 128 = true := by decide +kernel
private theorem c1568000 : checkChunk 1568000 128 = true := by decide +kernel
private theorem c1568128 : checkChunk 1568128 128 = true := by decide +kernel
private theorem c1568256 : checkChunk 1568256 128 = true := by decide +kernel
private theorem c1568384 : checkChunk 1568384 128 = true := by decide +kernel
private theorem c1568512 : checkChunk 1568512 128 = true := by decide +kernel
private theorem c1568640 : checkChunk 1568640 128 = true := by decide +kernel
private theorem c1568768 : checkChunk 1568768 128 = true := by decide +kernel
private theorem c1568896 : checkChunk 1568896 128 = true := by decide +kernel
private theorem c1569024 : checkChunk 1569024 128 = true := by decide +kernel
private theorem c1569152 : checkChunk 1569152 128 = true := by decide +kernel
private theorem c1569280 : checkChunk 1569280 128 = true := by decide +kernel
private theorem c1569408 : checkChunk 1569408 128 = true := by decide +kernel
private theorem c1569536 : checkChunk 1569536 128 = true := by decide +kernel
private theorem c1569664 : checkChunk 1569664 128 = true := by decide +kernel
private theorem c1569792 : checkChunk 1569792 128 = true := by decide +kernel
private theorem c1569920 : checkChunk 1569920 128 = true := by decide +kernel
private theorem c1570048 : checkChunk 1570048 128 = true := by decide +kernel
private theorem c1570176 : checkChunk 1570176 128 = true := by decide +kernel
private theorem c1570304 : checkChunk 1570304 128 = true := by decide +kernel
private theorem c1570432 : checkChunk 1570432 128 = true := by decide +kernel
private theorem c1570560 : checkChunk 1570560 128 = true := by decide +kernel
private theorem c1570688 : checkChunk 1570688 128 = true := by decide +kernel
private theorem c1570816 : checkChunk 1570816 128 = true := by decide +kernel
private theorem c1570944 : checkChunk 1570944 128 = true := by decide +kernel
private theorem c1571072 : checkChunk 1571072 128 = true := by decide +kernel
private theorem c1571200 : checkChunk 1571200 128 = true := by decide +kernel
private theorem c1571328 : checkChunk 1571328 128 = true := by decide +kernel
private theorem c1571456 : checkChunk 1571456 128 = true := by decide +kernel
private theorem c1571584 : checkChunk 1571584 128 = true := by decide +kernel
private theorem c1571712 : checkChunk 1571712 128 = true := by decide +kernel
private theorem c1571840 : checkChunk 1571840 128 = true := by decide +kernel
private theorem c1571968 : checkChunk 1571968 128 = true := by decide +kernel
private theorem c1572096 : checkChunk 1572096 128 = true := by decide +kernel
private theorem c1572224 : checkChunk 1572224 128 = true := by decide +kernel
private theorem c1572352 : checkChunk 1572352 128 = true := by decide +kernel
private theorem c1572480 : checkChunk 1572480 128 = true := by decide +kernel
private theorem c1572608 : checkChunk 1572608 128 = true := by decide +kernel
private theorem c1572736 : checkChunk 1572736 128 = true := by decide +kernel

public theorem checked : Checked 1564672 1572864 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1564672 128 c1564672) (checkChunk_sound 1564800 128 c1564800)) (Checked.append (checkChunk_sound 1564928 128 c1564928) (checkChunk_sound 1565056 128 c1565056))) (Checked.append (Checked.append (checkChunk_sound 1565184 128 c1565184) (checkChunk_sound 1565312 128 c1565312)) (Checked.append (checkChunk_sound 1565440 128 c1565440) (checkChunk_sound 1565568 128 c1565568)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1565696 128 c1565696) (checkChunk_sound 1565824 128 c1565824)) (Checked.append (checkChunk_sound 1565952 128 c1565952) (checkChunk_sound 1566080 128 c1566080))) (Checked.append (Checked.append (checkChunk_sound 1566208 128 c1566208) (checkChunk_sound 1566336 128 c1566336)) (Checked.append (checkChunk_sound 1566464 128 c1566464) (checkChunk_sound 1566592 128 c1566592))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1566720 128 c1566720) (checkChunk_sound 1566848 128 c1566848)) (Checked.append (checkChunk_sound 1566976 128 c1566976) (checkChunk_sound 1567104 128 c1567104))) (Checked.append (Checked.append (checkChunk_sound 1567232 128 c1567232) (checkChunk_sound 1567360 128 c1567360)) (Checked.append (checkChunk_sound 1567488 128 c1567488) (checkChunk_sound 1567616 128 c1567616)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1567744 128 c1567744) (checkChunk_sound 1567872 128 c1567872)) (Checked.append (checkChunk_sound 1568000 128 c1568000) (checkChunk_sound 1568128 128 c1568128))) (Checked.append (Checked.append (checkChunk_sound 1568256 128 c1568256) (checkChunk_sound 1568384 128 c1568384)) (Checked.append (checkChunk_sound 1568512 128 c1568512) (checkChunk_sound 1568640 128 c1568640)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1568768 128 c1568768) (checkChunk_sound 1568896 128 c1568896)) (Checked.append (checkChunk_sound 1569024 128 c1569024) (checkChunk_sound 1569152 128 c1569152))) (Checked.append (Checked.append (checkChunk_sound 1569280 128 c1569280) (checkChunk_sound 1569408 128 c1569408)) (Checked.append (checkChunk_sound 1569536 128 c1569536) (checkChunk_sound 1569664 128 c1569664)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1569792 128 c1569792) (checkChunk_sound 1569920 128 c1569920)) (Checked.append (checkChunk_sound 1570048 128 c1570048) (checkChunk_sound 1570176 128 c1570176))) (Checked.append (Checked.append (checkChunk_sound 1570304 128 c1570304) (checkChunk_sound 1570432 128 c1570432)) (Checked.append (checkChunk_sound 1570560 128 c1570560) (checkChunk_sound 1570688 128 c1570688))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1570816 128 c1570816) (checkChunk_sound 1570944 128 c1570944)) (Checked.append (checkChunk_sound 1571072 128 c1571072) (checkChunk_sound 1571200 128 c1571200))) (Checked.append (Checked.append (checkChunk_sound 1571328 128 c1571328) (checkChunk_sound 1571456 128 c1571456)) (Checked.append (checkChunk_sound 1571584 128 c1571584) (checkChunk_sound 1571712 128 c1571712)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1571840 128 c1571840) (checkChunk_sound 1571968 128 c1571968)) (Checked.append (checkChunk_sound 1572096 128 c1572096) (checkChunk_sound 1572224 128 c1572224))) (Checked.append (Checked.append (checkChunk_sound 1572352 128 c1572352) (checkChunk_sound 1572480 128 c1572480)) (Checked.append (checkChunk_sound 1572608 128 c1572608) (checkChunk_sound 1572736 128 c1572736)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B008
