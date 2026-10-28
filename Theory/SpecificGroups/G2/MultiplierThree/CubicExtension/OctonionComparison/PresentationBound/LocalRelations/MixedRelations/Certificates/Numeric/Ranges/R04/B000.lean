module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [860160, 868352).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B000
private theorem c860160 : checkChunk 860160 128 = true := by decide +kernel
private theorem c860288 : checkChunk 860288 128 = true := by decide +kernel
private theorem c860416 : checkChunk 860416 128 = true := by decide +kernel
private theorem c860544 : checkChunk 860544 128 = true := by decide +kernel
private theorem c860672 : checkChunk 860672 128 = true := by decide +kernel
private theorem c860800 : checkChunk 860800 128 = true := by decide +kernel
private theorem c860928 : checkChunk 860928 128 = true := by decide +kernel
private theorem c861056 : checkChunk 861056 128 = true := by decide +kernel
private theorem c861184 : checkChunk 861184 128 = true := by decide +kernel
private theorem c861312 : checkChunk 861312 128 = true := by decide +kernel
private theorem c861440 : checkChunk 861440 128 = true := by decide +kernel
private theorem c861568 : checkChunk 861568 128 = true := by decide +kernel
private theorem c861696 : checkChunk 861696 128 = true := by decide +kernel
private theorem c861824 : checkChunk 861824 128 = true := by decide +kernel
private theorem c861952 : checkChunk 861952 128 = true := by decide +kernel
private theorem c862080 : checkChunk 862080 128 = true := by decide +kernel
private theorem c862208 : checkChunk 862208 128 = true := by decide +kernel
private theorem c862336 : checkChunk 862336 128 = true := by decide +kernel
private theorem c862464 : checkChunk 862464 128 = true := by decide +kernel
private theorem c862592 : checkChunk 862592 128 = true := by decide +kernel
private theorem c862720 : checkChunk 862720 128 = true := by decide +kernel
private theorem c862848 : checkChunk 862848 128 = true := by decide +kernel
private theorem c862976 : checkChunk 862976 128 = true := by decide +kernel
private theorem c863104 : checkChunk 863104 128 = true := by decide +kernel
private theorem c863232 : checkChunk 863232 128 = true := by decide +kernel
private theorem c863360 : checkChunk 863360 128 = true := by decide +kernel
private theorem c863488 : checkChunk 863488 128 = true := by decide +kernel
private theorem c863616 : checkChunk 863616 128 = true := by decide +kernel
private theorem c863744 : checkChunk 863744 128 = true := by decide +kernel
private theorem c863872 : checkChunk 863872 128 = true := by decide +kernel
private theorem c864000 : checkChunk 864000 128 = true := by decide +kernel
private theorem c864128 : checkChunk 864128 128 = true := by decide +kernel
private theorem c864256 : checkChunk 864256 128 = true := by decide +kernel
private theorem c864384 : checkChunk 864384 128 = true := by decide +kernel
private theorem c864512 : checkChunk 864512 128 = true := by decide +kernel
private theorem c864640 : checkChunk 864640 128 = true := by decide +kernel
private theorem c864768 : checkChunk 864768 128 = true := by decide +kernel
private theorem c864896 : checkChunk 864896 128 = true := by decide +kernel
private theorem c865024 : checkChunk 865024 128 = true := by decide +kernel
private theorem c865152 : checkChunk 865152 128 = true := by decide +kernel
private theorem c865280 : checkChunk 865280 128 = true := by decide +kernel
private theorem c865408 : checkChunk 865408 128 = true := by decide +kernel
private theorem c865536 : checkChunk 865536 128 = true := by decide +kernel
private theorem c865664 : checkChunk 865664 128 = true := by decide +kernel
private theorem c865792 : checkChunk 865792 128 = true := by decide +kernel
private theorem c865920 : checkChunk 865920 128 = true := by decide +kernel
private theorem c866048 : checkChunk 866048 128 = true := by decide +kernel
private theorem c866176 : checkChunk 866176 128 = true := by decide +kernel
private theorem c866304 : checkChunk 866304 128 = true := by decide +kernel
private theorem c866432 : checkChunk 866432 128 = true := by decide +kernel
private theorem c866560 : checkChunk 866560 128 = true := by decide +kernel
private theorem c866688 : checkChunk 866688 128 = true := by decide +kernel
private theorem c866816 : checkChunk 866816 128 = true := by decide +kernel
private theorem c866944 : checkChunk 866944 128 = true := by decide +kernel
private theorem c867072 : checkChunk 867072 128 = true := by decide +kernel
private theorem c867200 : checkChunk 867200 128 = true := by decide +kernel
private theorem c867328 : checkChunk 867328 128 = true := by decide +kernel
private theorem c867456 : checkChunk 867456 128 = true := by decide +kernel
private theorem c867584 : checkChunk 867584 128 = true := by decide +kernel
private theorem c867712 : checkChunk 867712 128 = true := by decide +kernel
private theorem c867840 : checkChunk 867840 128 = true := by decide +kernel
private theorem c867968 : checkChunk 867968 128 = true := by decide +kernel
private theorem c868096 : checkChunk 868096 128 = true := by decide +kernel
private theorem c868224 : checkChunk 868224 128 = true := by decide +kernel

public theorem checked : Checked 860160 868352 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 860160 128 c860160) (checkChunk_sound 860288 128 c860288)) (Checked.append (checkChunk_sound 860416 128 c860416) (checkChunk_sound 860544 128 c860544))) (Checked.append (Checked.append (checkChunk_sound 860672 128 c860672) (checkChunk_sound 860800 128 c860800)) (Checked.append (checkChunk_sound 860928 128 c860928) (checkChunk_sound 861056 128 c861056)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 861184 128 c861184) (checkChunk_sound 861312 128 c861312)) (Checked.append (checkChunk_sound 861440 128 c861440) (checkChunk_sound 861568 128 c861568))) (Checked.append (Checked.append (checkChunk_sound 861696 128 c861696) (checkChunk_sound 861824 128 c861824)) (Checked.append (checkChunk_sound 861952 128 c861952) (checkChunk_sound 862080 128 c862080))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 862208 128 c862208) (checkChunk_sound 862336 128 c862336)) (Checked.append (checkChunk_sound 862464 128 c862464) (checkChunk_sound 862592 128 c862592))) (Checked.append (Checked.append (checkChunk_sound 862720 128 c862720) (checkChunk_sound 862848 128 c862848)) (Checked.append (checkChunk_sound 862976 128 c862976) (checkChunk_sound 863104 128 c863104)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 863232 128 c863232) (checkChunk_sound 863360 128 c863360)) (Checked.append (checkChunk_sound 863488 128 c863488) (checkChunk_sound 863616 128 c863616))) (Checked.append (Checked.append (checkChunk_sound 863744 128 c863744) (checkChunk_sound 863872 128 c863872)) (Checked.append (checkChunk_sound 864000 128 c864000) (checkChunk_sound 864128 128 c864128)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 864256 128 c864256) (checkChunk_sound 864384 128 c864384)) (Checked.append (checkChunk_sound 864512 128 c864512) (checkChunk_sound 864640 128 c864640))) (Checked.append (Checked.append (checkChunk_sound 864768 128 c864768) (checkChunk_sound 864896 128 c864896)) (Checked.append (checkChunk_sound 865024 128 c865024) (checkChunk_sound 865152 128 c865152)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 865280 128 c865280) (checkChunk_sound 865408 128 c865408)) (Checked.append (checkChunk_sound 865536 128 c865536) (checkChunk_sound 865664 128 c865664))) (Checked.append (Checked.append (checkChunk_sound 865792 128 c865792) (checkChunk_sound 865920 128 c865920)) (Checked.append (checkChunk_sound 866048 128 c866048) (checkChunk_sound 866176 128 c866176))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 866304 128 c866304) (checkChunk_sound 866432 128 c866432)) (Checked.append (checkChunk_sound 866560 128 c866560) (checkChunk_sound 866688 128 c866688))) (Checked.append (Checked.append (checkChunk_sound 866816 128 c866816) (checkChunk_sound 866944 128 c866944)) (Checked.append (checkChunk_sound 867072 128 c867072) (checkChunk_sound 867200 128 c867200)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 867328 128 c867328) (checkChunk_sound 867456 128 c867456)) (Checked.append (checkChunk_sound 867584 128 c867584) (checkChunk_sound 867712 128 c867712))) (Checked.append (Checked.append (checkChunk_sound 867840 128 c867840) (checkChunk_sound 867968 128 c867968)) (Checked.append (checkChunk_sound 868096 128 c868096) (checkChunk_sound 868224 128 c868224)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B000
