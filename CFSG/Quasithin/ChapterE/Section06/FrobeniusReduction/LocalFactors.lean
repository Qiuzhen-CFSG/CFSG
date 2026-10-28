module

public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.Conjugates
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.Enlargement

/-!
# Local factors in the proof of E.6.25

The cyclic conjugates are realized inside N_G(U), and the prime-rank bound
is proved for a genuine commuting lift family. The exceptional summands
supply an obstruction V₂, transport the Sylow subgroup to C_G(V₂), and
construct a properly containing C-component with fixed-space corank three
from the explicit earlier component theorems.

Two obligations remain before the local-factor argument is complete:
construct a commuting cyclic lift family using the local component action,
and carry out the component-versus-block model sieve for the enlarged
component, followed by the incompatible E.6.8 ranks. The theorems here do
not assert E.6.25 before these hypotheses have been discharged.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
E.6.25, printed pp.255–256 (PDF pp.266–267).
-/
