module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.SuzukiRecognition.RecognitionInput
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.SuzukiRecognition.Involutions
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.SuzukiRecognition.Assembly

/-!
# The Suzuki residual in J.2.9

`Choices.source_suzuki_recognition` proves all three clauses of J.2.9 from
explicit preceding J.2.3/J.2.7 witnesses. It constructs the actual Sz(8)
isomorphism, multiplication equivalence S₀ × L_s ≃ C_G(s), normalizer
factorization, outer cubic action and literal involution-class equality.
Its residual geometry includes transfer, the Sylow subgroup, omega equality,
uniform involution centralizers, TI and strong embedding.

`SuzukiSourceConclusion.oddPrime_local_consequences` supplies the exact
order, centralizer intersections and full local automizer used in J.2.10.
The final odd-complement construction and preceding-source assembly remain
with the parent Centralizers theorem. No recognition or SQTK property is
inserted into the Ru hypotheses.

Source: Aschbacher–Smith, J.2.9–10, printed p.438 (PDF p.449).
-/
