module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.SymmetricLocal
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Selection

/-!
# The orthogonal branch of Lemma 14.4.9

The exported source subgroups and normalizer deductions use the literal
conjugation convention, centralizers, two-core images and Sylow restrictions.
The elementary order-64 lift, its original-side centralizers and K₀U
normalization are proved from the actual irreducible moved section.
The two core identities, symmetric centralizers and original local Sylow
are now deduced from the actual selected component and action markings.
The complete lift, including chief modules and transvection identification,
is assembled by `lift_of_selected_configuration`. The full exclusion still
requires the involution/diagonal selection and precise Appendix A.3.14 application.
No result here consumes the legacy contradictory `Omega4PlusInput`.

Source: Aschbacher–Smith, printed pp.1009–1010.
-/
