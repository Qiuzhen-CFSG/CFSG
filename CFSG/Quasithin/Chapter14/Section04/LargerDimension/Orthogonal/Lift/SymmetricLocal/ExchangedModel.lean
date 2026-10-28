module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.SymmetricLocal.Core
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.SymmetricLocal.Symmetry
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.SymmetricLocal.ExchangedModel.JointCore
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.SymmetricLocal.ExchangedModel.Cubic
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.SymmetricLocal.ExchangedModel.MovedSection
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.SymmetricLocal.ExchangedModel.Interchange
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.SymmetricLocal.ExchangedModel.Assembly

/-!
# Component interchange and the exchanged orthogonal lift

From D=O₂(C_G(⟨z,zˣ⟩)), |D|=64 and |U|=512, the joint-core argument
proves z∉Uˣ and that the exchanged moved image has more than four elements.
The involution centralizer in Uˣ has at least sixteen elements. Intersecting
it with a sixteen-element fixed subgroup in D rules out any actor fixing
only the center of Uˣ.

The actual case-(3) action coordinates now construct the residual matrix
image and prove moved order sixteen and irreducibility. The original
marked A₅ quotient supplies nonsolvability. Applying
`symmetric_lift_of_exchanged_moved_section` proves normalization of D by Uˣ
and its fixed line ⟨zˣ⟩. These deductions retain the earlier source action
markings explicitly. Cubic actors lift through the actual two-group kernel,
and the original marked action proves their fixed-point bound. This excludes
the preserving alternative and proves component interchange without a symmetry
certificate. `exchanged_components_and_symmetric_lift` assembles interchange,
both exchanged moved-section premises, and their symmetric-lift application.

The earlier action markings remain with the selection producer. The parent
SymmetricLocal task retains their instantiation, the common-core premises,
and the remaining source-lemma assembly.

Source: Aschbacher–Smith, Lemma 14.4.9, printed p.1010.
-/
