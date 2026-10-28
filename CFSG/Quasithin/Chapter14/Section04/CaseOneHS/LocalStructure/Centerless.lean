module

public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.FaithfulComponent
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.FaithfulExclusion
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.SolvableSeed
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.SolvableSeedAction
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.SolvableSeedSplitting
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.SolvableSeedRecognition
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.SolvableCentralQuotient
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.SolvableCentralSplitting
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.SolvableFullKernel
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.SolvableExclusion
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.ComponentLift
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.Shifted
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.ShiftedAmalgam
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.ShiftedAction
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.ShiftedMovement
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.ShiftedType
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.SymmetricFive
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.AlternatingSix
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.Orbit
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.DualQuotient
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.Thompson

/-!
# Source preparation for the HS centerlessness branch

The original selected counterexample supplies a central Sylow involution
whenever Z(I₂) is nontrivial. Its actual L-orbit, together with V, is a
reduced LT-module. The re-exported modules also construct the reduced
test module for 14.3.25, prove faithful-family membership for components
outside N_G(L), and construct the literal centralizer quotient for 14.3.31.
The shifted conjugator now supplies both the plane geometry and residual
generation. Assuming 14.3.25, the shifted centers are disjoint, and the
actual shifted involution constructs Ke inside its original centralizer.
The shifted center acts faithfully on the actual quotient U/Z(U), so the
chosen shifted involution has nontrivial image in that action. The two
displaced centralizers generate U, and their separate line bounds put the
whole shifted-center displacement inside the original V-hat. The alternating
displacement form gives order at most two and type a₂ for the nontrivial
shifted actor, conditional on the preceding seed exclusion.
The symmetric-five and alternating-six branches are now excluded using the actual marked moved
plane, the full Sylow image and the nontrivial point-residual action. Its
literal local-structure application retains the independent action premise.
The original central involution now has the exact stabilizer I₂T and an
orbit of seven elements. Its reduced orbit module is a quotient of that
binary permutation module with kernel O₂(LT), conditional on 14.3.25.
The same marked natural coordinates identify that orbit with the Fano lines.
The module calculation in 14.3.29(1) now gives dimensions 3, 4, 6 or 7 and
a surjective intertwiner onto the dual of the original V.
The natural and dual constituents now prove J(T) normal in LT, and hence
J(T) ≤ O₂(I₂T), still conditional on 14.3.25.

The faithful nonsolvable seed argument now constructs the original normal
component from the marked quotient row of 14.3.23--24, without assuming a
solvable action kernel. It constructs the A₅ quotient and kernel using the
faithful classifier, then contradicts its rank-one inner action on the reduced
test module. Its S₅/A₆ centerlessness and literal LocalStructure consumers
discharge the component and seed premises. Construction of the earlier marked
quotient alternatives remains independent.

The solvable seed branch now proves C_K(VH) <= C_K(U-hat) from the
original marked S3 image, its L1T supplement, and Sylow geometry. Its literal
centralizer quotient surjects onto the dotted S3, and a conjugate-center
actor survives on VH with displacement rank one and square acting trivially.
The entire marked center has the same cyclic image on VH. Consequently the
literal K-action image is the normal closure of this rank-one involution,
and the proved B.5 classification applies with faithfulness, trivial two-core
and an actual SQTK cover discharged. An S3 identification of that action
now gives equality of the literal kernels and a split commutator plane in
VH. The quotient kernel is normal in the whole H-action. This excludes the
two-factor and hyperplane rows; the perfect Sylow supplement excludes the
quasisimple row, and the rank-one offender argument excludes the outer row.
Thus the actual action is S3 without an additional model assumption, and
the original kernel equality and split VH-plane follow from the marked row.
The whole-center commutator now equals the same order-four VH-plane and
meets C_Z(U)(K) trivially. The literal quotient H/C_Z(U)(K) kills V1,
has elementary U-image, and preserves that commutator plane. Its marked
plane has order two and is Sylow-central, proving that U-image reduced
by B.2.13. Comparing the three successive layers now identifies the original
K-kernels on VH, Z(U), U-hat and the U-image in H/C_Z(U)(K). The actual
S3 action on Z(U) splits off its order-four commutator plane, proving the
whole-center splitting without assuming it in the kernel comparison.
The full hatted kernel now centralizes the moving plane, yielding equality
with the full kernel on the U-image in H/C_Z(U)(K). The resulting H-dot
isomorphism with the second centralizer quotient preserves both original
quotient maps. The original natural seed now embeds in that elementary
quotient. Normality of dotted L1 forces its fixed subgroup to be trivial,
so the original central LT seed lies in C_Z(U)(K). Its H-orbit then
centralizes K, contradicting the order-four commutator plane. The actual
S3 x S3 model supplies dotted L1 normality from its abelian two-residual
and the original Sylow normalization. This completes the solvable seed
contradiction conditional on the earlier marked row and model, and its
literal Thompson-containment consumer discharges the seed premise.
Constructing the earlier marked rows remains with this centerlessness owner;
the completed later action theorem assumes centerlessness.

The solvable model now constructs the marked seed row. In the original
Goldschmidt branch, the literal action kernel equals O₃′(Ke), the action
quotient is PSL₃(2), and the selected faithful component is the solvable
residual of Ke. Compatible parabolic markings then apply H.5.5 to Ue,
giving natural coordinates and order eight. The opposite dimension bound
and exhaustive centerlessness assembly remain with qt-d-hs-centerless-source.
This is preparation for 14.3.31; it does not assert its conclusion. Final local-structure assembly remains
with qt-d-hs-local-structure, including its independently produced action.

Source: Aschbacher--Smith, 14.3.25 and 14.3.28--31, printed pp.1001--1003.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual contrary-branch witness and reduced module, with all initial
subgroup, normalization, and characteristic-two premises discharged. -/
theorem source_contrary_reduced_module (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥) :
    ∃ e : G, orderOf e = 2 ∧ e ∈ Chapter12.Section08.centerIn (F.I₂ L) ∧
      e ∈ sylowOmega T ∧ e ∈ F.ZU ∧ e ∉ F.Vi 1 ∧
      IsPReduced 2 ((V ⊔ conjugateSpanBy (zpowers e) L).subgroupOf
        (L ⊔ (T : Subgroup G))) := by
  obtain ⟨e, he, heI, heT, heU, heV⟩ :=
    source_center_involution d earlier hq chosen structural alternatives F hne hI
  exact ⟨e, he, heI, heT, heU, heV,
    source_seed_sup_involution_orbit_reduced d earlier hq chosen structural F e he heT⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
