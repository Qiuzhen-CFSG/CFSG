module

public import Theory.SpecificGroups.ReeTwo.CoreQuotientCenter
public import Theory.SpecificGroups.ReeTwo.CentralizerResidualObstruction
public import Theory.SpecificGroups.ReeTwo.ParabolicSourceObstruction
public import Theory.SpecificGroups.ReeTwo.CoreOmegaDerived
public import Theory.SpecificGroups.ReeTwo.ParabolicCoreStructure
public import Theory.SpecificGroups.ReeTwo.ParabolicConcreteOrbits
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.Parabolics.Overgroups

/-!
# Concrete Ree local calculations for Lemma 14.2.21

The verified root-and-Weyl comparisons now identify the coordinate locals
with the actual first parabolics in `ReeF4.Model 0` and the Atlas Tits group.
The Tits local is the mixed-character kernel. `ReeTwo.ParabolicConcrete`
computes the following subgroups, quotients and actions inside those actual
parabolics. Final assembly of H = Mc in Lemma 14.2.21 remains with the parent.

* The full-Ree normal core is its intrinsic two-core, of order 1024;
  its quotient is the specified faithful C5:C4 group. The actual Tits core
  has order 512 and the same quotient, with compatible Suzuki projections.
* Its derived subgroup E is elementary abelian of order 32 and equals its
  second center. Its centralizer F in the whole local model lies in the core,
  has order 64, and equals ⟨v5⟩E.
* The quotient QH/F is elementary abelian of order sixteen. The actual
  conjugation action has an image of order divisible by five and has no
  nontrivial proper invariant subgroup.
* The chosen cyclic-five complement X has C_QH(X) = ⟨v5⟩, cyclic of order
  four. Core involutions outside F exist and form one local conjugacy class.
* The characteristic subgroup Ω₁(QH) has order 512, intersects F in E,
  and joins F to QH. Its own derived subgroup is E, which is characteristic
  and self-centralizing there. The literal Tits-to-Ree embedding maps the
  Tits core onto this omega subgroup. This extra invariant subgroup is retained.
* In the actual Tits parabolic E has order 32 and F = E. Its quotient QH/F
  is elementary of order sixteen with irreducible actual conjugation action;
  the five-fixed subgroup is the marked central involution subgroup. The
  involutions in QH minus F exist and form one Tits-parabolic conjugacy class.
* Both actual H/F representations are faithful in the binary five-space
  stabilizer of the source mark Z. Their core images are exactly its
  translation subgroup. The embedding of E and its conjugation formula
  are supplied, as are the normality reductions for faithful extensions to
  Mc/F. Both H/QH quotients have cyclic Sylow two-subgroups.

Two formulas in the original requested intermediate package conflict with
the source relations. Their obstruction theorems remain exported:

* Source root v5 centralizes the derived subgroup of the ten-root core,
  but its coset modulo the center is not central. Thus the image of this
  centralizer is not the quotient center. The relation-only obstruction
  proves this without assuming compatibility with an ambient Ree model:
  [v5,v7] = v11 and [v3,v11] = v12, whereas v3 centralizes v12.
* In the concrete centralizer semidirect product, root v5 does not
  centralize the two-residual: a conjugate of an order-five complement
  element witnesses this. Source (3.2.7) states C_J(X) = ⟨v5⟩ for the
  cyclic-five complement X, not C_J(O²(H)) = ⟨v5⟩.

Source (3.2.6) explicitly gives Sz(2), of order twenty, for the full-Ree
parabolic quotient. Parrott (1972), printed p.672, uses the Frobenius
quotient of order twenty for the Tits centralizer as well. The D10
quotient belongs to the parity-character kernel, which is not the actual
Tits parabolic. The quotient assignments use the verified ambient maps.

The core is defined by root coordinates in `ReeTwo.Core`; `root i` is
source root v(i+3). The ambient comparisons preserve the specified Sylow
subgroups, their whole parabolic
overlap, and the source Z = Ω₁(Z(T)). These concrete facts discharge the
model premises; the parent still supplies the source ambient configuration
and any larger-group action used in the final overgroup argument.

Sources: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript, Lemma 14.2.21, printed p.989 (PDF p.1006); Aschbacher,
*The Tits group as a standard subgroup*, Math. Z.181 (1982), (3.1),
(3.2.2–7), printed pp.233–234; Parrott, *A characterization of the Tits'
simple group*, Canad. J. Math.24 (1972), printed p.672.
-/
