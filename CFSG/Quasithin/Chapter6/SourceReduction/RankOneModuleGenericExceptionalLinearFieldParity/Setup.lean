module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericCartan
public import CFSG.Quasithin.Chapter3.Section02.Setup
public import CFSG.Quasithin.ChapterF.Section08
public import CFSG.KnownSimple.CarrierCatalogue
public import Stellmacher.OmegaOneCenterMap

/-!
# The literal configuration for the odd-exponent argument

In the proof of 5.1.17 the module is chosen anew from the Fundamental
Setup. The five F.8 subgroups are then V, Z∩V, L, T and H D_L.
The record below specifies the output needed from the first part of that
argument. Its existence is a separate source obligation; neither parity
nor an inconsistent pair of numerical bounds is a field of the record.

The later displacement statements concern the actual action on U/(Z∩V),
where U is the H D_L-span of the selected V. In particular an involution
means an involution modulo O₂(H D_L), rather than an arbitrary lift of
order two in H D_L. All centralizers and normality assertions remain
relative to the displayed groups.

Source: Aschbacher–Smith, 5.1.17, printed pp.640–642
(`refs/quasithin.pdf`, PDF pp.657–659).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity

variable {G : Type*} [Group G] [Finite G]

/-- F.8's five subgroups, with the actual left Cartan A=D_L.
W denotes the module selected in the proof of 5.1.17. -/
def setup (T : Sylow 2 G) (L W H A : Subgroup G) : ChapterF.Section08.Setup G where
  V := W
  V₁ := Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ W
  L := L
  T := T
  H := H ⊔ A

/-- Construction target for the first part of the odd-exponent argument.
These are source inputs to the two independent final calculations, not
a theorem asserting that such a configuration exists. -/
structure Seed (T : Sylow 2 G) (L H A : Subgroup G) (n : ℕ) where
  V : Subgroup G
  fundamental : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L
  module_eq : fundamental.moduleSubgroup = V
  natural : IsNaturalModule L V n
  f8 : (setup T L V H A).Hypothesis
  point_card : Nat.card (setup T L V H A).V₁ = 2 ^ n
  point_TI : ∀ g : G,
    (setup T L V H A).V₁ ⊓
        (setup T L V H A).V₁.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      (setup T L V H A).V₁.map (MulAut.conj g).toMonoidHom =
        (setup T L V H A).V₁
  cartan_central :
    (A.subgroupOf (H ⊔ A)).map (QuotientGroup.mk' (pCore 2 (H ⊔ A : Subgroup G))) ≤
      center ((H ⊔ A : Subgroup G) ⧸ pCore 2 (H ⊔ A : Subgroup G))
  moved : ⁅(setup T L V H A).U, A⁆ ⊔ (setup T L V H A).V₁ =
    (setup T L V H A).U
  quotient_rank : primeRank 2 ((H ⊔ A : Subgroup G) ⧸ pCore 2 (H ⊔ A : Subgroup G)) ≤ 4

/-- The codimension of the fixed space on the literal U/V₁.
The action construction identifies this subgroup index with its linear
meaning; the definition itself requires no ambient normality of V₁. -/
def displacement (E : ChapterF.Section08.Setup G) (y : G) : ℕ :=
  Nat.log 2 ((commutatorPreimage E.U (zpowers y) E.V₁).relIndex E.U)

/-- The representation calculation on printed p.641, for every nonidentity
involution of the actual H₁/O₂(H₁). -/
def LargeDisplacement (E : ChapterF.Section08.Setup G) : Prop :=
  ∀ y ∈ E.H, y ^ 2 ∈ E.QH → y ∉ E.QH → 9 ≤ displacement E y

/-- The small mover constructed by the terminal critical-pair argument.
The source first obtains a bound of three in the centralized branch, and
then a bound of seven in the remaining branch. -/
def SmallMover (E : ChapterF.Section08.Setup G) : Prop :=
  ∃ y ∈ E.H, y ^ 2 ∈ E.QH ∧ y ∉ E.QH ∧ displacement E y ≤ 7

/-- First source obligation: construct the specialized module and all
F.8.1 hypotheses for the supplied compatible Cartans. -/
def OddSeedSource (T : Sylow 2 G) (L H : Subgroup G) (n : ℕ) : Prop :=
  ∀ A B : Subgroup G, CartanPair T L H A B → Odd n → Nonempty (Seed T L H A n)

/-- Independent representation-theoretic obligation, conditional on the
configuration produced by the first source obligation. -/
def DisplacementSource (T : Sylow 2 G) (L H : Subgroup G) (n : ℕ) : Prop :=
  ∀ A B : Subgroup G, CartanPair T L H A B → Odd n →
    ∀ s : Seed T L H A n, LargeDisplacement (setup T L s.V H A)

/-- Independent critical-pair obligation. The displacement lower bound
is available as a premise, so this proof can proceed before its producer. -/
def CriticalSource (T : Sylow 2 G) (L H : Subgroup G) (n : ℕ) : Prop :=
  ∀ A B : Subgroup G, CartanPair T L H A B → Odd n →
    ∀ s : Seed T L H A n, LargeDisplacement (setup T L s.V H A) →
      SmallMover (setup T L s.V H A)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
