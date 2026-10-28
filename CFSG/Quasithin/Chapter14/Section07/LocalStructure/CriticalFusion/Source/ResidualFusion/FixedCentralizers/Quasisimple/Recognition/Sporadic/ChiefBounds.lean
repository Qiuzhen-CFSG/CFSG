module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Quasisimple.Recognition.Sporadic.Setup
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Quasisimple.Recognition.Sporadic.ChiefBounds.Transfer
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Quasisimple.Recognition.Sporadic.ChiefBounds.J2Native
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Quasisimple.Recognition.Sporadic.ChiefBounds.HSNative

/-!
# The J₂ and HS bounds on the original K's chief factors

The native centralizers `(Q₈ * D₈).A₅` and `(D₈ * D₈ * 4).S₅` have
two-residuals with at most one noncentral two-chief factor. Their proofs
use the actual core actions to establish chiefness of the core modulo its
center; the central initial interval and terminal A₅ quotient contribute
no noncentral two-chief factors.

The supplied marking of the literal two-core quotient induces a genuine
two-central inner action on the named carrier. Sylow-fixed lifting gives
a central surjection on fixed residuals, and the unchanged ambient inclusion
identifies the upstairs residual with K. Thus the native bounds apply to
every complete chief series of the original K, without any assumption on
the order of the covering kernel.

The final exclusion takes an explicit complete series with at least two
noncentral two-chief factors. Its independent producer is
`qt-14-07-fixed-dual-k-chief-factors`; the Ru sieve assembles that lower
bound with the unconditional upper bound proved here.

Source: Aschbacher–Smith 14.7.68(2), printed p.1071 / PDF p.1088,
and 1.1.5(3)(f), printed pp.502–503; GLS3 Tables 5.3g and 5.3m.
-/

public section
open Subgroup Theory.GroupTheory NoncentralChiefRefinement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 ClassificationModels
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

namespace Data
variable (d : Data T L V F W) (u : F.U) {Lu : Subgroup G}
  (α : MulAut (Lu.subgroupOf (d.fixedCentralizer u))) {name : SporadicName}
  (e : ((Lu.subgroupOf (d.fixedCentralizer u)) ⧸
    pCore 2 (Lu.subgroupOf (d.fixedCentralizer u))) ≃* name.Carrier)
  (h : SporadicSieve.Case d u Lu α name)

include e h

/-- Both native sporadic cases bound every complete chief series of the
original K through the supplied quotient marking and literal residual map. -/
theorem fixedJ2HS_noncentralTwoCount_le_one (hname : name = .j2 ∨ name = .hs)
    (s : ChiefSeries (K F)) (hs0 : s.head = ⊥) (hs1 : s.last = ⊤) :
    s.noncentralTwoCount ≤ 1 := by
  rcases hname with rfl | rfl
  · exact d.fixedJ2_noncentralTwoCount_le_one u α h e s hs0 hs1
  · exact d.fixedHS_noncentralTwoCount_le u α e h s hs0 hs1

/-- The 14.7.68(2) chief-count comparison excludes J₂ and HS once the
independent 14.5.21(1) lower-bound witness on this same K is supplied. -/
theorem fixedSporadic_not_j2_hs_of_two_le
    (s : ChiefSeries (K F)) (hs0 : s.head = ⊥) (hs1 : s.last = ⊤)
    (hcount : 2 ≤ s.noncentralTwoCount) : name ≠ .j2 ∧ name ≠ .hs := by
  have hn : ¬ (name = .j2 ∨ name = .hs) := by
    intro hname
    have hle := d.fixedJ2HS_noncentralTwoCount_le_one u α e h hname s hs0 hs1
    omega
  exact ⟨fun hj2 => hn (Or.inl hj2), fun hhs => hn (Or.inr hhs)⟩

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
