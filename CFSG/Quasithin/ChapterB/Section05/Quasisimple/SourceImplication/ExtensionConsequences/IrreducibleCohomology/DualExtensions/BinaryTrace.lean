module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.DualExtensions.G2Cocycles
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.DualExtensions.BinaryTrace.SylowGeometry

/-!
# Binary G₂ trace detection and the original-module supplement

A rank-three elementary abelian subgroup has order eight. The concrete octonion
geometry bounds any elementary abelian stabilizer of a trace-one class modulo
the identity line by four. Consequently every scalar-fixed octonion has trace
zero. This supplies the binary geometry premise of `g2Two_supplement_of_trace`
and hence proves its original-module conclusion, retaining the actual marked
commutator subgroup inside the full G₂(2) actor.

Source: Aschbacher–Smith, B.5.1(5), I.1.7(b), and B.4.6(3),(13), printed
pp.102–103, 408–409, and 88–90. The coordinate proof uses the licensed ATLAS
split-octonion model through the imports.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open Atlas.SplitOctonion
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences.DualExtensions

/-- Binary trace detection for the full G₂(2) actor on the eight octonion
coordinates. The elementary abelian rank already forces the obstruction. -/
theorem binary_traceDetection : G2TraceDetection BinaryField.two := by
  dsimp only [G2TraceDetection, BinaryField.two, mul_one]
  intro A hA hr x hx
  let : IsElementaryAbelian 2 A := hA.1.2
  have hcard : Nat.card A = 8 := by
    rw [hA.1.card_eq_two_pow_rank, hr]
    rfl
  have hb : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel
  rcases hb (trace x) with ht | ht
  · exact ht
  · have hle := BinaryTrace.card_le_four A x ht hx
    omega

universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

/-- The binary G₂ row of B.5.1(5), with its actual derived-subgroup marking:
the original module is the sum of its moved section and its G-fixed space. -/
theorem g2Two_supplement [Finite G] {K : CFSG.Quasithin.GroupClass.{u}}
    {L : Subgroup G} (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L)
    (e : MarkedActionEquiv s.action (offenderSubgroup s.action) L (g2Natural (ZMod 2))
      (commutator (Atlas.G2.Model (ZMod 2))))
    (hoff : ∀ A, IsBestOffender s.action A → rank A = 3)
    (hq : quadraticRatio s.action = 1) : s.space.toSubmodule ⊔ ρ.invariants = ⊤ :=
  g2Two_supplement_of_trace h s e hoff hq binary_traceDetection

end CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences.DualExtensions
