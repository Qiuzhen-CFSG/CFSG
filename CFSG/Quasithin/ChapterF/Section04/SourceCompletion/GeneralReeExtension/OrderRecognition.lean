module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.GeneralReeExtension.FixedApartment

/-!
# Recognition of small completions of full general Ree extensions

For every positive Ree parameter, the full carrier order bound closes the
marked apartment in the native subcompletion. The resulting literal Weyl
relation feeds the paired-completion comparison. Thus the supplied group
has the full extension order and a faithful type-preserving action on the
native Ree group containing all inner automorphisms. Original ambient
simplicity removes the outer part. No extra geometric or relation premise
remains; whole overlap and the bound against the full extension are retained.

Source: Aschbacher–Smith F.4.10,16–17,24, printed pp.279,282–283,287–288.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.GeneralReeExtension
open Subgroup Theory.GroupTheory ReeF4.Parabolics
variable {m : ℕ} (E : SourceExtension m) {M : Type*} [Group M] [Finite M] (c : Completion E M)

/-- The full positive-parameter Ree recognition theorem with exactly the
whole-overlap and full-extension order hypotheses. -/
theorem faithful_extension_of_order_bound (hm : 0 < m)
    (ho : c.left.range ⊓ c.right.range=c.middle.range)
    (horder : Nat.card M≤Nat.card E.carrier) :
    Nat.card M = Nat.card E.carrier ∧
      ∃ a : M →* MulAut (ReeF4.Model m), Function.Injective a ∧
        (MulAut.conj : ReeF4.Model m →* MulAut (ReeF4.Model m)).range ≤ a.range ∧
        ∀ g : M, UnitaryNonbinary.PreservesTypes
          (parabolic m .linear) (parabolic m .suzuki) (a g) :=
  faithful_extension_of_weyl_relation E c hm ho (weylProduct_eight_eq_one E c hm ho horder)

/-- A simple order-bounded completion is the actual native Ree group. -/
theorem nonempty_native_mulEquiv_of_simple_of_order_bound [IsSimpleGroup M]
    (hm : 0 < m) (ho : c.left.range ⊓ c.right.range=c.middle.range)
    (horder : Nat.card M≤Nat.card E.carrier) : Nonempty (M ≃* ReeF4.Model m) :=
  nonempty_native_mulEquiv_of_simple_of_weyl_relation E c hm ho
    (weylProduct_eight_eq_one E c hm ho horder)
end CFSG.Quasithin.ChapterF.SourceCompletion.GeneralReeExtension
