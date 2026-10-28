module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.Reduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.FixedKernel

/-!
# The abelian binary MS core branch

For an abelian commutator core D = [O₂(J),L], the genuine binary MS hypotheses
give a quotient D/C_D(L) consisting of one or two natural SL₃(2) modules.
The fixed kernel has order at most two, and is trivial in the two-copy case.
The equivariant square map and [D,L] = D prove exponent two, including in
the exceptional extension of order sixteen. The resulting orders 8, 16 and
64 give actual elementary-group models in dimensions 3, 4 and 6.

Source: Aschbacher–Smith C.1.31–34, combined manuscript (1 March 2004),
printed pp.135–137, especially alternatives (1), (2), (5) of C.1.34.
-/

public section

namespace CFSG.Quasithin.ChapterC.BinaryMS

universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J}

/-- The abelian commutator core of a genuine binary MS group is an elementary
two-group of dimension three, four or six. The natural quotient and its fixed
kernel bounds are proved from the MS input, rather than additional premises. -/
theorem Input.abelianCore_model
    (h : Input κ L R) (hc : IsMulCommutative (commutatorCore L)) :
    ∃ d : ℕ, (d = 3 ∨ d = 4 ∨ d = 6) ∧
      Nonempty (commutatorCore L ≃* Multiplicative (Fin d → ZMod 2)) := by
  obtain ⟨m, hm, ⟨q⟩⟩ :=
    AbelianCore.QuotientRecognition.Input.exists_abelianCore_naturalQuotient (h := h) hc
  obtain ⟨hfixed, hdouble⟩ := h.abelianCore_fixedKernel_bounds hc hm q
  exact h.abelianCore_model_of_naturalQuotient hc q hm hfixed hdouble

end CFSG.Quasithin.ChapterC.BinaryMS
