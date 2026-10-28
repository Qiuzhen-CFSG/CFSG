module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.FixedKernel.OneCopy
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.FixedKernel.DoubleCopy

/-!
# Fixed kernels of binary natural MS quotients

Let D = [O₂(J),L] be abelian, and suppose its quotient by the literal fixed
subgroup C_D(L) is equivariantly identified with one or two natural binary
SL₃(2) modules. Universal-cover duality bounds |C_D(L)| by two in the one-copy
case. In the two-copy case, MS3 supplies a faithful FF-action on D, and the
cover-rigidity theorem excludes every nontrivial fixed extension.

Combining these branches gives |C_D(L)| ≤ 2, with equality to one whenever
there are two natural copies. Existence of the supplied natural quotient
remains a separate obligation for the source-theorem assembly.

Source: Aschbacher–Smith C.1.31(MS3), C.1.34(1),(2),(5), combined manuscript
(1 March 2004), printed pp.135–137.
-/

public section

namespace CFSG.Quasithin.ChapterC.BinaryMS

universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J}

/-- The fixed kernel of an abelian binary MS core has order at most two
when its fixed quotient consists of one or two natural modules. For two
copies the kernel is trivial. The natural quotient is explicit input. -/
theorem Input.abelianCore_fixedKernel_bounds
    (h : Input κ L R) (hc : IsMulCommutative (commutatorCore L))
    {m : ℕ} (hm : m = 1 ∨ m = 2) (q : AbelianCore.NaturalQuotient h m) :
    Nat.card (coreFixed L) ≤ 2 ∧ (m = 2 → Nat.card (coreFixed L) = 1) := by
  rcases hm with rfl | rfl
  · exact ⟨h.abelianCore_fixedKernel_le_two_of_oneCopy hc q, by simp⟩
  · have hfixed := h.abelianCore_fixedKernel_eq_one_of_twoCopies hc q
    exact ⟨hfixed.le.trans (by decide), fun _ => hfixed⟩

end CFSG.Quasithin.ChapterC.BinaryMS
