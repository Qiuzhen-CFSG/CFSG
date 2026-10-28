module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.Frames
public import BenderSuzuki.SE.InvolutionsInTwoSubgroups
/-!
# Type U₄(3) excludes strongly embedded subgroups

The original IsType configuration supplies an elementary four-group and
an involutive frame a,b in the actual extraspecial two-core, with
b*a = a*b*z. Since z is the specified nonidentity involution, this frame
does not commute. The full Bender–Suzuki corollary contradicts that pair.
No ambient simple-group, stabilizer model, solvability, or odd-core premise
is added to the original source hypotheses.

Source: Aschbacher, Sporadic Groups (1994), 45.2–45.3 and the final
strong-embedding step of 45.11, printed pp.242–243,248–249.
-/
public section
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
open Subgroup BenderSuzuki BenderSuzuki.PFchapter1section1
variable {G : Type*} [Group G] [Finite G] {z : G}
theorem IsType.not_stronglyEmbedded (h : IsType z) (M : Subgroup G) :
    ¬ BenderSuzuki.IsStronglyEmbedded M := by
  intro hM
  obtain ⟨R⟩ := h.exists_rootPair
  obtain ⟨a,b,ha,hb,ha2,hb2,hab,_⟩ := R.exists_left_frame h
  have hr : TwoRankAtLeastTwo G := by
    let : IsElementaryAbelian 2 R.E := R.E_elementary h
    refine ⟨R.E,R.E_card h,?_⟩
    intro x
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian (A:=R.E) (x:G) x.property
  have hQ : IsPGroup 2 (core z) := isPGroup_pCoreIn 2 (residual z)
  have hc := hM.squares_commute_in_twoSubgroup hr (core z) hQ a b ha.1 hb.1 ha2 hb2
  have he : a*b=a*b*z := hc.eq.trans hab
  have hz : z=1 := (mul_left_cancel (a:=a*b) (by simpa using he.symm))
  have hi:=h.involution
  simp [hz] at hi
end Theory.GroupTheory.Recognition.UnitaryFourThree
