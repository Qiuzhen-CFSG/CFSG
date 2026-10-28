module
public import Theory.GroupTheory.ProductDisconnected.InvolutionFusion
public import BenderSuzuki.ZD.Recognition.NativeSource

/-!
# The terminal ZD consequence of local involution fusion

If a subgroup contains an ambient Sylow two-subgroup, controls involution
fusion, and satisfies the distinguished-class centralizer criterion, a proper
such subgroup is product-disconnected. The proved simple Corollary ZD makes
it a solvable Borel subgroup. A nonsolvable subgroup satisfying these conditions
therefore equals the ambient nonabelian simple group.

Source application: Aschbacher--Smith13.4.9, printed pp.906--907. Nonsolvability
is available after recognition of the subgroup as Sp6(2); it supplies the
terminal contradiction directly.
-/

public section
namespace BenderSuzuki.ZD
open Theory.GroupTheory Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Local centralizer and fusion calculations close a nonsolvable subgroup in a
nonabelian simple ambient group; the full ZD theorem is discharged here. -/
theorem eq_top_of_involution_fusion (E : Subgroup G) (T : Sylow 2 G)
    (hs : IsSimpleGroup G) (hna : ¬ IsMulCommutative G) (hns : ¬ Group.IsSolvable E)
    (hTE : (T : Subgroup G) ≤ E) (d : G) (hd : BenderSuzuki.PFAppendixIII.IsInvolution d) (hdE : d ∈ E)
    (hf : ∀ a ∈ E, ∀ b ∈ E, BenderSuzuki.PFAppendixIII.IsInvolution a → IsConj a b →
      ∃ c ∈ E, MulAut.conj c a = b)
    (hc : centralizer ({d} : Set G) ≤ E)
    (hp : ∀ e ∈ E, IsConj d e → Commute d e → e ≠ d →
      centralizer ({d*e} : Set G) ≤ E) : E = ⊤ := by
  by_contra hE
  have hdisc := productDisconnected_of_involution_fusion E T hTE hE d hd hdE hf hc hp
  have hB := (simple_bender_borel _ E hdisc hs hna).2
  exact hns hB.1

end BenderSuzuki.ZD
