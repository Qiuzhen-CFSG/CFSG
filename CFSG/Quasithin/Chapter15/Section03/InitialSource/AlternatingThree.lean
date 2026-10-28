module

public import CFSG.Quasithin.Chapter14.Section01.AlternatingThree.Source
public import CFSG.Quasithin.Chapter15.Section03.Constructions

/-!
# The original A₃ exclusion in the Chapter 15 local subgroup

The actual 14.1.10 theorem is applied to the original X≤M and R≤T∩M.
It excludes an alternating-three block whenever M differs from Mc or the
original Sylow omega-center has order two. The local core, Sylow embedding,
Thompson subgroup and central-involution subgroup are precisely the
Chapter 15 constructions. No marked replacement block is introduced.

Source: Aschbacher--Smith 14.1.10, printed p.978, used in the Section 15.3
local-block reductions, printed pp.1120--1146.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.InitialSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Literal source exclusion for the original Chapter 15 block and Thompson actor. -/
theorem alternating_three_excluded
    (h1391 : ∀ (H : Type u) [Group H] [Finite H],
      IsSimpleQTKE KnownSimple.IsKnownSimple H → Chapter13.Section09.Configuration H → False)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {M Mc : Subgroup G}
    (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (X R : Subgroup M) (hb : ChapterC.IsBlock X)
    (hQR : pCore 2 M ≤ R) (hRT : R ≤ (T.subtype hM.2 : Subgroup M))
    (hm : X = ⁅X,elementaryAbelianMaxJ R⁆)
    (haway : M ≠ Mc ∨ Nat.card (centralInvolutions T) = 2) :
    ¬ ChapterC.IsAlternatingBlock X 3 := by
  intro ha
  obtain ⟨he,hZ⟩ := Chapter14.AlternatingThree.source_lemma_14_1_10
    h1391 hG T hM hu hmany X R hb ha hQR hRT hm
  rcases haway with hne | hcard
  · exact hne he
  · change 2 < Nat.card (centralInvolutions T) at hZ
    omega

end CFSG.Quasithin.Chapter15.Section03.InitialSource
