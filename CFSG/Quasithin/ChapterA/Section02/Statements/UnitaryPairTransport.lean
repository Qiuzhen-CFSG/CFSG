module

public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Covering

/-!
# Transporting the literal exceptional unitary pair

An isomorphism carries both actual components, their embedded equal centers,
the ordered product decomposition and their unitary model parameters. This
supplies the top-subgroup witness required by Theorem A's existential form.

Source: Aschbacher–Smith A.2.1(1b) and A.2.12(II), printed pp.33,37.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02
universe u v
variable {G : Type u} {H : Type v} [Group G] [Group H]

private theorem map_center_equiv (e : G ≃* H) :
    (center G).map e.toMonoidHom = center H := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (centerCongr e ⟨x, hx⟩).property
  · intro y hy
    exact ⟨e.symm y, (centerCongr e).symm ⟨y, hy⟩ |>.property, e.apply_symm_apply y⟩

theorem TheoremAUnitaryPair.exception_of_centerQuotient [Finite G]
    (d : TheoremAUnitaryPair G) (hr : primeRank 3 G = 3)
    {S : Type u} [Group S] (e : S ≃* G ⧸ center G) :
    TheoremAException G S 3 := by
  let j : G ≃* (⊤ : Subgroup G) := topEquiv.symm
  have hc : (center G).map j.toMonoidHom = center (⊤ : Subgroup G) := map_center_equiv j
  refine ⟨rfl, ⊤, ?_, ⟨e.trans (QuotientGroup.congr _ _ j hc)⟩, ⟨d.map j⟩⟩
  exact (primeRank_equiv 3 j).symm.trans hr

end CFSG.Quasithin.ChapterA.Section02
