module
public import Stellmacher.SectionsOneToFourDefs

/-!
# Native unique maximal containment

A subgroup `T` of `P` whose ambient image lies in a unique maximal subgroup
of `P` has the same uniqueness property when `P` is treated as the ambient
group and its ambient subgroup is `⊤`. No finiteness or Sylow hypothesis is
needed: this is transport through the subgroup lattice equivalence induced
by `Subgroup.topEquiv`. Injectivity of the inclusion of `P` reflects the
containment condition.

This supplies the native-group form of the `PSet` uniqueness hypothesis
for applications of Stellmacher (2.4), including the proof of (4.6).
Source: the definition `IsUniqueMaximalContaining` and elementary subgroup
lattice transport, accompanying `refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher

/-- Express unique maximal containment in the native ambient subgroup. -/
public theorem native_uniqueMaximalContaining
    {G : Type*} [Group G] (P : Subgroup G) (T : Subgroup P)
    (h : IsUniqueMaximalContaining (T.map P.subtype) P) :
    IsUniqueMaximalContaining T (⊤ : Subgroup P) := by
  obtain ⟨M, hM, hTM, hunique⟩ := h
  let e : (⊤ : Subgroup P) ≃* P := Subgroup.topEquiv
  have he : e.toMonoidHom = (⊤ : Subgroup P).subtype := rfl
  have hTM' : T ≤ M := Subgroup.map_subtype_le_map_subtype.mp hTM
  let N := M.map e.symm.toMonoidHom
  have hNmap : N.map (⊤ : Subgroup P).subtype = M := by
    rw [← he]
    dsimp only [N]
    rw [Subgroup.map_map]
    simp
  refine ⟨N, (OrderIso.isCoatom_iff e.symm.mapSubgroup M).2 hM, ?_, ?_⟩
  · rwa [hNmap]
  · intro N' hN' hTN'
    have hN'M : N'.map e.toMonoidHom = M := by
      apply hunique
      · exact (OrderIso.isCoatom_iff e.mapSubgroup N').2 hN'
      · exact Subgroup.map_mono (by simpa only [he] using hTN')
    apply e.mapSubgroup.injective
    change N'.map e.toMonoidHom = N.map e.toMonoidHom
    rw [he, hNmap] at *
    exact hN'M

end Stellmacher
