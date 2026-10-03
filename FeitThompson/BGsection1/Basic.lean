module

public import FeitThompson.BGsection1.Defs
public import FeitThompson.BGsection1.CentralizerLemmas
public import FeitThompson.BGsection1.CriticalSubgroupLemmas
public import FeitThompson.BGsection1.PLengthLemmas
public import FeitThompson.Commutator.FocalSubgroup
public import FeitThompson.GroupAction.CentralizerCondition
public import Theory.GroupAction.CoprimeHall
public import Theory.GroupAction.FixedPointTransport
public import FeitThompson.GroupAction.NoncyclicAbelianPGroup
public import FeitThompson.GroupAction.SeriesPiGroup
public import FeitThompson.PCore.CentralizerControl
public import Theory.GroupAction.NormalComplement
public import Theory.GroupTheory.Commutator.ActionTriviality
public import Theory.Frattini.CoprimeAction
public import Theory.GroupTheory.Commutator.CyclicSylow
public import Theory.GroupTheory.Commutator.Basic
public import Theory.ElementaryAbelian.VectorSpace
public import FeitThompson.Fitting.Centralizer
public import FeitThompson.Fitting.Core
public import FeitThompson.Fitting.Faithful
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import FeitThompson.PGroup.OmegaFrattini
public import Mathlib.GroupTheory.SpecificGroups.ZGroup

public import Theory.GroupTheory.Hall.Basic
public import FeitThompson.ChiefFactors.BaerCore


open scoped Pointwise

public section

theorem centerIn_eq_map_center_local {G : Type*} [Group G] (H : Subgroup G) :
    centerIn H = (Subgroup.center H).map H.subtype := by
  simp [centerIn]
  ext x
  constructor
  · rintro ⟨hxH, hx_centralizer⟩
    refine ⟨⟨x, hxH⟩, ?_, rfl⟩
    exact Subgroup.mem_center_iff.mpr fun h =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hx_centralizer (h : G) h.property)
  · rintro ⟨h, hh, rfl⟩
    refine ⟨h.property, ?_⟩
    intro g hg
    calc
      g * (h : G) = (⟨g, hg⟩ * h : H).val := by simp
      _ = (h * ⟨g, hg⟩ : H).val := by
            rw [Subgroup.mem_center_iff.mp hh ⟨g, hg⟩]
      _ = (h : G) * g := by simp


end
