module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceB513.SplitModels
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceB513.SL2G2
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceB513.Symplectic
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.EndNodeRank
public import Theory.Representation.BinaryOffender.SmallDimensionDualFF
/-!
# Split moved sections in the dual B.5.13 estimate

A complement to the component fixed space has zero central kernel, so its
actual moved quotient identifies equivariantly with the moved space. Small
quotients use the uniform dimension-nine estimate. The SL₃ row uses its graph
automorphism after restricting a genuine offender to the generated component.

Source: Aschbacher–Smith B.5.13, printed pp.110–111.
-/

public section
open Representation Representation.BinaryOffender Subgroup
namespace CFSG.Quasithin.ChapterB.SourceB513
open QuasisimpleSource QuasisimpleSource.ExtensionConsequences
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem central_eq_bot (s : MovedSection ρ L)
    (hc : IsCompl s.space.toSubmodule (fixedSpace ρ L)) : s.central.toSubmodule = ⊥ := by
  rw [s.central_eq]
  apply bot_unique
  intro v hv
  apply Subtype.ext
  exact (disjoint_iff.mp hc.disjoint).le ⟨v.property, fun g => congrArg Subtype.val (hv g)⟩

noncomputable def splitQuotientEquiv (s : MovedSection ρ L)
    (hc : IsCompl s.space.toSubmodule (fixedSpace ρ L)) :
    ActionEquiv s.action s.space.toRepresentation where
  groupEquiv := MulEquiv.refl G
  linearEquiv := s.central.toSubmodule.quotEquivOfEqBot (central_eq_bot s hc)
  intertwines g v := by
    induction v using Submodule.Quotient.induction_on with | _ v => rfl

theorem small_moved_dual_bound (s : MovedSection ρ L)
    (hc : IsCompl s.space.toSubmodule (fixedSpace ρ L))
    (hff : IsFFModule ρ)
    (hdim : Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) ≤ 9) :
    quadraticRatio s.space.toRepresentation.dual ≤ 2 := by
  apply dual_quadraticRatio_le_two_of_small_FF s.space.toRepresentation
  · obtain ⟨A,hA⟩ := hff
    exact ⟨A,hA.1,(fixedCodim_subrepresentation_le ρ s.space A).trans hA.2⟩
  · rwa [← (splitQuotientEquiv s hc).linearEquiv.finrank_eq]

theorem linearThree_moved_dual_bound (s : MovedSection ρ L)
    (hc : IsCompl s.space.toSubmodule (fixedSpace ρ L))
    (hff : IsFFModule ρ) (hgen : offenderSubgroup s.action = L)
    (F : BinaryField) (e : ActionEquiv (s.action.comp L.subtype) (linearNatural F 3)) :
    quadraticRatio s.space.toRepresentation.dual ≤ 2 := by
  let q := splitQuotientEquiv s hc
  have hffU : IsFFModule (G := G) (V := s.space.toSubmodule) s.space.toRepresentation := by
    obtain ⟨A,hA⟩ := hff
    exact ⟨A,hA.1,(fixedCodim_subrepresentation_le ρ s.space A).trans hA.2⟩
  have hffQ : IsFFModule s.action := hffU.map_equivariant _ _
    (actionSymm q).groupEquiv.toMonoidHom (actionSymm q).groupEquiv.injective
    (actionSymm q).linearEquiv (actionSymm q).intertwines
  obtain ⟨A,hA⟩ := hffQ
  obtain ⟨B,_,hB,_,_⟩ := hA.exists_quadratic_minimalBestOffender s.action
  have hBL : B ≤ L := hgen ▸ hB.1.le_offenderSubgroup s.action
  have hffL : IsFFModule (s.action.comp L.subtype) :=
    ⟨B.subgroupOf L,(hB.1.subgroupOf s.action hBL).isOffender _⟩
  have hqL : quadraticRatio (Representation.dual (s.action.comp L.subtype)) ≤ 2 :=
    dual_bound_of_marked_ratio e
      (SourceCompletion.linearThreeGraphDualAction F).quadraticRatio_eq.symm hffL
  have hqQ : quadraticRatio s.action.dual ≤ 2 := by
    apply (quadraticRatio_le_of_injective_equivariant (Representation.dual (s.action.comp L.subtype))
      s.action.dual L.subtype L.subtype_injective (LinearEquiv.refl _ _) ?_).trans hqL
    intro g v
    apply LinearMap.ext
    intro w
    rfl
  rwa [q.dual.quadraticRatio_eq] at hqQ
end CFSG.Quasithin.ChapterB.SourceB513
