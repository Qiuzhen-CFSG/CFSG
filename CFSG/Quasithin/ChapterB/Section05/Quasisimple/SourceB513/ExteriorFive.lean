module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceB513.IrreducibleTransport

/-!
# The exterior-five row in the dual B.5.13 bound

The actual ten-dimensional section has a quadratic minimal best offender.
The source marks that offender as an end-node radical, giving rank four.
If its fixed codimension is at most two, a nonidentity involution gives the
dual bound. Otherwise quadraticity puts the moved space inside a fixed space
of dimension at most seven, again at most twice the offender rank.

A complement to the component-fixed space identifies this literal quotient
with the original moved space, and transports the bound to its dual.

Source: Aschbacher–Smith, B.4.2(11) and B.5.13, printed pp.86 and 110–111.
-/

public section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceB513
open QuasisimpleSource QuasisimpleSource.ExtensionConsequences
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

private theorem rank_four_dual_bound
    (σ : Representation (ZMod 2) G V) {A : Subgroup G}
    (hA : IsElementaryTwo A) (hq : IsQuadratic σ A) (hr : rank A = 4)
    (hdim : Module.finrank (ZMod 2) V = 10) : quadraticRatio σ.dual ≤ 2 := by
  by_cases hc : fixedCodim σ A ≤ 2
  · apply quadraticRatio_le_two_of_dual_fixedCodim_le_two σ.dual hA
    have he : fixedCodim σ.dual.dual A = fixedCodim σ A := by
      rw [fixedCodim_dual_eq_moved_finrank, subspaceCommutator_top_eq_coinvariants]
      exact (finrank_quotient_invariants_eq_dual_commutator (σ.comp A.subtype)).symm
    rwa [he]
  have hm : subspaceCommutator σ ⊤ A ≤ fixedSpace σ A := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, v, _, rfl⟩ b
    exact hq b b.property a ha v
  have hmrank := Submodule.finrank_mono hm
  have htotal := fixedCodim_add_finrank σ A
  apply (quadraticRatio_le_two_iff σ.dual).mpr
  refine ⟨A, hA, (isQuadratic_dual_iff σ A).mpr hq, ?_⟩
  rw [fixedCodim_dual_eq_moved_finrank]
  omega

/-- The exterior-five source row gives the dual bound on the original moved space. -/
theorem exteriorFive_moved_dual_bound (s : MovedSection ρ L)
    (hc : IsCompl s.space.toSubmodule (fixedSpace ρ L))
    (hff : IsFFModule ρ) (hgen : offenderSubgroup s.action = L) (_hL : L = ⊤)
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))
    (hdim : Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 10)
    (hoff : ∀ A, IsBestOffender s.action A →
      IsEndNodeRadical ((A.subgroupOf L).map e.toMonoidHom)) :
    quadraticRatio s.space.toRepresentation.dual ≤ 2 := by
  let q := splitQuotientEquiv s hc
  have hffU : IsFFModule (G := G) (V := s.space.toSubmodule) s.space.toRepresentation := by
    obtain ⟨A, hA⟩ := hff
    exact ⟨A, hA.1, (fixedCodim_subrepresentation_le ρ s.space A).trans hA.2⟩
  have hffQ : IsFFModule s.action := hffU.map_equivariant _ _
    (actionSymm q).groupEquiv.toMonoidHom (actionSymm q).groupEquiv.injective
    (actionSymm q).linearEquiv (actionSymm q).intertwines
  obtain ⟨A, hA⟩ := hffQ
  obtain ⟨B, _, hB, hqB, _⟩ := hA.exists_quadratic_minimalBestOffender s.action
  have hBL : B ≤ L := hgen ▸ hB.1.le_offenderSubgroup s.action
  have hr := (hoff B hB.1).rank
  rw [rank_map_injective e.toMonoidHom e.injective, rank_subgroupOf hBL] at hr
  have hqQ : quadraticRatio s.action.dual ≤ 2 :=
    rank_four_dual_bound s.action hB.1.1 hqB hr hdim
  rwa [q.dual.quadraticRatio_eq] at hqQ

end CFSG.Quasithin.ChapterB.SourceB513
