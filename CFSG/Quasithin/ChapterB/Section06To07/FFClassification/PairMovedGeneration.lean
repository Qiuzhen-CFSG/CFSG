module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairResidual
public import Theory.Representation.ResidualMovedGeneration
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates
/-!
# Residual generation in the original two-factor source module

When both specified source summands are the actual moved spaces, their
images generate the central quotient. Full displacement on that quotient
survives restriction to the two-residual by dual modular fixed-vector
theory. Lifting the quotient gives generation by the residual moved space
and the original fixed space, without assuming a direct decomposition.
The final consumer identifies the offender residual with the ambient one.
Source: Aschbacher–Smith B.5.6(3), B.6.9(2),(4) and E.2.3(2).
-/
public section
open Subgroup Representation Representation.BinaryOffender
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterB.SourceInduction
open QuasisimpleSource
variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) D V}

theorem SourceTwoFactorCase.residual_moved_sup_fixed (d : SourceTwoFactorCase ρ)
    (h₁ : d.firstSpace.toSubmodule = moved ρ d.first)
    (h₂ : d.secondSpace.toSubmodule = moved ρ d.second) :
    subspaceCommutator ρ ⊤ (pResidual 2 D) ⊔ ρ.invariants = ⊤ := by
  let τ := (fixed ρ).quotientRepresentation
  have hm (A : Subgroup D) : (moved ρ A).map (fixed ρ).toSubmodule.mkQ =
      subspaceCommutator τ ⊤ A := by
    have hh := subspaceCommutator_map_embedding τ ρ (MonoidHom.id D)
      (fixed ρ).toSubmodule.mkQ (fun _ _ => rfl) A ⊤
    rw [Submodule.map_top, LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _),
      Subgroup.map_id] at hh
    exact hh.symm
  have hfull : subspaceCommutator τ ⊤ ⊤ = ⊤ := by
    apply top_unique
    apply d.decomposition.sup_eq_top.ge.trans
    apply sup_le
    · change d.firstSpace.toSubmodule.map (fixed ρ).toSubmodule.mkQ ≤ _
      rw [h₁,hm]
      apply Submodule.span_le.mpr
      rintro _ ⟨g,hg,v,hv,rfl⟩
      exact Submodule.subset_span ⟨g,mem_top _,v,hv,rfl⟩
    · change d.secondSpace.toSubmodule.map (fixed ρ).toSubmodule.mkQ ≤ _
      rw [h₂,hm]
      apply Submodule.span_le.mpr
      rintro _ ⟨g,hg,v,hv,rfl⟩
      exact Submodule.subset_span ⟨g,mem_top _,v,hv,rfl⟩
  have hr := commutator_pResidual_eq_top τ ⊤ hfull
  have htop : (pResidual 2 (⊤ : Subgroup D)).map (⊤ : Subgroup D).subtype =
      pResidual 2 D := by
    exact map_pResidual_of_surjective 2 (⊤ : Subgroup D).subtype
      (fun g => ⟨⟨g,mem_top _⟩,rfl⟩)
  rw [htop,← hm] at hr
  have hc := congrArg (Submodule.comap (fixed ρ).toSubmodule.mkQ) hr
  rw [Submodule.comap_map_mkQ,Submodule.comap_top] at hc
  exact (sup_comm _ _).trans hc
end CFSG.Quasithin.ChapterB.SourceInduction

namespace CFSG.Quasithin.ChapterB
open QuasisimpleSource SourceInduction
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

theorem source_offender_pair_moved_sup_fixed
    (ρ : Representation (ZMod 2) G V) (T : Sylow 2 G)
    (hP : IsMinimalParabolicOver T ⊤) (hff : IsFFModule ρ)
    (hcore : pCore 2 G = ⊥) (d : SourceTwoFactorCase (ρ.comp (offenderSubgroup ρ).subtype)) :
    subspaceCommutator ρ ⊤ (pResidual 2 G) ⊔ fixedSpace ρ (offenderSubgroup ρ) = ⊤ := by
  obtain ⟨h₁,h₂⟩ := source_offender_two_factor_rank_one ρ T hP hff hcore d
  have hs := d.residual_moved_sup_fixed h₁.1 h₂.1
  have hh := subspaceCommutator_map_embedding (ρ.comp (offenderSubgroup ρ).subtype)
    ρ (offenderSubgroup ρ).subtype (LinearMap.id : V →ₗ[ZMod 2] V)
    (fun _ _ => rfl) (pResidual 2 (offenderSubgroup ρ)) ⊤
  simp only [Submodule.map_id,offender_residual_eq T hP ρ hff hcore] at hh
  rw [hh] at hs
  exact hs
end CFSG.Quasithin.ChapterB
