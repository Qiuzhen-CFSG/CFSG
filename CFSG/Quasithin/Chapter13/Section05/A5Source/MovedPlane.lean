module
public import Theory.Representation.CyclicFixedRank
public import CFSG.Quasithin.Chapter13.Section05.A5Source.ComponentConfiguration
public import Theory.Representation.BinaryFullPlane
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.CentralQuotient

/-!
# The actual moved plane in the original A₅ branch

The original seed has rank two and is its full L₁-commutator. Every proper
nonzero invariant subspace would leave a trivial binary line quotient,
contradicting this movement. F.9 identifies the seed with displacement of
the actual V* generator, and L₁ centralizes that generator.
Source: Aschbacher--Smith13.5.21(iii), printed pp.923–924.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open ComponentReduction Section08.Source Recognition Recognition.Configuration
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ : Subgroup G} [IsElementaryAbelian 2 D.V]
  (d : Context D.T D.L D.V D.V₁ V₂ D.Vplus) (h : D.Hypothesis)
  [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]
include d h

/-- The fully moved binary seed supplies the actual irreducible plane once
the independently classified local actor lies in K. -/
theorem source_moved_plane (hU : ¬IsMulCommutative D.UH)
    (K : Subgroup G) (hLK : D.L₁ ≤ K)
    (v : Catalogue.actor D K)
    (hv : zpowers (v : Hstar D.H) = starImage D.H D.V) :
    ∃ p : MovedPlane (Catalogue.representation D K h) (Catalogue.localActor D K) v,
      p.plane.toSubmodule = Action.seedSpace D := by
  let ρ := Action.starRepresentation D h
  let τ := (Catalogue.representation D K h).comp (Catalogue.localActor D K).subtype
  have hs : ∀ l : Catalogue.localActor D K, ∀ w ∈ Action.seedSpace D, τ l w ∈ Action.seedSpace D := by
    intro l w hw
    obtain ⟨x,hx,he⟩ := l.property
    obtain ⟨u,hu,rfl⟩ := hw
    change ρ (l.val : Hstar D.H) (Additive.ofMul (QuotientGroup.mk' _ u)) ∈ Action.seedSpace D
    change QuotientGroup.mk' (pCore 2 D.H) x = (l.val : Hstar D.H) at he
    rw [←he]
    rw [Action.starRepresentation_apply]
    refine ⟨⟨x.val*u.val*x.val⁻¹,le_normalizer_iff.mp (le_normalizer_conjugateSpanBy _ _)
      x.val x.property u.val u.property⟩,?_,rfl⟩
    exact le_normalizer_iff.mp h.local_normalizes x.val (mem_sup_left hx) u.val hu
  let P : Subrepresentation τ := ⟨Action.seedSpace D,hs⟩
  have hl : D.Vplus=⁅D.Vplus,D.L₁⁆ := by
    have hs : D.Vplus = ⁅D.V,D.L₁⁆ := d.third_eq_commutator
    conv_rhs => rw [hs]
    rw [commutator_isPPerfect_idempotent D.L₁ D.V
      (isPPerfect_embedded_pResidual 2 _) (IsElementaryAbelian.isPGroup 2 D.V)
      ((map_subtype_le _).trans (inf_le_left.trans d.chosen.normalizes))]
    exact d.third_eq_commutator
  have hm := source_module_conditions h d.third_index hU d.module_card hl
  have hdim : Module.finrank (ZMod 2) P.toSubmodule = 2 := hm.2.2
  have hlocal : (Catalogue.localActor D K).map (Catalogue.actor D K).subtype=
      starImage D.H D.L₁ := map_subgroupOf_eq_of_le
        ((map_mono (comap_mono hLK)).trans le_sup_left)
  have hfull : subspaceCommutator τ P.toSubmodule ⊤=P.toSubmodule := by
    change subspaceCommutator
      (((Action.starRepresentation D h).comp (Catalogue.actor D K).subtype).comp
        (Catalogue.localActor D K).subtype) (Action.seedSpace D) ⊤=Action.seedSpace D
    rw [BinaryParabolicNatural.commutator_comp,←MonoidHom.range_eq_map,
      Subgroup.range_subtype,BinaryParabolicNatural.commutator_comp,hlocal]
    exact hm.2.1
  have hp : IsIrreducible P.toRepresentation := by
    apply irreducible_of_rank_two_full_movement _ hdim
    apply Submodule.map_injective_of_injective P.toSubmodule.injective_subtype
    rw [BinaryGroupAction.subrepresentation_moved_map,Submodule.map_top,
      Submodule.range_subtype,hfull]
  have hPV : starImage D.H D.V = zpowers (v : Hstar D.H) := hv.symm
  have hmove : P.toSubmodule = LinearMap.range (Catalogue.representation D K h v - 1) := by
    change Action.seedSpace D = LinearMap.range (ρ (v : Hstar D.H) - 1)
    rw [←hm.1,←hv]
    exact Representation.CyclicFixedRank.commutator_eq_range ρ (v : Hstar D.H)
  have hcentral := Fitting.star_centralizes_V D h d.third_index
    hU D.L₁ (((map_subtype_le _).trans inf_le_left).trans d.chosen.normalizes)
  refine ⟨⟨P,hmove,hdim,hp,?_⟩,rfl⟩
  intro l
  change l.val*v=v*l.val
  apply Subtype.ext
  exact (hcentral l.property (v : Hstar D.H) (hv ▸ mem_zpowers _)).symm
end CFSG.Quasithin.Chapter13.Section05.A5Source
