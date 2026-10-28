module
public import Theory.Representation.CyclicFixedRank
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.Configuration
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.CentralQuotient

/-!
# The original marked displacement plane

The seed in U_H/V₁ is invariant under the literal L₁ image. Its nonzero
vectors form the original natural point-residual orbit, so it is irreducible.
F.9 identifies it with the displacement of the marked V* generator, while
the star-centrality of L₁ gives the commuting actor. This is the exact
MovedPlane used on the catalogue's chief sections and the central quotient.
Source: Aschbacher–Smith13.5.21(iii), pp.923–924.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix
open Section08.SourceCompletion Section08.Source Recognition Recognition.Configuration
open Section08.TransvectionRecognition
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionParabolic.Marking
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz) (h : D.Hypothesis)
  [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]
include d h

/-- The concrete natural point-residual orbit supplies the actual irreducible
moved plane once the independently classified local actor lies in K. -/
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
  have hm := source_module_conditions h (NormalBranch.SourceOrthogonal.seed_index d) hU
    (NormalBranch.ReturningPlane.module_card d)
    (by rw [residual_eq_sourceOne d h];exact (Section07.ModelExclusions.seed_commutator_point_residual d).symm)
  have hdim : Module.finrank (ZMod 2) P.toSubmodule = 2 := hm.2.2
  have hp : IsIrreducible P.toRepresentation := by
    have hn : Nontrivial P.toSubmodule := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank (ZMod 2) P.toSubmodule)
    let := hn
    rw [Representation.IsIrreducible,isSimpleOrder_iff]
    refine ⟨inferInstance,fun W => ?_⟩
    by_cases hW : W=⊥
    · exact Or.inl hW
    right
    apply top_unique
    intro w _
    by_cases hw0 : w=0
    · rw [hw0];exact W.toSubmodule.zero_mem
    obtain ⟨u,hu,hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (show W.toSubmodule≠⊥ from fun he => hW (Subrepresentation.toSubmodule_injective he))
    let : (D.V₁.subgroupOf (Section08.Source.UH D.H D.Vplus)).Normal := inferInstanceAs ((D.V₁.subgroupOf D.UH).Normal)
    let : IsElementaryAbelian 2 (Section08.Source.Utilde D.H D.Vplus D.V₁) := inferInstanceAs (IsElementaryAbelian 2 (Action.ModuleGroup D))
    have hLH : sourceOne D.L D.T D.V₁ ≤ D.H :=
      (residual_eq_sourceOne d h).symm ▸ (le_sup_left.trans h.local_le)
    have hρ : IsConjugation D.H D.Vplus D.V₁ ρ := Action.starRepresentation_apply D h
    obtain ⟨l,hl⟩ := Section07.ModelExclusions.seed_section_nonzero_orbit d hLH ρ hρ
      u.val u.property (fun he => hu0 (Subtype.ext he))
      w.val w.property (fun he => hw0 (Subtype.ext he))
    let a : Catalogue.localActor D K := Catalogue.localActorEquiv D K hLK
      ⟨QuotientGroup.mk' (pCore 2 D.H) (inclusion hLH l),
        mem_map_of_mem _ ((residual_eq_sourceOne d h).symm ▸ l.property)⟩
    have hh := W.apply_mem_toSubmodule a hu
    have he : P.toRepresentation a u=w := Subtype.ext hl
    exact he ▸ hh
  have hPV : starImage D.H D.V = zpowers (v : Hstar D.H) := hv.symm
  have hmove : P.toSubmodule = LinearMap.range (Catalogue.representation D K h v - 1) := by
    change Action.seedSpace D = LinearMap.range (ρ (v : Hstar D.H) - 1)
    rw [←hm.1,←hv]
    exact Representation.CyclicFixedRank.commutator_eq_range ρ (v : Hstar D.H)
  have hcentral := Fitting.star_centralizes_V D h (NormalBranch.SourceOrthogonal.seed_index d)
    hU D.L₁ ((((map_subtype_le _).trans inf_le_left).trans le_sup_left).trans d.normalizes_V)
  refine ⟨⟨P,hmove,hdim,hp,?_⟩,rfl⟩
  intro l
  change l.val*v=v*l.val
  apply Subtype.ext
  exact (hcentral l.property (v : Hstar D.H) (hv ▸ mem_zpowers _)).symm
end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix
