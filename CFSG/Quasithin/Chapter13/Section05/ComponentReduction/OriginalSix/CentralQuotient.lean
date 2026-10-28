module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.MovedPlane

/-!
# The original central quotient after the chief catalogue

The natural source flag supplies the exact marked moved plane and the
commutator seed identity. Original13.5.19 makes the local residual act
nontrivially on the selected component. Once the chief catalogue supplies
its natural rows, centerlessness and L₁-containment, the existing marked
quotient argument proves relative normality, ambient core generation and
the faithful natural central quotient. These are the actual inputs of the
three parabolic consumers, with all original quotient maps retained.
Source: Aschbacher–Smith13.5.21(3),(5),(6), printed p.924.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix
open Section08.SourceCompletion Section08.Source Recognition Recognition.Configuration
open Recognition.MarkedModule
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz) (h : D.Hypothesis)
  (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
  [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]
include d h e

/-- The literal natural central quotient and ambient generation from the
independently classified original selected component. -/
theorem source_central_quotient (hU : ¬IsMulCommutative D.UH)
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T D.L)
    (hc : centralizer (D.Vplus : Set G) ≤ M ⊓ normalizer (D.V : Set G))
    (K : Subgroup G) (s : Selected D K) (hLK : D.L₁ ≤ K)
    [IsSimpleGroup (starImage D.H K)]
    (hcat : CentralQuotient.ChiefCatalogue D h K) :
    (K.subgroupOf D.H).Normal ∧ D.UH = ⁅D.QH,K⁆ ∧
    ∃ hn : (starImage D.H K).Normal,
      D.tilde D.UH = ⁅D.tilde D.UH,D.tilde K⁆ ∧
      subspaceCommutator (Action.starRepresentation D h) ⊤ (starImage D.H K) = ⊤ ∧
      CentralQuotient.NaturalAction (Catalogue.component D K)
        ((CentralQuotient.representation D h K hn).comp (Catalogue.actor D K).subtype) ∧
      Function.Injective (CentralQuotient.representation D h K hn) ∧
      Function.Injective (CentralQuotient.seedMap D h K) ∧
      Module.finrank (ZMod 2) (CentralQuotient.seedSpace D h K) = 2 := by
  have hi := NormalBranch.SourceOrthogonal.seed_index d
  have hSQ := (Chapter1.Section02.uniqueness_local_quotient_sqtk
    d.counterexample.qtke (selected_H_mem h)).stronglyQuasithin
  obtain ⟨himage,hcore⟩ := normalizer_conclusions d h e h1221 hc
  have hm : ⁅starImage D.H K,starImage D.H D.L₁⁆ ≠ ⊥ := by
    rw [(selected_local_commutators s h d.counterexample.qtke (selected_H_mem h)
      D.L₁ le_rfl himage hcore).2]
    intro he
    exact s.moved (by rw [he,commutator_bot_left])
  have hcomm := (selected_actor_normalization s h hi hU).2
  have hgroup := group_conclusions s h hSQ hi hU hLK (seed_identity d h) hm hcomm
  have hcard := LocalGeometry.star_V_card_two h hi hU
  have hcyc : IsCyclic (starImage D.H D.V) := isCyclic_of_prime_card hcard
  obtain ⟨x,hx⟩ := (starImage D.H D.V).isCyclic_iff_exists_zpowers_eq_top.mp hcyc
  let v : Catalogue.actor D K := ⟨x,(show starImage D.H D.V ≤ Catalogue.actor D K from le_sup_right) (hx ▸ mem_zpowers x)⟩
  have hv : zpowers (v : Hstar D.H) = starImage D.H D.V := hx
  obtain ⟨p,hp⟩ := source_moved_plane d h hU K hLK v hv
  obtain ⟨hn,htilde,hgen,hnat,hfaith,hseed,hdim,_,_⟩ :=
    CentralQuotient.source_central_quotient D h K s d.counterexample.qtke.properK
      hSQ hLK (seed_identity d h) hm hcard (selected_section_even s) v hv p hp hcat
  exact ⟨hgroup.1,hgroup.2.2.2,hn,htilde,hgen,hnat,hfaith,hseed,hdim⟩
end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix
