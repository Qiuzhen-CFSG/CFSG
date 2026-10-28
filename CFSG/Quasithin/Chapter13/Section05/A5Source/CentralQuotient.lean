module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.MovedPlane

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
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section08
open ComponentReduction Section08.Source Recognition Recognition.Configuration
open Recognition.MarkedModule
universe u
variable {G : Type u} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ : Subgroup G} [IsElementaryAbelian 2 D.V]
  (d : Context D.T D.L D.V D.V₁ V₂ D.Vplus) (h : D.Hypothesis)
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
  (hH : D.H ∈ Hz D.L₁ (D.T : Subgroup G)
    (centralizer (D.V₁ : Set G)) (normalizer (D.L : Set G)))
  (h17 : ∀ J ∈ Hz D.L₁ (D.T : Subgroup G)
    (centralizer (D.V₁ : Set G)) (normalizer (D.L : Set G)),
    ¬ IsMulCommutative (UH J D.Vplus) → (D.L₁.subgroupOf J).Normal →
      ClassicalGroup.IsPSU G 4 2 ∨ ClassicalGroup.IsPSL G 4 3)
  (hnot : ¬ ModelConclusion G 5)
  [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]
include d h hA312 hH h17 hnot

/-- The literal natural central quotient and ambient generation from the
independently classified original selected component. -/
theorem source_central_quotient (hU : ¬IsMulCommutative D.UH)
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
  have hi := d.third_index
  have hSQ := (Chapter1.Section02.uniqueness_local_quotient_sqtk
    d.hypothesis.qtke hH.1.1).stronglyQuasithin
  obtain ⟨himage,hcore⟩ := source13_5_19 d hA312 hH h17 hnot
  have hm : ⁅starImage D.H K,starImage D.H D.L₁⁆ ≠ ⊥ := by
    rw [(selected_local_commutators s h d.hypothesis.qtke hH.1.1
      D.L₁ le_rfl himage hcore).2]
    intro he
    exact s.moved (by rw [he,commutator_bot_left])
  have hcomm := (selected_actor_normalization s h hi hU).2
  have hgroup := group_conclusions s h hSQ hi hU hLK d.third_eq_commutator hm hcomm
  have hcard := LocalGeometry.star_V_card_two h hi hU
  have hcyc : IsCyclic (starImage D.H D.V) := isCyclic_of_prime_card hcard
  obtain ⟨x,hx⟩ := (starImage D.H D.V).isCyclic_iff_exists_zpowers_eq_top.mp hcyc
  let v : Catalogue.actor D K := ⟨x,(show starImage D.H D.V ≤ Catalogue.actor D K from le_sup_right) (hx ▸ mem_zpowers x)⟩
  have hv : zpowers (v : Hstar D.H) = starImage D.H D.V := hx
  obtain ⟨p,hp⟩ := source_moved_plane d h hU K hLK v hv
  obtain ⟨hn,htilde,hgen,hnat,hfaith,hseed,hdim,_,_⟩ :=
    CentralQuotient.source_central_quotient D h K s d.hypothesis.qtke.properK
      hSQ hLK d.third_eq_commutator hm hcard (selected_section_even s) v hv p hp hcat
  exact ⟨hgroup.1,hgroup.2.2.2,hn,htilde,hgen,hnat,hfaith,hseed,hdim⟩
end CFSG.Quasithin.Chapter13.Section05.A5Source
