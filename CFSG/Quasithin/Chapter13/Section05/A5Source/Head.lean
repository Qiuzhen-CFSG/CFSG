module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.MovedPlane
public import Theory.Representation.BinaryOffender.MovedPlaneFaithfulHead
public import Theory.GroupTheory.SylowSubnormalIntersection

/-!
# Faithful chief heads and the original component Sylow marking

Local containment and relative normality give full component generation of
U_H/V₁. The original moved plane therefore makes every maximal quotient
faithful, without assuming a model. The original Sylow intersection also
retains pointwise centralization by the V* generator on the component Sylow.
Source: Aschbacher–Smith13.5.21, printed pp.923–924.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open ComponentReduction Section08.Source Recognition Recognition.Configuration
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ : Subgroup G} [IsElementaryAbelian 2 D.V]
  (d : Context D.T D.L D.V D.V₁ V₂ D.Vplus) (h : D.Hypothesis)
  [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]
include d h

/-- The source's maximal module quotients retain every original actor. -/
theorem source_head_faithful (hU : ¬ IsMulCommutative D.UH)
    (K : Subgroup G) (s : Selected D K) (hLK : D.L₁ ≤ K)
    (hnK : (K.subgroupOf D.H).Normal) [IsSimpleGroup (starImage D.H K)]
    (N : Subrepresentation (Catalogue.representation D K h)) (hN : IsCoatom N) :
    Function.Injective N.quotientRepresentation := by
  let : (starImage D.H K).Normal :=
    Subgroup.Normal.map hnK _ (QuotientGroup.mk'_surjective _)
  let : (Catalogue.component D K).Normal := by
    change ((starImage D.H K).subgroupOf (Catalogue.actor D K)).Normal
    infer_instance
  let e : Catalogue.component D K ≃* starImage D.H K := subgroupOfEquivOfLe le_sup_left
  let : IsSimpleGroup (Catalogue.component D K) := e.isSimpleGroup
  let : IsQuasisimple (starImage D.H K) := s.quasisimple
  let : IsQuasisimple (Catalogue.component D K) := IsQuasisimple.of_mulEquiv e.symm
  have hcard := LocalGeometry.star_V_card_two h d.third_index hU
  have hcyc : IsCyclic (starImage D.H D.V) := isCyclic_of_prime_card hcard
  obtain ⟨x,hx⟩ := (starImage D.H D.V).isCyclic_iff_exists_zpowers_eq_top.mp hcyc
  let v : Catalogue.actor D K := ⟨x, (show starImage D.H D.V ≤ Catalogue.actor D K from le_sup_right)
    (hx ▸ mem_zpowers x)⟩
  have hv : zpowers (v : Hstar D.H) = starImage D.H D.V := hx
  obtain ⟨p,_⟩ := source_moved_plane d h hU K hLK v hv
  have hg := MarkedModule.linear_generation D h s hLK hnK d.third_eq_commutator
  have hg' : subspaceCommutator (Catalogue.representation D K h) ⊤ (Catalogue.component D K) = ⊤ := by
    apply top_unique
    conv_lhs => rw [← hg]
    apply Submodule.span_le.mpr
    rintro _ ⟨k,hk,w,hw,rfl⟩
    exact Submodule.subset_span
      ⟨⟨k,(show starImage D.H K ≤ Catalogue.actor D K from le_sup_left) hk⟩,hk,w,hw,rfl⟩
  have hn : ¬ Catalogue.component D K ≤ (Catalogue.representation D K h).ker := by
    intro hz
    have hk : starImage D.H K = ⊥ := by
      apply bot_unique
      intro k hk
      have he := (Catalogue.representation_injective D K h)
        ((hz (show (⟨k,(show starImage D.H K ≤ Catalogue.actor D K from le_sup_left) hk⟩ : Catalogue.actor D K)
          ∈ Catalogue.component D K from hk)).trans (map_one _).symm)
      exact congrArg Subtype.val he
    exact s.moved (by rw [hk]; simp)
  exact p.coatom_quotient_faithful _ (Catalogue.component D K) (Catalogue.localActor D K) v
    (Catalogue.component_commutator D K h s hcard (selected_section_even s) v hv)
    hg' (Catalogue.representation_injective D K h) hn N hN

omit [IsElementaryAbelian 2 D.V]
  [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)] in
/-- A source generator with its intrinsic component Sylow marking. -/
theorem source_actor_marking (hU : ¬ IsMulCommutative D.UH)
    (K : Subgroup G) (s : Selected D K) :
    ∃ v : Catalogue.actor D K, zpowers (v : Hstar D.H) = starImage D.H D.V ∧
      orderOf v = 2 ∧ ∃ P : Sylow 2 (Catalogue.component D K),
        ∀ x ∈ P, (x : Catalogue.actor D K) * v = v * (x : Catalogue.actor D K) := by
  have hcard := LocalGeometry.star_V_card_two h d.third_index hU
  have hcyc : IsCyclic (starImage D.H D.V) := isCyclic_of_prime_card hcard
  obtain ⟨x,hx⟩ := (starImage D.H D.V).isCyclic_iff_exists_zpowers_eq_top.mp hcyc
  have hxV : x ∈ starImage D.H D.V := hx ▸ mem_zpowers x
  let v : Catalogue.actor D K := ⟨x,(show starImage D.H D.V ≤ Catalogue.actor D K from le_sup_right) hxV⟩
  let e : Catalogue.component D K ≃* starImage D.H K := subgroupOfEquivOfLe le_sup_left
  obtain ⟨P,hP⟩ := (starSylow D h).exists_subgroupOf_eq_of_subnormal
    (starImage D.H K) s.star_component.1
  let Q := P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  refine ⟨v,hx,?_,Q,?_⟩
  · have ho : orderOf (v : Hstar D.H) = 2 := by rw [←Nat.card_zpowers,hx,hcard]
    exact (orderOf_injective (Catalogue.actor D K).subtype Subtype.val_injective v).symm.trans ho
  · rintro z ⟨y,hy,rfl⟩
    apply Subtype.ext
    change (y : Hstar D.H) * x = x * (y : Hstar D.H)
    apply mem_centralizer_iff.mp (star_actor_centralizes_sylow D h hcard hxV)
    change y ∈ (P : Subgroup (starImage D.H K)) at hy
    rwa [hP] at hy

end CFSG.Quasithin.Chapter13.Section05.A5Source
