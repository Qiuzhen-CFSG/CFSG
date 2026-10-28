module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedRestriction
public import Theory.Representation.NormalElementaryEmbedding

/-!
# Comparing moved sections on two normal elementary subgroups

If two normal elementary subgroups have the same conjugation kernel, their
literal inclusion is a faithful equivariant embedding. For a perfect
component with irreducible moved central quotient, its moved spaces agree.
The resulting action equivalence also compares sections taken in different
ambient overgroups of that same component. This preserves the original
quotient map and the component marking when the offender subgroup changes.
Source: Aschbacher–Smith C.2.7(3)(a), pp.146–147.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {G H : Type*} [Group G] [Group H]
  (U V : Subgroup G) [U.Normal] [V.Normal]
  [IsElementaryAbelian 2 U] [IsElementaryAbelian 2 V]
  (hUV : U ≤ V) (q : G →* H) (hq : Function.Surjective q)
  (hU : q.ker = centralizer (U : Set G))
  (hV : q.ker = centralizer (V : Set G))

noncomputable def normalElementary_moved_comparison
    (C J₁ J₂ : Subgroup H) [Group.IsPerfect C] (hne : C ≠ ⊥)
    (hC₁ : C ≤ J₁) (hC₂ : C ≤ J₂)
    (s : MovedSection ((NormalElementaryQuotient.representation V q hq hV).comp J₁.subtype)
      (C.subgroupOf J₁))
    (t : MovedSection ((NormalElementaryQuotient.representation U q hq hU).comp J₂.subtype)
      (C.subgroupOf J₂))
    (hi : IsIrrPlus (NormalElementaryQuotient.representation V q hq hV) C
      (moved (NormalElementaryQuotient.representation V q hq hV) C)) :
    ActionEquiv (t.action.comp (C.subgroupOf J₂).subtype)
      (s.action.comp (C.subgroupOf J₁).subtype) := by
  let ρ := NormalElementaryQuotient.representation V q hq hV
  let σ := NormalElementaryQuotient.representation U q hq hU
  let e := NormalElementaryQuotient.inclusionLinear U V hUV
  have he : Function.Injective e := NormalElementaryQuotient.inclusionLinear_injective U V hUV
  have hact : ∀ g w, e (σ g w) = ρ g (e w) :=
    NormalElementaryQuotient.inclusionLinear_intertwines U V hUV q hq hU hV
  have hn : ¬ LinearMap.range e ≤ fixedSpace ρ C :=
    range_not_fixed_of_faithful_embedding ρ σ e he hact
      (NormalElementaryQuotient.representation_injective U q hq hU) C hne
  have hs : C ≤ subspaceStabilizer ρ (LinearMap.range e) := by
    apply le_subspaceStabilizer
    rintro c hc _ ⟨w,rfl⟩
    exact ⟨σ c w,hact c w⟩
  have heq := moved_eq_of_noncentral_invariant ρ C hi (LinearMap.range e) hs hn
  have hm : (moved σ C).map e = moved ρ C := by
    have hh := subspaceCommutator_map_embedding ρ σ (MonoidHom.id H) e
      (fun g w => (hact g w).symm) C ⊤
    have hh' : subspaceCommutator ρ (LinearMap.range e) C = (moved σ C).map e := by
      simpa only [Submodule.map_top,Subgroup.map_id] using hh
    exact hh'.symm.trans heq
  let φ : (C.subgroupOf J₂) ≃* (C.subgroupOf J₁) :=
    (subgroupOfEquivOfLe hC₂).trans (subgroupOfEquivOfLe hC₁).symm
  apply s.componentEmbeddingEquiv t φ e he
  · intro c w
    exact hact c.val.val w
  · rw [moved_comp_map,moved_comp_map,map_subgroupOf_eq_of_le hC₂,
      map_subgroupOf_eq_of_le hC₁]
    exact hm

end CFSG.Quasithin.ChapterB.QuasisimpleSource
