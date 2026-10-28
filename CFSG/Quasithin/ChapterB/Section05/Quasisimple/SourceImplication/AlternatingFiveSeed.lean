module
public import Theory.Representation.NormalElementaryFixedSeed
public import Theory.Representation.BinaryPermutation.CubicFixedSpace.Five
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Geometry

/-!
# The natural alternating-five moved section conflicts with a Sylow seed

A moved section is the literal quotient [V,C]/C_[V,C](C). Its quotient map
constructs a natural central section for the same embedded A₅; the ambient
quotient above [V,C] is fixed by construction. The natural A₅ fixed-space
enlargement theorem therefore contradicts a seed contained in V whose
centralizer is the prescribed Sylow subgroup. Both central extensions are
retained, and no splitting or change of ambient quotient is used.
Source: Aschbacher–Smith C.2.7(3) and the source application in 15.4.20.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q]
    (V Z : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* Q) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (V : Set G))

theorem not_alternatingFive_movedSection_of_seed
    (hZV : Z ≤ V) (P : Sylow 2 G) (hCZ : centralizer (Z : Set G) = (P : Subgroup G))
    (J C : Subgroup Q)
    (s : MovedSection ((NormalElementaryQuotient.representation V q hq hk).comp J.subtype)
      (C.subgroupOf J))
    (e : ActionEquiv (s.action.comp (C.subgroupOf J).subtype) (alternatingNatural 5)) : False := by
  let ρ := NormalElementaryQuotient.representation V q hq hk
  let fJ : alternatingGroup (Fin 5) →* J :=
    (C.subgroupOf J).subtype.comp e.groupEquiv.symm.toMonoidHom
  let f : alternatingGroup (Fin 5) →* Q := J.subtype.comp fJ
  have hf : Function.Injective f :=
    J.subtype_injective.comp ((C.subgroupOf J).subtype_injective.comp e.groupEquiv.symm.injective)
  let W : Subrepresentation (ρ.comp f) :=
    ⟨s.space.toSubmodule,fun g v hv => s.space.apply_mem_toSubmodule (fJ g) hv⟩
  let b : W.toSubmodule →ₗ[ZMod 2] s.space.toSubmodule := LinearMap.id
  let π : W.toSubmodule →ₗ[ZMod 2] BinaryPermutation.natural (Fin 5) :=
    e.linearEquiv.toLinearMap.comp (s.central.toSubmodule.mkQ.comp b)
  have hact (g : alternatingGroup (Fin 5)) (w : W.toSubmodule) :
      b (W.toRepresentation g w) = s.space.toRepresentation (fJ g) (b w) := by
    apply Subtype.ext
    rfl
  have hequiv : ∀ g w, π (W.toRepresentation g w) =
      BinaryPermutation.naturalRepresentation (Fin 5) g.val (π w) := by
    intro g w
    change e.linearEquiv (s.central.toSubmodule.mkQ (b (W.toRepresentation g w))) = _
    rw [hact]
    have hh := e.intertwines (e.groupEquiv.symm g) (s.central.toSubmodule.mkQ (b w))
    simpa only [π, MovedSection.action, alternatingNatural, fJ,
      MonoidHom.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      Subrepresentation.quotientRepresentation_mk, Subgroup.subtype_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] using hh
  have hcentral : ∀ g w, π w = 0 → W.toRepresentation g w = w := by
    intro g w hw
    have hz : s.central.toSubmodule.mkQ (b w) = 0 :=
      e.linearEquiv.injective (by simpa only [π, LinearMap.comp_apply, LinearEquiv.coe_coe, map_zero] using hw)
    have hm : b w ∈ s.central.toSubmodule := (Submodule.Quotient.mk_eq_zero _).mp hz
    rw [s.central_eq] at hm
    exact hm (e.groupEquiv.symm g)
  have hquot : ∀ g v, ρ (f g) v - v ∈ W := by
    intro g v
    change ρ (f g) v - v ∈ s.space.toSubmodule
    rw [s.space_eq]
    exact Submodule.subset_span ⟨fJ g,(e.groupEquiv.symm g).property,v,Submodule.mem_top,rfl⟩
  let S := P.mapSurjective hq
  obtain ⟨g,hg,_,hfix⟩ := BinaryPermutation.CubicFixedSpace.Five.centralSection_enlargement
    ρ f hf W π hequiv hcentral hquot S
  exact NormalElementaryQuotient.no_fixedSpace_enlargement_of_seed
    V Z q hq hk hZV (P : Subgroup G) hCZ g hg hfix

/-- The actual marked symmetric-five B.5 row has the same obstruction. -/
theorem not_markedFive_movedSection_of_seed
    (hZV : Z ≤ V) (P : Sylow 2 G) (hCZ : centralizer (Z : Set G) = (P : Subgroup G))
    (J C : Subgroup Q)
    (s : MovedSection ((NormalElementaryQuotient.representation V q hq hk).comp J.subtype)
      (C.subgroupOf J))
    (A : Subgroup J)
    (e : MarkedActionEquiv s.action A (C.subgroupOf J)
      (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5))) : False := by
  apply not_alternatingFive_movedSection_of_seed V Z q hq hk hZV P hCZ J C s
  refine ⟨e.subgroupEquiv,e.action.linearEquiv,?_⟩
  intro g v
  have he := e.action.intertwines ⟨g,e.contained g.property⟩ v
  rw [e.compatible] at he
  exact he

end CFSG.Quasithin.ChapterB.QuasisimpleSource
