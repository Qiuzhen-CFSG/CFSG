module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairResidual
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.AlternatingFiveSeed
/-!
# Five-letter source sections cannot have a Sylow seed centralizer

For a literal centralizer quotient, a natural alternating-five central
section supplies a nontrivial cubic element fixing the Sylow fixed space.
It must lift into the seed centralizer, contradicting that this is the
Sylow subgroup. For a marked pair, the inverse image of the first
coordinate is the needed central section; its central kernel is retained.

Source: Aschbacher--Smith 10.2.3(4), printed p.745, using B.5.1 and E.2.3.
-/
public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB
open QuasisimpleSource SourceInduction
variable {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q]
    (V Z : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* Q) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (V : Set G))
theorem not_five_movedSection_of_seed
    (hZV : Z ≤ V) (P : Sylow 2 G) (hCZ : centralizer (Z : Set G) = (P : Subgroup G))
    (J : Subgroup Q) (A : Subgroup J)
    (s : MovedSection ((NormalElementaryQuotient.representation V q hq hk).comp J.subtype)
      A)
    (e : ActionEquiv (s.action.comp A.subtype) (alternatingNatural 5)) : False := by
  let ρ := NormalElementaryQuotient.representation V q hq hk
  let fJ : alternatingGroup (Fin 5) →* J :=
    A.subtype.comp e.groupEquiv.symm.toMonoidHom
  let f : alternatingGroup (Fin 5) →* Q := J.subtype.comp fJ
  have hf : Function.Injective f :=
    J.subtype_injective.comp (A.subtype_injective.comp e.groupEquiv.symm.injective)
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


/-- Apply the seed obstruction to the source's marked alternating-five row. -/
theorem not_marked_five_movedSection_of_seed
    (hZV : Z ≤ V) (P : Sylow 2 G) (hCZ : centralizer (Z : Set G) = (P : Subgroup G))
    (J : Subgroup Q) (A : Subgroup J)
    (s : MovedSection ((NormalElementaryQuotient.representation V q hq hk).comp J.subtype) A)
    (a : MarkedActionEquiv s.action (offenderSubgroup s.action) A
      (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5))) : False := by
  apply not_five_movedSection_of_seed V Z q hq hk hZV P hCZ J A s
  refine ⟨a.subgroupEquiv,a.action.linearEquiv,?_⟩
  intro g v
  have he := a.action.intertwines ⟨g,a.contained g.property⟩ v
  rw [a.compatible] at he
  exact he


set_option backward.isDefEq.respectTransparency false in
theorem not_pairedFive_of_seed
    (hZV : Z ≤ V) (P : Sylow 2 G) (hCZ : centralizer (Z : Set G) = (P : Subgroup G))
    (J : Subgroup Q)
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation V q hq hk).comp J.subtype))
    (c : d.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5))) : False := by
  let ρ := NormalElementaryQuotient.representation V q hq hk
  let A := alternatingGroup (Fin 5)
  let E := Equiv.Perm (Fin 5)
  let fJ : A →* J := c.action.groupEquiv.symm.toMonoidHom.comp
    ((MonoidHom.inl E E).comp A.subtype)
  let f : A →* Q := J.subtype.comp fJ
  have hf : Function.Injective f := by
    intro a b hab
    apply A.subtype_injective
    exact congrArg Prod.fst (c.action.groupEquiv.symm.injective
      (J.subtype_injective hab))
  have hact (a : A) (v : Additive V) :
      c.quotientMap (ρ (f a) v) =
        (BinaryPermutation.naturalRepresentation (Fin 5) a.val (c.quotientMap v).1,
          (c.quotientMap v).2) := by
    have hh := c.quotientMap_action (fJ a) v
    rw [show c.action.groupEquiv (fJ a) = (a.val,1) from
      c.action.groupEquiv.apply_symm_apply _] at hh
    change c.quotientMap (ρ (f a) v) =
      (BinaryPermutation.naturalRepresentation (Fin 5) a.val (c.quotientMap v).1,
       BinaryPermutation.naturalRepresentation (Fin 5) 1 (c.quotientMap v).2) at hh
    simpa only [map_one,Module.End.one_apply] using hh
  let W : Subrepresentation (ρ.comp f) :=
    ⟨(LinearMap.snd (ZMod 2) _ _ |>.comp c.quotientMap).ker,by
      intro a v hv
      change (c.quotientMap (ρ (f a) v)).2 = 0
      rw [hact]
      exact hv⟩
  let π : W.toSubmodule →ₗ[ZMod 2] BinaryPermutation.natural (Fin 5) :=
    (LinearMap.fst (ZMod 2) _ _).comp (c.quotientMap.comp W.toSubmodule.subtype)
  have hequiv (a : A) (v : W.toSubmodule) :
      π (W.toRepresentation a v) =
        BinaryPermutation.naturalRepresentation (Fin 5) a.val (π v) := by
    exact congrArg Prod.fst (hact a v)
  have hcentral (a : A) (v : W.toSubmodule) (hv : π v = 0) :
      W.toRepresentation a v = v := by
    apply Subtype.ext
    have hz : c.quotientMap v.val = 0 := Prod.ext hv v.property
    have hm : v.val ∈ Representation.invariants (ρ.comp J.subtype) := by
      rw [← c.quotientMap_ker]
      exact hz
    exact hm (fJ a)
  have hquot (a : A) (v : Additive V) : ρ (f a) v - v ∈ W := by
    change (c.quotientMap (ρ (f a) v-v)).2 = 0
    rw [map_sub,hact]
    exact sub_self _
  obtain ⟨g,hg,_,hfix⟩ := BinaryPermutation.CubicFixedSpace.Five.centralSection_enlargement
    ρ f hf W π hequiv hcentral hquot (P.mapSurjective hq)
  exact NormalElementaryQuotient.no_fixedSpace_enlargement_of_seed
    V Z q hq hk hZV (P : Subgroup G) hCZ g hg hfix
end CFSG.Quasithin.ChapterB
