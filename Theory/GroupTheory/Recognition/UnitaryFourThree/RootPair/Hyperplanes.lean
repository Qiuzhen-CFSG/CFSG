module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.PlaneSource
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.CoreIncidence
public import Theory.GroupTheory.NormalizerAction
public import Theory.Representation.BinaryPolarity.ElementarySixteen

/-!
# The original core hyperplanes and six-letter normalizer action

Every nonidentity point x of a source plane has the canonical hyperplane
Ri∩O2(O2residual(C_G(x))). Its order is transported by actual normalizer
fusion. Core incidence is symmetric and self-incident, and naturality gives
equivariance. The binary polarity construction therefore yields an invariant
nondegenerate alternating form and an injective six-letter action of the
literal normalizer/centralizer quotient. No classification of transitive
order360 subgroups of GL4(2) is assumed.
Source: Aschbacher, Sporadic Groups (1994),45.6 and Exercise15.1, pp.244,249.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
variable {G:Type*} [Group G] [Finite G] {z:G}
namespace RootPair
variable (P:RootPair z)

theorem plane_inf_conjugate_core_card (h:IsType z) (V:Subgroup G)
    (hV:V≤P.T ∧ IsElementaryAbelian 2 V ∧ Nat.card V=16)
    (x:G) (hx:x∈V) (hxne:x≠1) : Nat.card (V⊓core x:Subgroup G)=8 := by
  have hzV : z∈V := P.E_le_plane h V hV P.z_mem_E
  have hz1:z≠1 := by intro he; have hh:=h.involution; simp [he] at hh
  obtain ⟨g,hg,hgx⟩ := P.plane_nonidentity_transitive h V hV z x hzV hx hz1 hxne
  have hmap : (V⊓core z).map (MulAut.conj g).toMonoidHom=V⊓core x := by
    have hgV : V.map (MulAut.conj g).toMonoidHom=V := mem_normalizer_iff_map_conj_eq.mp hg
    rw [map_inf _ _ _ (MulAut.conj g).injective,map_core,hgV]
    exact congrArg (fun w:G=>V⊓core w) hgx
  rw [←hmap,card_map_of_injective (MulAut.conj g).injective,P.plane_inf_core_card h V hV]

def planeHyperplane (V:Subgroup G) (x:V) : Subgroup V := (V⊓core (x:G)).subgroupOf V

theorem planeHyperplane_index (h:IsType z) (V:Subgroup G)
    (hV:V≤P.T ∧ IsElementaryAbelian 2 V ∧ Nat.card V=16)
    (x:V) (hx:x≠1) : (planeHyperplane V x).index=2 := by
  have hc : Nat.card (planeHyperplane V x)=8 := by
    unfold planeHyperplane
    rw [Nat.card_congr (subgroupOfEquivOfLe (show V⊓core (x:G)≤V from inf_le_left)).toEquiv]
    exact P.plane_inf_conjugate_core_card h V hV x x.property (fun he=>hx (Subtype.ext he))
  have hh:=(planeHyperplane V x).index_mul_card
  rw [hc,hV.2.2] at hh
  omega

def planeHyperplanes (h:IsType z) (V:Subgroup G)
    (hV:V≤P.T ∧ IsElementaryAbelian 2 V ∧ Nat.card V=16) :
    {x:V // x≠1} → {D:Subgroup V // D.index=2} :=
  fun x=>⟨planeHyperplane V x,P.planeHyperplane_index h V hV x x.property⟩

theorem planeHyperplanes_symmetric (h:IsType z) (V:Subgroup G)
    (hV:V≤P.T ∧ IsElementaryAbelian 2 V ∧ Nat.card V=16) (x y:{x:V // x≠1}) :
    x.val∈(P.planeHyperplanes h V hV y).val ↔ y.val∈(P.planeHyperplanes h V hV x).val := by
  change ((x.val:G)∈V ∧ (x.val:G)∈core (y.val:G)) ↔ ((y.val:G)∈V ∧ (y.val:G)∈core (x.val:G))
  rw [and_iff_right x.val.property,and_iff_right y.val.property]
  exact core_incidence_symmetric h _ _
    (P.plane_nonidentity_fused h V hV x.val x.val.property (fun he=>x.property (Subtype.ext he)))
    (P.plane_nonidentity_fused h V hV y.val y.val.property (fun he=>y.property (Subtype.ext he)))

theorem planeHyperplanes_self (h:IsType z) (V:Subgroup G)
    (hV:V≤P.T ∧ IsElementaryAbelian 2 V ∧ Nat.card V=16) (x:{x:V // x≠1}) :
    x.val∈(P.planeHyperplanes h V hV x).val :=
  ⟨x.val.property,mem_own_core_of_fused h x.val
    (P.plane_nonidentity_fused h V hV x.val x.val.property (fun he=>x.property (Subtype.ext he)))⟩

theorem planeHyperplane_map (V:Subgroup G) (a:normalizer (V:Set G)) (x:V) :
    planeHyperplane V (V.normalizerMonoidHom a x)=
      (planeHyperplane V x).map (V.normalizerMonoidHom a).toMonoidHom := by
  apply map_injective V.subtype_injective
  unfold planeHyperplane
  rw [map_subgroupOf_eq_of_le inf_le_left,map_map]
  have he : V.subtype.comp (V.normalizerMonoidHom a).toMonoidHom =
      (MulAut.conj (a:G)).toMonoidHom.comp V.subtype := rfl
  rw [he,←map_map,map_subgroupOf_eq_of_le inf_le_left,map_inf _ _ _ (MulAut.conj (a:G)).injective]
  have haV : V.map (MulAut.conj (a:G)).toMonoidHom=V := mem_normalizer_iff_map_conj_eq.mp a.property
  rw [haV,map_core]
  rfl


theorem planeHyperplanes_equivariant (h:IsType z) (V:Subgroup G)
    (hV:V≤P.T ∧ IsElementaryAbelian 2 V ∧ Nat.card V=16)
    (a:NormalizerAction.Star V) (x:{x:V // x≠1}) :
    (P.planeHyperplanes h V hV ⟨NormalizerAction.action V a x,
      fun he=>x.property ((NormalizerAction.action V a).map_eq_one_iff.mp he)⟩).val =
      (P.planeHyperplanes h V hV x).val.map (NormalizerAction.action V a).toMonoidHom := by
  refine Quotient.inductionOn a ?_
  intro g
  exact planeHyperplane_map V g x

theorem exists_invariant_plane_form (h:IsType z) (V:Subgroup G)
    (hV:V≤P.T ∧ IsElementaryAbelian 2 V ∧ Nat.card V=16)
    [IsElementaryAbelian 2 V] :
    ∃ B:LinearMap.BilinForm (ZMod 2) (Additive V), B.IsAlt ∧ B.Nondegenerate ∧
      (∀a x y,B (Additive.ofMul (NormalizerAction.action V a x.toMul))
        (Additive.ofMul (NormalizerAction.action V a y.toMul))=B x y) ∧
      ∀(x:{x:V // x≠1})(y:V),B (Additive.ofMul x) (Additive.ofMul y)=0 ↔
        (y:G)∈core (x.val:G) := by
  obtain ⟨B,hA,hN,hB,hker⟩:=BinaryPolarity.exists_invariant_form_of_elementary_hyperplanes
    (NormalizerAction.action V) (P.planeHyperplanes h V hV)
    (P.planeHyperplanes_symmetric h V hV) (P.planeHyperplanes_self h V hV)
    (P.planeHyperplanes_equivariant h V hV)
  refine ⟨B,hA,hN,hB,?_⟩
  intro x y
  have he:=hker x y
  change _ ↔ (y:G)∈V ∧ (y:G)∈core (x.val:G) at he
  simpa only [y.property,true_and] using he

theorem exists_injective_plane_six_action (h:IsType z) (V:Subgroup G)
    (hV:V≤P.T ∧ IsElementaryAbelian 2 V ∧ Nat.card V=16) :
    ∃φ:NormalizerAction.Star V →* Equiv.Perm (Fin 6),Function.Injective φ := by
  let := hV.2.1
  obtain ⟨B,hA,hN,hB,_⟩:=P.exists_invariant_plane_form h V hV
  let σ:=Representation.elementaryRepresentation (p:=2) (NormalizerAction.action V)
  have hσ : Function.Injective σ := by
    intro a b hab
    apply NormalizerAction.action_injective V
    apply MulEquiv.ext
    intro x
    exact congrArg Additive.toMul (congrArg (fun f=>f (Additive.ofMul x)) hab)
  have hd : Module.finrank (ZMod 2) (Additive V)=4 := by
    apply Nat.pow_right_injective (by decide : 2≤2)
    have hc:=Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=Additive V)
    rw [Nat.card_zmod] at hc
    exact hc.symm.trans hV.2.2
  exact BinaryPolarity.exists_injective_six_action_of_form σ hσ hd B hA hN hB

end RootPair
end Theory.GroupTheory.Recognition.UnitaryFourThree
