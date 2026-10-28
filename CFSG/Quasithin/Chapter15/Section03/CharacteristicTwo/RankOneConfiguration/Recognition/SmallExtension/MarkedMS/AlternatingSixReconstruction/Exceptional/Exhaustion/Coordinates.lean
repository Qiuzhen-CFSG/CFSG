module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.Parabolics
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.Graph

/-!
# Literal hexacode coordinates at every exceptional vertex

When the initial action kernel is Q, the existing covered-six normalizer
recognizes the action on the entire initial moved subgroup [X,K]. The
moved-space equivalence transports these coordinates back to that literal
subgroup. Conjugation on the free-amalgam graph then gives the corresponding
section inside each vertex's X, with projection kernel exactly its Q.

This constructs the model used in the distance-two commutator estimate;
it does not assume that the initial moved subgroup is the whole core.
Source: MS93 (3.2), pp.863--864; Aschbacher--Smith K.1.3, p.453.
The underlying hexacode model retains its imported ATLAS attribution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.CoveredSixModels
open Atlas.Codes
open CFSG.Quasithin.ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
local notation "M" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf (L ⊔ R)
local notation "X" => centralOmega L R

abbrev initialMoved (L R : Subgroup G) : Subgroup (L ⊔ R : Subgroup G) :=
  ⁅centralOmega L R,L.subgroupOf (L ⊔ R)⁆

instance initialMoved_elementary : IsElementaryAbelian 2 (initialMoved L R) :=
  IsElementaryAbelian.of_le (commutator_le_left X K)

theorem initialMoved_normal (h : SmallMSPair KnownSimple.IsKnownSimple L R) :
    (initialMoved L R).Normal := by
  let := h.relative_normal
  infer_instance

theorem initial_moved_hexacode_model
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (hc : layerKernel L R = pCore 2 M) :
    letI := initialMoved_normal h
    ∃ (f : M →* HexAutomorphisms)
      (φ : Additive (initialMoved L R) ≃ₗ[ZMod 2] hexacode),
      f.ker = pCore 2 M ∧
      ∀ (g : M) (v : initialMoved L R),
        φ (Additive.ofMul (MulAut.conjNormal g v)) =
          Hexacode.action (f g) (φ (Additive.ofMul v)) := by
  let := h.relative_normal
  let := initialMoved_normal h
  let := layerComponent_normal h
  let := layerComponent_quasisimple h e hz
  let q := QuotientGroup.mk' (layerKernel L R)
  obtain ⟨a⟩ := layerComponent_equiv_hexEven h e hz hc
  obtain ⟨m⟩ := nonempty_actionData (layerAction L R) (layerComponent L R) a
    (layerComponent_sqtk h e hz) (layerActor_component_quotient_two h)
    (layerActor_twoCore h e hz) layerAction_faithful (layer_source_conclusion h e hz).1
  obtain ⟨f,c,E,hf,_,_,hE⟩ := m.exists_full_model a
    (layerActor_component_quotient_two h) (layerActor_twoCore h e hz)
  have hs : moved (layerAction L R) (layerComponent L R) =
      m.ambientSection.space.toSubmodule := m.ambientSection.space_eq.symm
  let ψ := (NormalElementaryQuotient.movedEquiv X q (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _) K).trans (LinearEquiv.ofEq _ _ hs)
  have hψ (v : Additive (initialMoved L R)) :
      (ψ v).val = Additive.ofMul ⟨v.toMul,(commutator_le_left X K) v.toMul.property⟩ := by
    rfl
  refine ⟨f.comp q, ψ.trans E, ?_, ?_⟩
  · rw [MonoidHom.ker_comp_of_injective _ _ hf,QuotientGroup.ker_mk',hc]
  · intro g v
    change E (ψ (Additive.ofMul (MulAut.conjNormal g v))) =
      Hexacode.action (f (q g)) (E (ψ (Additive.ofMul v)))
    rw [←hE]
    apply congrArg E
    apply Subtype.ext
    rw [hψ]
    apply Additive.toMul.injective
    apply Subtype.ext
    change g * (v : M) * g⁻¹ =
      (((layerAction L R) (q g) (ψ (Additive.ofMul v)).val).toMul : M)
    rw [hψ]
    exact (NormalElementaryQuotient.representation_apply X q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) g
      (Additive.ofMul ⟨v,(commutator_le_left X K) v.property⟩)).symm

end AlternatingSixReconstruction.Exceptional.Exhaustion
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
local notation "T" => edge L R
local notation "M" => (L ⊔ R : Subgroup G)

theorem vertex_hexacode_model
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (hc : layerKernel L R = pCore 2 M)
    (c : Vertex T) (hcCol : color T c = false) :
    ∃ (f : stabilizer T c →* Atlas.Codes.HexAutomorphisms)
      (W : Subgroup (stabilizer T c)) (hWN : W.Normal)
      (hWE : IsElementaryAbelian 2 W),
      letI := hWN; letI := hWE
      W.map (stabilizer T c).subtype ≤ X T c ∧
      f.ker = (Q T c).subgroupOf (stabilizer T c) ∧
      ∃ φ : Additive W ≃ₗ[ZMod 2] Atlas.Codes.hexacode,
        ∀ (g : stabilizer T c) (v : W),
          φ (Additive.ofMul (MulAut.conjNormal g v)) =
            Hexacode.action (f g) (φ (Additive.ofMul v)) := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color T hcCol
  let H := stabilizer T (mVertex T g)
  let H0 := stabilizer T (alpha T)
  let b : M ≃* H0 := (MonoidHom.ofInjective (embedM_injective T)).trans
    (MulEquiv.subgroupCongr (stabilizer_m_base T).symm)
  have hG : H0.map (MulAut.conj g⁻¹).toMonoidHom = H := by
    simpa only [H0,H,alpha,act_mVertex,one_mul] using (stabilizer_act T g (alpha T)).symm
  let a : M ≃* H := b.trans (((MulAut.conj g⁻¹).subgroupMap H0).trans
    (MulEquiv.subgroupCongr hG))
  have ha (m : M) : (a m : FreeAmalgam T) = (MulAut.conj g⁻¹) (embedM T m) := rfl
  have hQ : (pCore 2 M).map a.toMonoidHom = (Q T (mVertex T g)).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_map, map_subgroupOf_eq_of_le (show Q T (mVertex T g) ≤ H from fun _ hx => hx.1)]
    change (pCore 2 M).map ((MulAut.conj g⁻¹).toMonoidHom.comp (embedM T)) = _
    rw [←map_map,←Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le]
    simpa only [alpha,act_mVertex,one_mul] using (Q_act T g (alpha T)).symm
  have hX : (centralOmega L R).map a.toMonoidHom = (X T (mVertex T g)).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_map, map_subgroupOf_eq_of_le (show X T (mVertex T g) ≤ H from
      (omegaCenter_le _).trans (fun _ hx => hx.1))]
    change (centralOmega L R).map ((MulAut.conj g⁻¹).toMonoidHom.comp (embedM T)) = _
    rw [←map_map,←graph_X h]
    simpa only [alpha,act_mVertex,one_mul] using (X_act T g (alpha T)).symm
  let := initialMoved_normal h
  obtain ⟨q,φ,hq,hφ⟩ := initial_moved_hexacode_model h e hz hc
  let W := (initialMoved L R).comap a.symm.toMonoidHom
  let : W.Normal := inferInstance
  let : IsElementaryAbelian 2 W :=
    IsElementaryAbelian.comap_of_injective a.symm.toMonoidHom a.symm.injective (initialMoved L R)
  let η := a.symm.toMonoidHom.subgroupComap (initialMoved L R)
  have hηi : Function.Injective η := by
    intro x y hh
    apply Subtype.ext
    exact a.symm.injective (congrArg Subtype.val hh)
  have hηs : Function.Surjective η :=
    MonoidHom.subgroupComap_surjective_of_surjective _ _ a.symm.surjective
  let ηlin := η.toAdditive.toZModLinearMap 2
  let ηequiv : Additive W ≃ₗ[ZMod 2] Additive (initialMoved L R) :=
    LinearEquiv.ofBijective ηlin ⟨fun x y hh => Additive.toMul.injective (hηi hh),
      fun v => by obtain ⟨w,hw⟩ := hηs v.toMul; exact ⟨Additive.ofMul w,congrArg Additive.ofMul hw⟩⟩
  refine ⟨q.comp a.symm.toMonoidHom,W,inferInstance,inferInstance,?_,?_,ηequiv.trans φ,?_⟩
  · rintro x ⟨w,hw,rfl⟩
    have hx : a.symm w ∈ centralOmega L R := (commutator_le_left _ _) hw
    have hm : w ∈ (centralOmega L R).map a.toMonoidHom := ⟨a.symm w,hx,a.apply_symm_apply w⟩
    rwa [hX] at hm
  · ext w
    change q (a.symm w) = 1 ↔ (w : FreeAmalgam T) ∈ Q T (mVertex T g)
    rw [←MonoidHom.mem_ker,hq]
    change a.symm w ∈ pCore 2 M ↔ w ∈ (Q T (mVertex T g)).subgroupOf H
    rw [←hQ]
    exact (mem_map_equiv).symm
  · intro y v
    change φ (Additive.ofMul (η (MulAut.conjNormal y v))) =
      Hexacode.action (q (a.symm y)) (φ (Additive.ofMul (η v)))
    rw [←hφ]
    apply congrArg φ
    apply Additive.toMul.injective
    apply Subtype.ext
    change a.symm (y * (v : H) * y⁻¹) =
      a.symm y * a.symm (v : H) * (a.symm y)⁻¹
    simp only [map_mul,map_inv]

end AlternatingSixReconstruction.Exceptional.Exhaustion
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
