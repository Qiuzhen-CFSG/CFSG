module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointOrdinaryModels
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointOrdinaryCenter
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# Original ordinary closure structure with explicit remaining sporadic cases

The genuine model theorem leaves PSL₃(4), Held, and Rudvalis. In the linear
case the literal closure is the actual component, so its central quotient
transports to the fixed matrix model over the four-element field. The proved
center calculation identifies its whole center with the original field point.
The Held and Rudvalis alternatives remain explicit.

Source: Aschbacher--Smith 12.7.5, printed p.840.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The literal original closure has the required linear quotient and field-point
center, unless the actual ordinary component has Held or Rudvalis quotient. -/
theorem original_tripleSix_point_ordinary_structure_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (J : Subgroup (centralizer ({(t : G)} : Set G)))
    (hJ : IsComponent (centralizer ({(t : G)} : Set G)) J) :
    let H := centralizer ({(t : G)} : Set G)
    let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
    let B := conjugateSpanBy Lt H
    (centerIn B = tripleSixPoint D a t ∧
      Nonempty ((B ⧸ center B) ≃* Matrix.PSL3Four.PSL)) ∨
      Nonempty ((J ⧸ center J) ≃* Held.He) ∨
      Nonempty ((J ⧸ center J) ≃* Rudvalis.Model) := by
  let H := centralizer ({(t : G)} : Set G)
  let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
  let B := conjugateSpanBy Lt H
  rcases original_tripleSix_point_ordinary_models_at h structural D a t ht heven J hJ with
    hm | hm | hm
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let := Fintype.ofFinite F
    let := Fintype.ofFinite Matrix.PSL3Four.F
    let f : F ≃+* Matrix.PSL3Four.F := FiniteField.ringEquivOfCardEq (by
      rw [←Nat.card_eq_fintype_card,←Nat.card_eq_fintype_card,hF,Matrix.PSL3Four.card_F])
    let eJ : J ⧸ center J ≃* Matrix.PSL3Four.PSL := e.trans (Atlas.fieldEquivPSL 3 f)
    have hOrd := original_tripleSix_point_ordinary_closure_at h structural D a t ht heven J hJ
    let b : B ≃* J := (MulEquiv.subgroupCongr hOrd.1).trans
      (J.equivMapOfInjective H.subtype H.subtype_injective).symm
    have hc : (center B).map b.toMonoidHom = center J := by
      ext y
      constructor
      · rintro ⟨x,hx,rfl⟩
        exact (centerCongr b ⟨x,hx⟩).property
      · intro hy
        exact ⟨b.symm y,(centerCongr b.symm ⟨y,hy⟩).property,b.apply_symm_apply y⟩
    let eB : B ⧸ center B ≃* Matrix.PSL3Four.PSL :=
      (QuotientGroup.congr _ _ b hc).trans eJ
    exact .inl ⟨original_tripleSix_point_ordinary_center_at h structural D a t ht heven J hJ eB,
      ⟨eB⟩⟩
  · exact .inr (.inl hm)
  · exact .inr (.inr hm)

/-- The linear branch also records the actual embedded field point as the
center inside B and forms the quotient by that original subgroup itself. -/
theorem original_tripleSix_point_ordinary_module_structure_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (J : Subgroup (centralizer ({(t : G)} : Set G)))
    (hJ : IsComponent (centralizer ({(t : G)} : Set G)) J) :
    let H := centralizer ({(t : G)} : Set G)
    let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
    let B := conjugateSpanBy Lt H
    let Vt := tripleSixPoint D a t
    (centerIn B = Vt ∧ Vt.subgroupOf B = center B ∧
      ∃ hn : (Vt.subgroupOf B).Normal, letI := hn
        Nonempty ((B ⧸ Vt.subgroupOf B) ≃* Matrix.PSL3Four.PSL)) ∨
      Nonempty ((J ⧸ center J) ≃* Held.He) ∨
      Nonempty ((J ⧸ center J) ≃* Rudvalis.Model) := by
  let H := centralizer ({(t : G)} : Set G)
  let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
  let B := conjugateSpanBy Lt H
  let Vt := tripleSixPoint D a t
  rcases original_tripleSix_point_ordinary_structure_at h structural D a t ht heven J hJ with
    ⟨hz,⟨e⟩⟩ | hm | hm
  · change centerIn B = Vt at hz
    change B ⧸ center B ≃* Matrix.PSL3Four.PSL at e
    have hVB : Vt ≤ B := by
      rw [←hz,centerIn_eq_map_center]
      exact map_subtype_le _
    have hc : Vt.subgroupOf B = center B := by
      apply map_injective B.subtype_injective
      rw [map_subgroupOf_eq_of_le hVB,←centerIn_eq_map_center]
      exact hz.symm
    have hn : (Vt.subgroupOf B).Normal := by rw [hc]; infer_instance
    refine .inl ⟨hz,hc,hn,?_⟩
    let := hn
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hc).trans e⟩
  · exact .inr (.inl hm)
  · exact .inr (.inr hm)

end CFSG.Quasithin.Chapter12.Section07
