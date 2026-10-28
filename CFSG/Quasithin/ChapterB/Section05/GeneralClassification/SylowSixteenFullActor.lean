module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SylowSixteenCubicMarking
public import Theory.Representation.HexacodeAction.FaithfulNormalOvergroup

/-!
# The full actor of the original marked binary six-space

The fitting subgroup of the actual normal offender subgroup is carried
into the whole actor as a normal subgroup. Its proved cubic marking extends
in the same coordinates, and the actual Sylow order sixteen forces the
full hexacode group. The marked fitting component maps exactly to the even
subgroup; no ambient normalizer or centralizer is identified by assumption.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Atlas.Codes
namespace CFSG.Quasithin.ChapterB.SourceInduction.SylowSixteenSixSpace
open QuasisimpleSource
variable {D V : Type*} [Group D] [Finite D]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem full_actor_of_cubic_source (ρ : Representation (ZMod 2) D V)
    (hf : Function.Injective ρ) (hi : ρ.IsIrreducible)
    (hd : Module.finrank (ZMod 2) V=6)
    (hq : IsQuasisimple (generalizedFitting (offenderSubgroup ρ)))
    (c : ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp (offenderSubgroup ρ).subtype) (generalizedFitting (offenderSubgroup ρ)))
    (hc : Nat.card (center (generalizedFitting (offenderSubgroup ρ)))=3)
    (eq : (generalizedFitting (offenderSubgroup ρ) ⧸
      center (generalizedFitting (offenderSubgroup ρ)))≃*alternatingGroup (Fin 6))
    (S : Sylow 2 D) (hS : Nat.card S=16) :
    ∃ e : ActionEquiv ρ Hexacode.action,
      ((generalizedFitting (offenderSubgroup ρ)).map (offenderSubgroup ρ).subtype).map
        e.groupEquiv.toMonoidHom=hexSign.ker := by
  let J := offenderSubgroup ρ
  let F := generalizedFitting J
  let N := F.map J.subtype
  let : J.Normal := offenderSubgroup_normal ρ
  let : F.Characteristic := generalizedFitting_characteristic
  let : N.Normal := inferInstance
  obtain ⟨a⟩ := cubic_fitting_actionEquiv ρ hf hi hd hq c hc eq
  let en := F.equivMapOfInjective J.subtype J.subtype_injective
  let b : ActionEquiv (ρ.comp N.subtype) Hexacode.evenAction := {
    groupEquiv := en.symm.trans a.groupEquiv
    linearEquiv := a.linearEquiv
    intertwines := by
      intro n v
      have hh := a.intertwines (en.symm n) v
      have he : ((en.symm n : F) : J).val=n.val :=
        congrArg Subtype.val (en.apply_symm_apply n)
      change a.linearEquiv (ρ ((en.symm n : F) : J).val v)=
        Hexacode.evenAction (a.groupEquiv (en.symm n)) (a.linearEquiv v) at hh
      rw [he] at hh
      exact hh }
  obtain ⟨e,hm,he⟩ := Hexacode.full_equivariant_of_sylow_sixteen
    ρ hf N b.groupEquiv b.linearEquiv b.intertwines S hS
  exact ⟨⟨e,b.linearEquiv,he⟩,hm⟩

/-- Complete original B.5, the A5 offender and the marked fixed line construct
an action equivalence for every element of the whole actor. -/
theorem full_actor_from_source (ρ : Representation (ZMod 2) D V)
    (hf : Function.Injective ρ) (hi : ρ.IsIrreducible)
    (hd : Module.finrank (ZMod 2) V=6)
    (cover : SQTKQuotient KnownSimple.IsKnownSimple D)
    (hsyl : ∀ S : Sylow 2 D, Nat.card S=16)
    (C : Subgroup D) (hCJ : C≤offenderSubgroup ρ)
    (eC : C≃*alternatingGroup (Fin 5)) (hCfix : fixedSpace ρ C≠⊥)
    (A : Subgroup D) (hA : IsPGroup 2 A)
    (hfix : Module.finrank (ZMod 2) (fixedSpace ρ A)=1) :
    ∃ e : ActionEquiv ρ Hexacode.action,
      ((generalizedFitting (offenderSubgroup ρ)).map (offenderSubgroup ρ).subtype).map
        e.groupEquiv.toMonoidHom=hexSign.ker := by
  obtain ⟨hq,⟨c⟩,⟨ec⟩,⟨eq⟩⟩ := cubic_from_source ρ hf hi hd cover
    (fun S => (hsyl S).le) C hCJ eC hCfix A hA hfix
  have hc : Nat.card (center (generalizedFitting (offenderSubgroup ρ)))=3 := by
    rw [Nat.card_congr ec.toEquiv]
    simp
  exact full_actor_of_cubic_source ρ hf hi hd hq c hc eq default (hsyl default)

end CFSG.Quasithin.ChapterB.SourceInduction.SylowSixteenSixSpace
