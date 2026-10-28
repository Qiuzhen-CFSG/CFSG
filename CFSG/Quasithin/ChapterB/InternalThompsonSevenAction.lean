module
public import CFSG.Quasithin.ChapterB.InternalThompsonAction
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.FullMovedEquivalence
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.FullDeletedSevenActor

/-!
# The literal symmetric-seven quotient of the point action

The marked B.5.1 deleted-seven row contains a full S7 actor. Cohomology
has identified its central quotient with the whole original module. The
faithful normal-extension theorem embeds the full internal conjugation
quotient in S7, so the contained marked S7 forces equality. Composition
with the original quotient map gives H→S7 with kernel exactly C_H(W),
component image exactly A7, and the literal conjugation representation
identified with the natural seven-letter module. These are the action
inputs of C.1.24(a) used in Aschbacher–Smith 10.2.9, printed pp.751–753.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.InternalThompsonAction
open QuasisimpleSource BinaryPermutation
variable {H : Type*} [Group H] [Finite H]

theorem deleted_seven_quotient_coordinates
    (W : Subgroup H) [W.Normal] [IsElementaryAbelian 2 W]
    (K : Subgroup H) [K.Normal]
    (hAN : K.map (actionMk W) ≤ offenderSubgroup (action W))
    (s : MovedSection ((action W).comp (offenderSubgroup (action W)).subtype)
      ((K.map (actionMk W)).subgroupOf (offenderSubgroup (action W))))
    (hm : moved ((action W).comp (offenderSubgroup (action W)).subtype)
      ((K.map (actionMk W)).subgroupOf (offenderSubgroup (action W))) = ⊤)
    (hc : fixedSpace ((action W).comp (offenderSubgroup (action W)).subtype)
      ((K.map (actionMk W)).subgroupOf (offenderSubgroup (action W))) = ⊥)
    (m : MarkedActionEquiv s.central.quotientRepresentation (offenderSubgroup s.central.quotientRepresentation)
      ((K.map (actionMk W)).subgroupOf (offenderSubgroup (action W)))
      (naturalRepresentation (Fin 7)) (alternatingGroup (Fin 7))) :
    ∃ q : H →* Equiv.Perm (Fin 7), ∃ hq : Function.Surjective q,
    ∃ hk : q.ker = centralizer (W : Set H),
      K.map q = alternatingGroup (Fin 7) ∧
      ∃ eV : Additive W ≃ₗ[ZMod 2] natural (Fin 7),
      ∀ g v, eV (NormalElementaryQuotient.representation W q hq hk g v) =
        naturalRepresentation (Fin 7) g (eV v) := by
  let Q := ActionQuotient W
  let q0 := actionMk W
  let ρ := action W
  let A := K.map q0
  let N := offenderSubgroup ρ
  let C := A.subgroupOf N
  let E : A ≃* C := (subgroupOfEquivOfLe hAN).symm
  let : A.Normal := (inferInstance : K.Normal).map q0 (QuotientGroup.mk'_surjective _)
  let a : ActionEquiv (ρ.comp A.subtype) (alternatingNaturalRepresentation (Fin 7)) := {
    groupEquiv := E.trans m.subgroupEquiv
    linearEquiv := (s.fullProjectionEquiv hm hc).trans m.action.linearEquiv
    intertwines x v := by
      change m.action.linearEquiv (s.fullProjection hm (ρ x v)) = _
      rw [show s.fullProjection hm (ρ x v) =
        s.central.quotientRepresentation (E x : N) (s.fullProjection hm v) from
          s.fullProjection_intertwines hm (E x : N) v]
      have h := m.action.intertwines ⟨E x,m.contained (E x).property⟩ (s.fullProjection hm v)
      exact h.trans (congrArg
        (fun g => naturalRepresentation (Fin 7) g (m.action.linearEquiv (s.fullProjection hm v)))
        (m.compatible (E x))) }
  have hcard : Nat.card (Equiv.Perm (Fin 7)) ≤ Nat.card Q := calc
    Nat.card (Equiv.Perm (Fin 7)) = Nat.card (offenderSubgroup s.central.quotientRepresentation) :=
      Nat.card_congr m.action.groupEquiv.toEquiv.symm
    _ ≤ Nat.card N := Nat.card_le_card_of_injective _ Subtype.val_injective
    _ ≤ Nat.card Q := Nat.card_le_card_of_injective _ Subtype.val_injective
  obtain ⟨b,hb⟩ := full_deleted_seven_actor ρ (action_faithful W) A a hcard
  let q := b.groupEquiv.toMonoidHom.comp q0
  have hq : Function.Surjective q := b.groupEquiv.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = centralizer (W : Set H) :=
    (MonoidHom.ker_comp_of_injective q0 b.groupEquiv.toMonoidHom b.groupEquiv.injective).trans
      (QuotientGroup.ker_mk' _)
  have hK : K.map q = alternatingGroup (Fin 7) := by
    rw [show K.map q = A.map b.groupEquiv.toMonoidHom from (map_map _ _ _).symm]
    ext g
    constructor
    · rintro ⟨x,hx,rfl⟩
      change b.groupEquiv x ∈ alternatingGroup (Fin 7)
      rw [hb ⟨x,hx⟩]
      exact (a.groupEquiv ⟨x,hx⟩).property
    · intro hg
      obtain ⟨x,hx⟩ := a.groupEquiv.surjective ⟨g,hg⟩
      refine ⟨x,x.property,?_⟩
      exact (hb x).trans (congrArg Subtype.val hx)
  refine ⟨q,hq,hk,hK,b.linearEquiv,?_⟩
  intro g v
  obtain ⟨h,rfl⟩ := hq g
  have he : NormalElementaryQuotient.representation W q hq hk (q h) v = ρ (q0 h) v := by
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [NormalElementaryQuotient.representation_apply, action_apply]
  rw [he]
  exact b.intertwines (q0 h) v
end CFSG.Quasithin.ChapterB.InternalThompsonAction
