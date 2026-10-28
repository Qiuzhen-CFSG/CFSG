module
public import Theory.SpecificGroups.AlternatingSix.AlternatingFourActions
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.FourMovementSource

/-!
# Natural automorphisms preserve four-groups in a two-group action

Embed the actual two-group action into a Sylow subgroup of Aut(A₆).
Its inner D₈ has exactly two four-groups, and their normalizers are the
natural S₆ intersection. Thus a natural actor preserves either four-group
already in the action. Applied to conjugation on a normal component, the
original noncommuting right conjugate forces the actor outside natural S₆.

Source: Aschbacher–Smith 2.4.35(2), printed p.548.
-/

public section
open Subgroup
namespace AlternatingSix.ShadowLocal
open SylowGeometry

/-- A natural element of a two-group action normalizes every inner four-group
already contained in that action. -/
theorem natural_preserves_four_in_twoGroup
    (A : Subgroup AutA6) (hA : IsPGroup 2 A)
    (F : Subgroup A6) [IsKleinFour F]
    (hFA : F.map (MulAut.conj : A6 →* AutA6) ≤ A)
    (a : AutA6) (ha : a ∈ A) (hn : a ∈ natural) : F.map a.toMonoidHom = F := by
  obtain ⟨P,hAP⟩ := hA.exists_le_sylow
  let E := F.map (MulAut.conj : A6 →* AutA6)
  have hEP : E ≤ P := hFA.trans hAP
  let EP := E.subgroupOf (P : Subgroup AutA6)
  let eF : F ≃* EP := (F.equivMapOfInjective (MulAut.conj : A6 →* AutA6)
    inner_injective).trans (subgroupOfEquivOfLe hEP).symm
  let : IsKleinFour EP := {
    card_four := (Nat.card_congr eF.toEquiv).symm.trans IsKleinFour.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eF).symm.trans IsKleinFour.exponent_two }
  have hEI : EP ≤ sylowInner P := by
    rintro d ⟨f,hf,he⟩
    exact ⟨f,he⟩
  have hN : normalizer (EP : Set P) = sylowNatural P := by
    rcases kleinFour_subgroups_inner P EP hEI with h | h
    · rw [h,normalizer_kleinZero]
    · rw [h,normalizer_kleinOne]
  let aP : P := ⟨a,hAP ha⟩
  have hnP : aP ∈ normalizer (EP : Set P) := hN ▸ hn
  have hfix : EP.map (MulAut.conj aP).toMonoidHom = EP :=
    mem_normalizer_iff_map_conj_eq.mp hnP
  have hh := congrArg (Subgroup.map (P : Subgroup AutA6).subtype) hfix
  have hcomp : (P : Subgroup AutA6).subtype.comp (MulAut.conj aP).toMonoidHom =
      (MulAut.conj a).toMonoidHom.comp (P : Subgroup AutA6).subtype := by
    apply MonoidHom.ext
    intro x
    rfl
  rw [map_map,hcomp,←map_map,map_subgroupOf_eq_of_le hEP] at hh
  change E.map (MulAut.conj a).toMonoidHom = E at hh
  rw [FourNormalizers.inner_map_transport F a] at hh
  exact (map_injective inner_injective) hh

variable {H : Type*} [Group H] [Finite H]

/-- An actual two-group actor moving a four-group in its normal A₆ component
lies outside natural S₆. The conjugate is the source right conjugate. -/
theorem conjugationAction_not_natural_of_four_movement
    (K : Subgroup H) [K.Normal] (e : K ≃* A6)
    (S U : Subgroup H) (hS : IsPGroup 2 S) [IsKleinFour U]
    (hUK : U ≤ K) (hUS : U ≤ S) (x : H) (hx : x ∈ S)
    (hm : ¬ U.map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U : Set H)) :
    conjugationAction K e x ∉ natural := by
  let A := S.map (conjugationAction K e)
  let F := (U.subgroupOf K).map e.toMonoidHom
  let eF : U ≃* F := (subgroupOfEquivOfLe hUK).symm.trans
    ((U.subgroupOf K).equivMapOfInjective e.toMonoidHom e.injective)
  let : IsKleinFour F := {
    card_four := (Nat.card_congr eF.toEquiv).symm.trans IsKleinFour.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eF).symm.trans IsKleinFour.exponent_two }
  have hFA : F.map (MulAut.conj : A6 →* AutA6) ≤ A := by
    rintro _ ⟨_,⟨u,hu,rfl⟩,rfl⟩
    exact (conjugationAction_on_inner K e u) ▸
      mem_map_of_mem (conjugationAction K e) (hUS hu)
  intro hn
  have hf := natural_preserves_four_in_twoGroup A (hS.map _) F hFA
    (conjugationAction K e x) (mem_map_of_mem _ hx) hn
  have hxN : x ∈ normalizer (U : Set H) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rintro _ ⟨u,hu,rfl⟩
      let uK : K := ⟨u,hUK hu⟩
      have he : conjugationAction K e x (e uK) ∈ F :=
        hf ▸ mem_map_of_mem (conjugationAction K e x).toMonoidHom
          (mem_map_of_mem e.toMonoidHom hu)
      rw [conjugationAction_apply] at he
      obtain ⟨v,hv,he⟩ := he
      have hev : (v : H) = x * u * x⁻¹ := congrArg Subtype.val (e.injective he)
      change x * u * x⁻¹ ∈ U
      exact hev ▸ hv
    · exact (card_map_of_injective (K := U) (MulAut.conj x).injective).ge
  have hxiN := (normalizer (U : Set H)).inv_mem hxN
  rw [mem_normalizer_iff_map_conj_eq] at hxiN
  apply hm
  rw [MulEquiv.toMonoidHom_eq_coe, hxiN]
  exact le_centralizer_iff_isMulCommutative.mpr IsKleinFour.isMulCommutative

end AlternatingSix.ShadowLocal
