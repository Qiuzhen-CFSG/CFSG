module
public import Theory.SpecificGroups.SL2.TorusMoverCentralizer
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# Torus and mover rigidity above a two-core

An automorphism preserving a Sylow subgroup and fixing its full odd torus
and one mover induces the identity on a characteristic-two SL₂ quotient.
The quotient map is injective on the odd torus, so the full torus marking
survives passage to the quotient. The Sylow normalizer lifts through the
two-core, preserving the literal mover condition.

Source: the quotient automorphism step of DGS (10.8), printed p.160.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup
variable {F A : Type*} [Field F] [Finite F] [CharP F 2] [Group A] [Finite A]

theorem core_quotient_torus_mover_fixed (hF : 2 < Nat.card F)
    (e : (A ⧸ pCore 2 A) ≃* SL(2,F))
    (T : Sylow 2 A) (C : Subgroup A)
    (hC : C ≤ normalizer (T : Set A))
    (ho : Odd (Nat.card C)) (hcard : Nat.card C = Nat.card Fˣ)
    (α : MulAut A) (hT : (T : Subgroup A).map α.toMonoidHom = T)
    (hfixC : ∀ c ∈ C, α c = c)
    (a : A) (ha : a ∉ normalizer (T : Set A)) (hfixa : α a = a) :
    quotientAut (pCore 2 A) α = 1 := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 A := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hker : q.ker ≤ (T : Subgroup A) := hk ▸ pCore_isPGroup.le_sylow_of_normal T
  let S := T.mapSurjective hq
  let D := C.map q
  let β := MulAut.congr e (quotientAut (pCore 2 A) α)
  have hβ (x : A) : β (q x) = q (α x) := by
    change e (quotientAut (pCore 2 A) α (e.symm (e (QuotientGroup.mk' _ x)))) = _
    rw [e.symm_apply_apply,quotientAut_apply_mk]
    rfl
  have hDS : D ≤ normalizer (S : Set SL(2,F)) :=
    (map_mono hC).trans (le_normalizer_map q)
  have hDo : Odd (Nat.card D) := ho.of_dvd_nat (C.card_map_dvd q)
  have hd : Disjoint C q.ker := by
    obtain ⟨n,hn⟩ := (show IsPGroup 2 q.ker from hk ▸ pCore_isPGroup).exists_card_eq
    exact disjoint_of_coprime_natCard (by rw [hn]; exact ho.coprime_two_right.pow_right n)
  have hqi : Function.Injective (q.subgroupMap C) := by
    apply (injective_iff_map_eq_one _).mpr
    intro x hx
    apply Subtype.ext
    apply disjoint_def.mp hd x.property
    exact congrArg Subtype.val hx
  have hDc : Nat.card D = Nat.card Fˣ :=
    (Nat.card_congr (MulEquiv.ofBijective (q.subgroupMap C)
      ⟨hqi,q.subgroupMap_surjective C⟩).toEquiv).symm.trans hcard
  have hS : (S : Subgroup SL(2,F)).map β.toMonoidHom = S := by
    change ((T : Subgroup A).map q).map β.toMonoidHom = (T : Subgroup A).map q
    rw [Subgroup.map_map,show β.toMonoidHom.comp q = q.comp α.toMonoidHom from
      MonoidHom.ext hβ,←Subgroup.map_map,hT]
  have hfixD : ∀ d ∈ D, β d = d := by
    rintro _ ⟨c,hc,rfl⟩
    rw [hβ,hfixC c hc]
  have hqa : q a ∉ normalizer (S : Set SL(2,F)) := by
    intro hh
    apply ha
    have he : (normalizer (S : Set SL(2,F))).comap q = normalizer (T : Set A) := by
      change (normalizer ((T : Subgroup A).map q : Set SL(2,F))).comap q = _
      rw [comap_normalizer_eq_of_surjective _ hq,comap_map_eq_self hker,T.coe_coe]
    exact he ▸ hh
  have hβ1 := odd_torus_and_mover_fixed_eq_one hF S D hDS hDo hDc β hS hfixD
    (q a) hqa (by rw [hβ,hfixa])
  apply (MulAut.congr e).injective
  simpa only [map_one] using hβ1
end Matrix.SpecialLinearGroup
