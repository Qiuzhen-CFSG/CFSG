module

public import Theory.GroupTheory.QuaternionInvolutionFixedEight
public import Theory.GroupTheory.PGroup.ClassTwoCyclicCenter
public import Theory.GroupTheory.NormalCenterQuotient

/-!
# Normality of fixed elementary eights in quaternion-core extensions

If a normal extraspecial quaternion central product has abelian ambient quotient,
an involution with fixed elementary subgroup of order eight fixes a normal
subgroup of the ambient group. The quaternion swap calculation identifies the
fixed subgroup with the commutator with the involution. This commutator contains
the derived subgroup of the core, so conjugation modulo the abelian quotient
preserves it. This supplies the normality, rather than merely the existence,
needed in Janko–Thompson (1970), §4, case (b)(ii), printed p.391.
-/

open Subgroup
open scoped commutatorElement

namespace Subgroup

/-- A relative commutator containing the core derived subgroup is normal
when the quotient by the core is abelian. -/
public theorem commutator_normal_of_abelian_quotient
    {P : Type*} [Group P] (H J : Subgroup P) [H.Normal]
    [IsMulCommutative (P ⧸ H)] (hder : ⁅H,H⁆ ≤ ⁅H,J⁆) :
    (⁅H,J⁆ : Subgroup P).Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  apply le_normalizer_closure_iff.mpr
  rintro g _ _ ⟨a, ha, b, hb, rfl⟩
  let f := MulAut.conj g
  have hfa : f a ∈ H := (inferInstance : H.Normal).conj_mem a ha g
  have hgb : ⁅g,b⁆ ∈ H :=
    Normal.quotient_commutative_iff_commutator_le.mp inferInstance
      (commutator_mem_commutator (mem_top g) (mem_top b))
  have hN := normalizer_commutator_ge_left H J hgb
  change f ⁅a,b⁆ ∈ ⁅H,J⁆
  rw [map_commutatorElement, show f b = ⁅g,b⁆ * b from conj_eq_commutatorElement_mul,
    commutatorElement_mul_right_eq_mul_conj]
  have hx := hder (commutator_mem_commutator hfa hgb)
  have hy := (mem_normalizer_iff.mp hN _).mp (commutator_mem_commutator hfa hb)
  simpa only [mul_assoc] using (⁅H,J⁆ : Subgroup P).mul_mem hx hy

/-- A fixed subgroup equal to the relative commutator is normal in an
abelian extension of a normal extraspecial two-group. -/
public theorem extraspecial_fixed_normal_of_eq_commutator
    {P : Type*} [Group P] [Finite P] (H : Subgroup P)
    [H.Normal] [IsExtraspecial 2 H] [IsMulCommutative (P ⧸ H)]
    (t : P) (heq : ⁅H,zpowers t⁆ = H ⊓ centralizer ({t} : Set P)) :
    (H ⊓ centralizer ({t} : Set P) : Subgroup P).Normal := by
  let Z := (center H).map H.subtype
  let : Z.Normal := ConjAct.normal_of_characteristic_of_normal
  have hZ : Z ≤ center P := central_of_normal_card_two Z
    ((card_map_of_injective H.subtype_injective).trans (IsExtraspecial.center_order_p 2 H))
  have hder : ⁅H,H⁆ ≤ Z := by
    rw [← map_subtype_commutator]
    exact map_mono (IsExtraspecial.quotient_elementary_abelian 2 H).commutator_le_center_of_central_quotient
  rw [← heq]
  apply commutator_normal_of_abelian_quotient H (zpowers t)
  rw [heq]
  exact le_inf (hder.trans (map_subtype_le _)) (hder.trans (hZ.trans (by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (mem_center_iff.mp ha t).symm)))

/-- In an abelian extension of a quaternion central product, a fixed elementary
 eight is normal in the whole extension. -/
public theorem quaternion_fixed_eight_normal
    {P : Type*} [Group P] [Finite P] (H : Subgroup P)
    [H.Normal] [IsExtraspecial 2 H] [IsMulCommutative (P ⧸ H)]
    (hH : Nat.card H = 32) (B C : Subgroup H)
    (hB : Nonempty (B ≃* QuaternionGroup 2)) (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = ⊤) (hinter : Nat.card (B ⊓ C : Subgroup H) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b)
    (t : P) (ht : t ^ 2 = 1)
    (hfixed : IsElementaryAbelian 2 (H ⊓ centralizer ({t} : Set P) : Subgroup P))
    (hcard : Nat.card (H ⊓ centralizer ({t} : Set P) : Subgroup P) = 8) :
    (H ⊓ centralizer ({t} : Set P) : Subgroup P).Normal := by
  let B' := B.map H.subtype
  let C' := C.map H.subtype
  have hB' : Nonempty (B' ≃* QuaternionGroup 2) := by
    obtain ⟨e⟩ := hB
    exact ⟨(B.equivMapOfInjective H.subtype H.subtype_injective).symm.trans e⟩
  have hC' : Nonempty (C' ≃* QuaternionGroup 2) := by
    obtain ⟨e⟩ := hC
    exact ⟨(C.equivMapOfInjective H.subtype H.subtype_injective).symm.trans e⟩
  have hjoin' : B' ⊔ C' = H := by
    rw [← map_sup, hjoin, ← MonoidHom.range_eq_map, H.range_subtype]
  have hinter' : Nat.card (B' ⊓ C' : Subgroup P) = 2 := by
    rw [← map_inf B C H.subtype H.subtype_injective, card_map_of_injective H.subtype_injective]
    exact hinter
  have hcomm' : ∀ b ∈ B', ∀ c ∈ C', b*c=c*b := by
    rintro _ ⟨b,hb,rfl⟩ _ ⟨c,hc,rfl⟩
    exact congrArg H.subtype (hcomm b hb c hc)
  apply extraspecial_fixed_normal_of_eq_commutator H t
  have heq := commutator_zpowers_eq_fixed_eight B' C' hB' hC' hinter' hcomm'
    (hjoin' ▸ hH) t ht
    (by rw [hjoin', H.normalizer_eq_top]; trivial)
    (hjoin' ▸ hcard) (hjoin' ▸ hfixed)
  simpa only [hjoin'] using heq

end Subgroup
