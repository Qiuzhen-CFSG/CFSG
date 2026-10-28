module
public import CFSG.Quasithin.ChapterC.Section03.A5.MathieuTwentyTwo
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingFive.CubicNormalizer
public import Theory.GroupTheory.CoprimeNormalizerAutomorphisms
public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# Real cubic actors in an alternating-five block

The quotient's cubic elements are inverted in A₅. Coprime normalizer lifting
realizes the same automorphism of the actual order-three subgroup upstairs.
The genuine deleted-five module has a nonidentity fixed vector for every
cubic actor, so a block supplies a real cubic commuting with an involution.
Source application: Aschbacher–Smith, 2.4.25, printed pp.542–543.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC
variable {H : Type*} [Group H] [Finite H]

private theorem alternating_cubic_real : ∀ a : alternatingGroup (Fin 5), a^3=1 →
    ∃ b : alternatingGroup (Fin 5), b*a*b⁻¹=a⁻¹ := by decide +kernel

/-- Every order-three element of an alternating-five block is real in the block. -/
theorem IsAlternatingBlock.cubic_real (h : IsAlternatingBlock H 5)
    (a : H) (ha : orderOf a=3) : IsConj a a⁻¹ := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := h.2.2.quotient_iso
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker=pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hcop : Nat.Coprime 3 (Nat.card q.ker) := by
    rw [hk]
    obtain ⟨k,hk⟩ := (pCore_isPGroup : IsPGroup 2 (pCore 2 H)).exists_card_eq
    rw [hk]
    exact (by decide : Nat.Coprime 3 2).pow_right k
  let C := zpowers a
  have hC : IsPGroup 3 C := IsPGroup.of_card (n:=1) (by rw [Nat.card_zpowers,ha,pow_one])
  let : Fact (IsPGroup 3 C) := ⟨hC⟩
  have hinj := injective_comp_subtype_of_coprime_ker q hcop C hC
  obtain ⟨b,hb⟩ := alternating_cubic_real (q a) (by rw [←map_pow,←ha,pow_orderOf_eq_one,map_one])
  have hbN : b ∈ normalizer (C.map q : Set (alternatingGroup (Fin 5))) := by
    change b ∈ normalizer ((zpowers a).map q : Set _)
    rw [MonoidHom.map_zpowers]
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [MonoidHom.map_zpowers]
    change zpowers (b*q a*b⁻¹)=zpowers (q a)
    rw [hb,zpowers_inv]
  rw [normalizer_map_eq_of_coprime_kernel 3 C q hq hcop] at hbN
  obtain ⟨g,hg,hgb⟩ := hbN
  have hca : g*a*g⁻¹∈C := (mem_normalizer_iff.mp hg a).mp (mem_zpowers a)
  have hia : a⁻¹∈C := C.inv_mem (mem_zpowers a)
  have he : (⟨g*a*g⁻¹,hca⟩:C)=⟨a⁻¹,hia⟩ := by
    apply hinj
    change q (g*a*g⁻¹)=q a⁻¹
    rw [map_mul,map_mul,map_inv,map_inv,hgb,hb]
  exact isConj_iff.mpr ⟨g,congrArg Subtype.val he⟩

end CFSG.Quasithin.ChapterC
