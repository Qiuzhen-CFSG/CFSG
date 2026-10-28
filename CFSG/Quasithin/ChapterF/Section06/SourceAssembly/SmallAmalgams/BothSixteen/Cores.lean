module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.MixedSixteen
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.SpecificGroups.QuaternionEightInvolution

/-!
# Local cores at overlap order sixteen

The cubic action on each self-centralizing core leaves only an elementary
eight or Q₈. The two cores intersect in at least four elements. An elementary
core cannot meet a quaternion core that largely. If both are quaternion,
the common involution is normalized by both vertices, contradicting
faithfulness. Thus both original cores are elementary abelian.

Source: the small characteristic-two cases in Aschbacher–Smith F.1.12 and
F.6.5. Only the original pair hypotheses and overlap order are used.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly.BothSixteen
variable {G : Type*} [Group G] [Finite G] {A B : Subgroup G}

private abbrev Q (A : Subgroup G) := (pCore 2 A).map A.subtype

omit [Finite G] in
private theorem normalizes_core (A : Subgroup G) : A ≤ normalizer (Q A : Set G) := by
  intro a ha
  apply (pCore 2 A).le_normalizer_map A.subtype
  exact ⟨⟨a,ha⟩,by rw [(pCore 2 A).normalizer_eq_top]; trivial,rfl⟩

theorem core_card (h : IsGoldschmidtTriple A B) (hT : Nat.card (A⊓B : Subgroup G)=16) :
    Nat.card (pCore 2 A)=8 := by
  have ha : Nat.card A=48 := by rw [h.local_card_eq_three_mul_intersection,hT]
  have hc := SymmetricThreeTwoCore.card_eq h.quotient_left.some
  omega

theorem core_shape (h : IsGoldschmidtTriple A B)
    (hA : generalizedFitting A=pCore 2 A) (hT : Nat.card (A⊓B : Subgroup G)=16) :
    IsElementaryAbelian 2 (pCore 2 A) ∨ Nonempty (pCore 2 A≃*QuaternionGroup 2) := by
  have hQ := core_card h hT
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := A) 3 (by
    rw [h.local_card_eq_three_mul_intersection,hT]; decide)
  have hx3 : x^3=1 := by rw [←hx]; exact pow_orderOf_eq_one x
  let a : MulAut (pCore 2 A) := MulAut.conjNormal x
  have ha3 : a^3=1 := by
    change (MulAut.conjNormal x)^3=1
    rw [←map_pow,hx3,map_one]
  have hane : a≠1 := by
    intro he
    have hxc : x∈centralizer (pCore 2 A : Set A) := by
      rw [mem_centralizer_iff]
      intro q hq
      have hh := congrArg (fun b : MulAut (pCore 2 A) => (b ⟨q,hq⟩ : A)) he
      change x*q*x⁻¹=q at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    let z : pCore 2 A := ⟨x,h.local_core_selfCentralizing hA hxc⟩
    have hz : orderOf z=3 := (Subgroup.orderOf_coe z).symm.trans hx
    have hh := (pCore_isPGroup (p := 2) (G := A)).orderOf_coprime
      (by decide : Nat.Coprime 2 3) z
    rw [hz] at hh
    norm_num at hh
  exact elementary_or_quaternion_of_small_two_group_cubic pCore_isPGroup hQ.le a ha3 hane

private theorem core_intersection_card_ge_four (h : IsGoldschmidtTriple A B)
    (hT : Nat.card (A⊓B : Subgroup G)=16) : 4≤Nat.card (Q A⊓Q B : Subgroup G) := by
  have hQA : Nat.card (Q A)=8 := (card_map_of_injective A.subtype_injective).trans (core_card h hT)
  have hQB : Nat.card (Q B)=8 := (card_map_of_injective B.subtype_injective).trans
    (core_card h.symm (by simpa only [inf_comm B A] using hT))
  have hn : Q B≤normalizer (Q A : Set G) :=
    (h.symm.local_twoCore_le_intersection.trans inf_le_right).trans (normalizes_core A)
  have hp := card_mul_eq_card_inf_mul_card_sup_of_normalizes (Q A) (Q B) hn
  have hle : Q A⊔Q B≤A⊓B := sup_le h.local_twoCore_le_intersection
    (by simpa only [inf_comm B A] using h.symm.local_twoCore_le_intersection)
  have hu := card_le_of_le hle
  rw [hT] at hu
  rw [hQA,hQB] at hp
  nlinarith

omit [Finite G] in
private theorem quaternion_elementary_intersection_small {P R : Subgroup G}
    (e : P≃*QuaternionGroup 2) [IsElementaryAbelian 2 R] :
    Nat.card (P⊓R : Subgroup G)≤2 := by
  let f : (P⊓R : Subgroup G) → {q : QuaternionGroup 2 // q^2=1} := fun x =>
    ⟨e ⟨x,x.property.1⟩,by
      rw [←map_pow,←map_one e]
      apply congrArg e
      exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (x : G) x.property.2)⟩
  have hf : Function.Injective f := by
    intro x y he
    exact Subtype.ext (congrArg (fun z : P => (z : G)) (e.injective (congrArg Subtype.val he)))
  have hc : Nat.card {q : QuaternionGroup 2 // q^2=1}=2 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  exact hc ▸ Nat.card_le_card_of_injective f hf

omit [Finite G] in
private theorem normalizer_fixes_quaternion_involution {P : Subgroup G}
    (e : P≃*QuaternionGroup 2) {z : G} (hz : z∈P) (hz2 : orderOf z=2)
    {a : G} (ha : a∈normalizer (P : Set G)) : a*z*a⁻¹=z := by
  have haz : a*z*a⁻¹∈P := (mem_normalizer_iff.mp ha z).mp hz
  let x : P := ⟨a*z*a⁻¹,haz⟩
  let y : P := ⟨z,hz⟩
  have hx : orderOf x=2 := (Subgroup.orderOf_coe x).symm.trans
    (((MulAut.conj a).orderOf_eq z).trans hz2)
  have hy : orderOf y=2 := (Subgroup.orderOf_coe y).symm.trans hz2
  exact congrArg Subtype.val (e.injective (QuaternionGroup.eq_of_orderOf_eq_two _ _
    ((e.orderOf_eq x).trans hx) ((e.orderOf_eq y).trans hy)))


private theorem not_both_quaternion (h : IsGoldschmidtTriple A B)
    (hcore : pCore 2 G=⊥) (hT : Nat.card (A⊓B : Subgroup G)=16)
    (eA : pCore 2 A≃*QuaternionGroup 2) (eB : pCore 2 B≃*QuaternionGroup 2) : False := by
  let eQA : Q A≃*QuaternionGroup 2 :=
    ((pCore 2 A).equivMapOfInjective A.subtype A.subtype_injective).symm.trans eA
  let eQB : Q B≃*QuaternionGroup 2 :=
    ((pCore 2 B).equivMapOfInjective B.subtype B.subtype_injective).symm.trans eB
  let I := Q A⊓Q B
  have hI4 : 4≤Nat.card I := core_intersection_card_ge_four h hT
  have hIp : IsPGroup 2 I := (pCore_isPGroup.map A.subtype).to_le inf_le_left
  have hId : 2∣Nat.card I := hIp.card_eq_or_dvd.resolve_left (by omega)
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := I) 2 hId
  have hz2 : orderOf (z : G)=2 := (Subgroup.orderOf_coe z).trans hz
  let N := zpowers (z : G)
  have hNI : N≤I := zpowers_le.mpr z.property
  have hNle : N≤A⊓B := hNI.trans (inf_le_left.trans h.local_twoCore_le_intersection)
  have hnA : (N.subgroupOf A).Normal := by
    apply (normal_subgroupOf_iff_le_normalizer (hNle.trans inf_le_left)).mpr
    intro a ha
    rw [mem_normalizer_iff_map_conj_eq,MonoidHom.map_zpowers]
    exact congrArg zpowers (normalizer_fixes_quaternion_involution eQA z.property.1 hz2
      (normalizes_core A ha))
  have hnB : (N.subgroupOf B).Normal := by
    apply (normal_subgroupOf_iff_le_normalizer (hNle.trans inf_le_right)).mpr
    intro a ha
    rw [mem_normalizer_iff_map_conj_eq,MonoidHom.map_zpowers]
    exact congrArg zpowers (normalizer_fixes_quaternion_involution eQB z.property.2 hz2
      (normalizes_core B ha))
  have hn := h.common_normal_eq_bot hcore N hNle hnA hnB
  have hz1 : (z : G)=1 := by
    have hzN : (z : G)∈N := mem_zpowers _
    rwa [hn,mem_bot] at hzN
  rw [hz1,orderOf_one] at hz2
  omega

/-- In a faithful characteristic-two pair with common Sylow order sixteen,
the original local cores are elementary of order eight. Quaternion cores
are excluded using their common involution, not an assumed core identity. -/
theorem left_core_elementary (h : IsGoldschmidtTriple A B)
    (hcore : pCore 2 G=⊥)
    (hA : generalizedFitting A=pCore 2 A) (hB : generalizedFitting B=pCore 2 B)
    (hT : Nat.card (A⊓B : Subgroup G)=16) : IsElementaryAbelian 2 (pCore 2 A) := by
  rcases core_shape h hA hT with he | hqA
  · exact he
  obtain ⟨eA⟩ := hqA
  rcases core_shape h.symm hB (by simpa only [inf_comm B A] using hT) with he | hqB
  · let : IsElementaryAbelian 2 (pCore 2 B) := he
    let : IsElementaryAbelian 2 (Q B) := IsElementaryAbelian.map_subtype
    let eQA : Q A≃*QuaternionGroup 2 :=
      ((pCore 2 A).equivMapOfInjective A.subtype A.subtype_injective).symm.trans eA
    have hlow := core_intersection_card_ge_four h hT
    have hup := quaternion_elementary_intersection_small (R := Q B) eQA
    omega
  · obtain ⟨eB⟩ := hqB
    exact (not_both_quaternion h hcore hT eA eB).elim

end CFSG.Quasithin.ChapterF.SourceAssembly.BothSixteen
