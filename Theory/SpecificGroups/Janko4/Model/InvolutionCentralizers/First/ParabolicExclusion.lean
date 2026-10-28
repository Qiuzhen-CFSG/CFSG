module
public import Theory.GroupTheory.PCoreSectionCard
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.QuotientExtension
public import Theory.Mathieu.M22.Properties.TwoLocalSeven

/-!
# The first-centralizer exclusion for small-core parabolics

A full-Sylow subgroup of the native first centralizer, divisible by seven,
cannot embed in a group whose two-core quotient has order 1008. Intersect
with the actual index-two subgroup and project through the full kernel
of order 2^13 times 3 to M22. Seven survives both operations, and the
original full Sylow restricts and projects to a full Mathieu Sylow.
A trivial two-core in that image would force its order to divide 1008,
contradicting its Sylow order. Its nontrivial core then supplies the
literal two-local normalizer excluded by the native M22 seven bound.

The source application is the original exterior point parabolic in
NaturalSource/Local/Normalizers/JankoNativeParabolic. No global placement
or choice of a native cover row is assumed here.
Source: Aschbacher–Smith, 12.5.3--4, printed pp.818--819.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.InvolutionCentralizers.First.ParabolicExclusion
open QuotientExtension

private theorem mathieu_kernel_card : Nat.card mathieuProjection.ker = 2 ^ 13 * 3 := by
  rw [mathieuProjection_ker, Nat.card_congr (subgroupOfEquivOfLe R_le_H).toEquiv]
  have hc := (Q.subgroupOf R).card_mul_index
  have hQ : Nat.card (Q.subgroupOf R) = 2 ^ 13 :=
    (Nat.card_congr (subgroupOfEquivOfLe Q_le_R).toEquiv).trans centralizer_twoCore_card
  have hi : (Q.subgroupOf R).index = 3 := by
    rw [index_eq_card, Nat.card_congr RQuotientEquivC3.toEquiv]
    simp
  rw [hQ, hi] at hc
  exact hc.symm

private theorem seven_image (D : Subgroup H) (h7 : 7 ∣ Nat.card D) :
    7 ∣ Nat.card (D.map mathieuProjection) := by
  let f := mathieuProjection.comp D.subtype
  have hk : Nat.card f.ker ∣ Nat.card mathieuProjection.ker := by
    let j : f.ker →* mathieuProjection.ker := {
      toFun x := ⟨x.val.val, x.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    exact card_dvd_of_injective j (fun x y he =>
      Subtype.ext (Subtype.ext (congrArg (fun z : mathieuProjection.ker => (z : H)) he)))
  have hcop : Nat.Coprime 7 (Nat.card f.ker) := by
    apply Nat.Coprime.coprime_dvd_right hk
    rw [mathieu_kernel_card]
    decide
  have hc := f.ker.card_mul_index
  rw [index_ker, show f.range = D.map mathieuProjection from by
    simp [f, MonoidHom.range_comp]] at hc
  exact hcop.dvd_of_dvd_mul_left (hc.symm ▸ h7)

/-- The full native Mathieu projection excludes the original small-core quotient. -/
theorem not_small_core_quotient_embedding
    {A : Type*} [Group A] [Finite A]
    (S : Sylow 2 centralizer) (J : Subgroup centralizer)
    (hSJ : (S : Subgroup centralizer) ≤ J) (h7 : 7 ∣ Nat.card J)
    (j : J →* A) (hj : Function.Injective j)
    (hA : Nat.card (A ⧸ pCore 2 A) = 1008) : False := by
  let D := J.subgroupOf H
  let d : D ≃* H.subgroupOf J := {
    toFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
    invFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  have hHindex : H.index = 2 := by
    rw [index_eq_card, Nat.card_congr centralizerQuotientEquivC2.toEquiv]
    simp
  have h7D : 7 ∣ Nat.card D := by
    have hidx : (H.subgroupOf J).index ∣ 2 := by
      change H.relIndex J ∣ 2
      exact hHindex ▸ H.relIndex_dvd_index_of_normal J
    have hc := (H.subgroupOf J).card_mul_index
    rw [← Nat.card_congr d.toEquiv] at hc
    rcases (Nat.Prime.dvd_mul (by decide : Nat.Prime 7)).mp (hc.symm ▸ h7) with hh | hh
    · exact hh
    · have bad := hh.trans hidx
      norm_num at bad
  obtain ⟨T, hT⟩ := S.exists_subgroupOf_eq_of_normal H
  have hTD : (T : Subgroup H) ≤ D := by
    rw [hT]
    exact comap_mono hSJ
  let P := T.mapSurjective mathieuProjection_surjective
  let X := D.map mathieuProjection
  have hPX : (P : Subgroup Sporadic.Mathieu.M22) ≤ X := map_mono hTD
  let jD : D →* A := j.comp ((H.subgroupOf J).subtype.comp d.toMonoidHom)
  have hjD : Function.Injective jD := by
    intro x y he
    apply d.injective
    apply Subtype.ext
    exact hj he
  have hcore : pCore 2 X ≠ ⊥ := by
    intro hz
    have hd := MonoidHom.card_corefree_quotient_dvd_of_embedding jD hjD
      (mathieuProjection.subgroupMap D) (mathieuProjection.subgroupMap_surjective D) hz
    rw [hA] at hd
    have h32 : 32 ∣ Nat.card P := P.pow_dvd_card_of_pow_dvd_card (n := 5)
      (by rw [Sporadic.Mathieu.m22_order]; decide)
    have bad := (h32.trans (card_dvd_of_le hPX)).trans hd
    norm_num at bad
  have hXN : X ≤ normalizer (((pCore 2 X).map X.subtype) : Set Sporadic.Mathieu.M22) :=
    X.le_normalizer.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  have hloc : IsTwoLocal (normalizer (((pCore 2 X).map X.subtype) : Set Sporadic.Mathieu.M22)) := by
    refine ⟨((pCore 2 X).map X.subtype), ?_, pCore_isPGroup.map X.subtype, rfl⟩
    intro he
    exact hcore ((map_eq_bot_iff_of_injective _ X.subtype_injective).mp he)
  exact Sporadic.Mathieu.M22TwoLocalOrders.not_seven_dvd_card_twoLocal P _ hloc
    (hPX.trans hXN) ((seven_image D h7D).trans (card_dvd_of_le hXN))

end Janko4.InvolutionCentralizers.First.ParabolicExclusion
