module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.FiveCore.Source.QuaternionLocal
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Commutators.NaturalHead
public import Theory.GroupAction.SubgroupConjugation


/-!
# The actual five-fixed sections in the Ru₂ local setup

An order-five permutation fixes no nonzero vector in either marked natural
section U/Z or Q/HC. Hence C_Q(B₅) lies in HC and meets U in Z. The product
formula bounds its order by eight. Counting fixed points on Q modulo five
and using the two-group order then forces order eight, giving
C_Q(B₅)U = HC. Every subgroup and quotient map is the original source one.
No quaternion recognition or five-centralizer conclusion is assumed.

Source: Aschbacher–Smith J.2.7(5), printed p.435, using J.2.2(2–3).
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ
open Subgroup Representation
open Representation.SL2FourNatural

namespace FiveNatural
private theorem stabilizer_standard_square (g : SL) (hg : action g ![1, 0] = ![1, 0]) :
    g ^ 2 = 1 := by
  have h00 : g.val 0 0 = 1 := by
    simpa [action_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hg 0
  have h10 : g.val 1 0 = 0 := by
    simpa [action_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hg 1
  have h11 : g.val 1 1 = 1 := by
    have hd : Matrix.det g.val = 1 := g.property
    rw [Matrix.det_fin_two, h00, h10] at hd
    simpa using hd
  apply Subtype.ext
  simp only [pow_two, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h00, h10, h11,
      CharTwo.add_self_eq_zero]

private theorem fixed_square (g : SL) {v : V} (hv : v ≠ 0) (hg : action g v = v) :
    g ^ 2 = 1 := by
  obtain ⟨a, ha⟩ := exists_first_column v hv
  have hfix : action (a⁻¹ * g * a) ![1, 0] = ![1, 0] := by
    simp only [map_mul, LinearEquiv.mul_apply, ha, hg]
    rw [← ha]
    simp
  have hh := stabilizer_standard_square (a⁻¹ * g * a) hfix
  have he : (a⁻¹ * g * a) ^ 2 = a⁻¹ * g ^ 2 * a := by simp only [pow_two]; group
  rw [he] at hh
  have := congrArg (fun x : SL => a * x * a⁻¹) hh
  simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left, mul_one,
    mul_inv_cancel] using this

private theorem five_fixed (g : SL) (h5 : g ^ 5 = 1) (hne : g ≠ 1)
    {v : V} (hv : action g v = v) : v = 0 := by
  by_contra hn
  have h2 := fixed_square g hn hv
  apply hne
  have hd : orderOf g ∣ Nat.gcd 2 5 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h5)
  have ho : orderOf g = 1 := Nat.eq_one_of_dvd_one hd
  exact orderOf_eq_one_iff.mp ho
end FiveNatural

/-- An order-five permutation has no nonzero fixed vector in the marked natural action. -/
theorem L2FourAction.five_fixed_eq_zero (r : L2FourAction) {g : S5}
    (hg : orderOf g = 5) {v : FourSpace} (hv : r.action g v = v) : v = 0 := by
  have hg5 : g ^ 5 = 1 := by simpa only [hg] using pow_orderOf_eq_one g
  have hsign : Equiv.Perm.sign g = 1 := by
    have hs : (Equiv.Perm.sign g) ^ 5 = 1 := by
      rw [← map_pow, hg5, map_one]
    have hp : (Equiv.Perm.sign g) ^ 5 = Equiv.Perm.sign g := by
      calc
        _ = (Equiv.Perm.sign g)^2 * (Equiv.Perm.sign g)^2 * Equiv.Perm.sign g := by group
        _ = _ := by simp only [Int.units_pow_two, one_mul]
    exact hp.symm.trans hs
  let a : SL2FourNatural.SL := r.marking.symm ⟨g, Equiv.Perm.mem_alternatingGroup.mpr hsign⟩
  have ha : (r.marking a : S5) = g := congrArg Subtype.val (r.marking.apply_symm_apply _)
  have ha5 : a ^ 5 = 1 := by
    apply r.marking.injective
    apply Subtype.ext
    simpa only [map_pow, Subgroup.coe_pow, ha, map_one, Subgroup.coe_one] using hg5
  have hane : a ≠ 1 := by
    intro he
    have hg1 : g = 1 := by simpa only [he, map_one, Subgroup.coe_one] using ha.symm
    rw [hg1, orderOf_one] at hg
    omega
  apply FiveNatural.five_fixed a ha5 hane
  rw [← r.restriction, ha]
  exact hv

variable {G : Type*} [Group G]
/-- Fixed elements lift into the literal kernel of a marked natural section. -/
theorem L2FourAction.centralizer_le_kernel_of_five_image {H A C B : Subgroup G}
    (r : L2FourAction) (q : H →* S5)
    (s : BinaryConjugationSection H A C (r.action.comp q))
    (hBH : B ≤ H) (b : B) (hb : orderOf (q ⟨b, hBH b.property⟩) = 5) :
    A ⊓ centralizer (B : Set G) ≤ C := by
  intro a ha
  apply (s.coordinates_eq_one_iff ⟨a, ha.1⟩).mp
  apply Multiplicative.toAdd.injective
  change (s.coordinates ⟨a, ha.1⟩).toAdd = 0
  apply r.five_fixed_eq_zero hb
  have he := s.equivariant ⟨b, hBH b.property⟩ ⟨a, ha.1⟩
  have hc : (b : G) * a * (b : G)⁻¹ = a := by
    rw [ha.2 b b.property, mul_inv_cancel_right]
  have hx : (⟨(b : G) * a * (b : G)⁻¹,
      (mem_normalizer_iff.mp (s.normalized (hBH b.property)) a).mp ha.1⟩ : A) =
      ⟨a, ha.1⟩ := Subtype.ext hc
  rw [hx] at he
  exact he.symm
end CFSG.Quasithin.ChapterJ

namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
open Subgroup
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
private instance primeFive : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem exists_five_image (B5 : Sylow 5 d.toTypeRuSetup.H) :
    ∃ b : B5Image B5,
      orderOf (d.ru2.quotientMap ⟨b, map_subtype_le _ b.property⟩) = 5 := by
  have hc : Nat.card B5 = 5 := by
    rw [B5.card_eq_multiplicity, d.ru2.card_H d.card_Z]
    decide +kernel
  let : IsCyclic B5 := isCyclic_of_prime_card hc
  obtain ⟨b,hb⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp (inferInstance : IsCyclic B5)
  have hi := d.toTypeRuSetup.quotientMap_injective_on_odd
    (B5 : Subgroup d.toTypeRuSetup.H) (by rw [hc]; decide)
  refine ⟨⟨b,mem_map_of_mem d.toTypeRuSetup.H.subtype b.property⟩, ?_⟩
  exact (orderOf_injective (d.ru2.quotientMap.comp (B5 : Subgroup _).subtype) hi b).trans
    (hb.trans hc)

theorem five_centralizer_le_HC (B5 : Sylow 5 d.toTypeRuSetup.H) :
    CQ B5 ≤ d.toTypeRuSetup.HC := by
  obtain ⟨b,hb⟩ := exists_five_image B5
  exact d.fusionNaturalHead.action.centralizer_le_kernel_of_five_image
    d.ru2.quotientMap d.fusionNaturalHead.sectionData (map_subtype_le _) b hb

theorem five_centralizer_inf_U (B5 : Sylow 5 d.toTypeRuSetup.H) :
    CQ B5 ⊓ d.toTypeRuSetup.U = d.toTypeRuSetup.Z := by
  obtain ⟨b,hb⟩ := exists_five_image B5
  have hc := d.ru2.naturalAction.centralizer_le_kernel_of_five_image
    d.ru2.quotientMap d.ru2.natural (map_subtype_le _) b hb
  apply le_antisymm
  · exact fun x hx => hc ⟨hx.2,hx.1.2⟩
  · refine le_inf (le_inf (d.ru2.natural.kernel_le.trans d.ru2.six.kernel_le) ?_)
      d.ru2.natural.kernel_le
    intro z hz b hb
    exact (((show B5Image B5 ≤ d.toTypeRuSetup.H from map_subtype_le _) hb) z hz).symm

theorem five_centralizer_card (B5 : Sylow 5 d.toTypeRuSetup.H) : Nat.card (CQ B5) = 8 := by
  let D := d.toTypeRuSetup
  have hle := five_centralizer_le_HC B5
  have hprod : CQ B5 ⊔ D.U ≤ D.HC := sup_le hle d.U_le_HC
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes (CQ B5) D.U
    ((le_centralizer_iff.mp (hle.trans inf_le_right)).trans (Subgroup.centralizer_le_normalizer _))
  rw [d.ru2.card_U d.card_Z, five_centralizer_inf_U, d.card_Z] at hc
  have hbound : Nat.card (CQ B5) ≤ 8 := by
    have hh := card_le_of_le hprod
    rw [d.card_HC] at hh
    omega
  let : MulDistribMulAction (B5Image B5) D.Q := conjMulDistribMulActionOfLeNormalizer
    (B5Image B5) D.Q ((map_subtype_le _).trans d.ru2.six.normalized)
  let X := FixedPoints.subgroup (B5Image B5) D.Q
  let e : X ≃ CQ B5 := {
    toFun x := ⟨x.val, x.val.property, by
      intro b hb
      have hh := congrArg Subtype.val (x.property (⟨b,hb⟩ : B5Image B5))
      change b * (x.val : G) * b⁻¹ = x.val at hh
      exact mul_inv_eq_iff_eq_mul.mp hh⟩
    invFun x := ⟨⟨x,x.property.1⟩, by
      intro b
      apply Subtype.ext
      change (b:G) * (x:G) * (b:G)⁻¹ = x
      rw [x.property.2 b b.property, mul_inv_cancel_right]⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have hp : IsPGroup 5 (B5Image B5) := B5.isPGroup'.map D.H.subtype
  have hm := hp.card_modEq_card_fixedPoints D.Q
  change Nat.card D.Q % 5 = Nat.card X % 5 at hm
  rw [d.ru2.card_Q d.card_Z, Nat.card_congr e] at hm
  have hd : Nat.card (CQ B5) ∣ 128 := by
    rw [← d.card_HC]
    exact card_dvd_of_le hle
  have hmem := Nat.mem_divisors.mpr ⟨hd, by decide⟩
  have ht : (128 : ℕ).divisors = {1,2,4,8,16,32,64,128} := by decide
  rw [ht] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  omega

theorem five_centralizer_sup_U (B5 : Sylow 5 d.toTypeRuSetup.H) :
    CQ B5 ⊔ d.toTypeRuSetup.U = d.toTypeRuSetup.HC := by
  have hle := five_centralizer_le_HC B5
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes (CQ B5) d.toTypeRuSetup.U
    ((le_centralizer_iff.mp (hle.trans inf_le_right)).trans (Subgroup.centralizer_le_normalizer _))
  rw [five_centralizer_card, d.ru2.card_U d.card_Z, five_centralizer_inf_U, d.card_Z] at hc
  apply eq_of_le_of_card_ge (sup_le hle d.U_le_HC)
  rw [d.card_HC]
  omega

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
