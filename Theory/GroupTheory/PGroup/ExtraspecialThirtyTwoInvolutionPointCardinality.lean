module

public import Theory.GroupTheory.PGroup.RankTwoExtraspecialThirtyTwo
public import Theory.GroupTheory.FrattiniInvolutionPoints
import Mathlib.Tactic

/-!
# Five involution points in the extraspecial group of order thirty-two

An extraspecial group of order 32 with no elementary abelian subgroup of order
8 is a central product of quaternion and dihedral groups of order 8. A product
of commuting factor elements has square one precisely when their squares are
both trivial or both nontrivial: the center has only one nonidentity element.
There are 24 such pairs in the explicit factors. The map from their direct
product to the Frattini quotient has fibers of size four, giving six cosets
with square-one representatives. Removing the identity leaves five points.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, printed p.389.
-/

open Subgroup

private theorem card_preimage_of_surjective
    {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) (s : Set H) :
    Nat.card (f ⁻¹' s) = Nat.card f.ker * Nat.card s := by
  let e := QuotientGroup.liftEquiv f.ker hf rfl
  have hs : Nat.card (e ⁻¹' s) = Nat.card s :=
    Nat.card_congr (e.toEquiv.subtypeEquiv (fun _ => Iff.rfl))
  calc
    Nat.card (f ⁻¹' s) = Nat.card (QuotientGroup.mk ⁻¹' (e ⁻¹' s)) := by
      congr 1
    _ = Nat.card f.ker * Nat.card (e ⁻¹' s) :=
      QuotientGroup.card_preimage_mk f.ker _
    _ = Nat.card f.ker * Nat.card s := by rw [hs]

private theorem square_product_iff
    {P : Type*} [Group P] [Finite P] [IsExtraspecial 2 P]
    (a b : P) (hc : Commute a b) :
    (a * b) ^ 2 = 1 ↔ (a ^ 2 = 1 ↔ b ^ 2 = 1) := by
  have hbi : (b ^ 2)⁻¹ = b ^ 2 := inv_eq_of_mul_eq_one_right (by
    rw [← pow_add]
    exact IsExtraspecial.pow_four_eq_one b)
  rw [hc.mul_pow, mul_eq_one_iff_eq_inv, hbi]
  constructor
  · intro h
    rw [h]
  · intro h
    by_cases ha : a ^ 2 = 1
    · exact ha.trans (h.mp ha).symm
    · have hb : b ^ 2 ≠ 1 := fun hb => ha (h.mpr hb)
      obtain ⟨z, _, hz⟩ := (Nat.card_eq_two_iff' (1 : center P)).mp
        (IsExtraspecial.center_order_p 2 P)
      exact congrArg Subtype.val
        ((hz ⟨a ^ 2, IsExtraspecial.square_mem_center a⟩
          (fun he => ha (congrArg Subtype.val he))).trans
        (hz ⟨b ^ 2, IsExtraspecial.square_mem_center b⟩
          (fun he => hb (congrArg Subtype.val he))).symm)

private theorem square_one_lift_iff
    {P : Type*} [Group P] [Finite P] [IsExtraspecial 2 P] (y : P) :
    (∃ x : P, x ^ 2 = 1 ∧
      QuotientGroup.mk' (frattini P) x = QuotientGroup.mk' (frattini P) y) ↔
        y ^ 2 = 1 := by
  constructor
  · rintro ⟨x, hx, he⟩
    obtain ⟨z, hz, rfl⟩ := (QuotientGroup.mk'_eq_mk' _).mp he
    have hzC : z ∈ center P := IsExtraspecial.frattini_eq_center_two (P := P) ▸ hz
    have hz2 : z ^ 2 = 1 := by
      have h := congrArg Subtype.val (pow_card_eq_one' (x := (⟨z, hzC⟩ : center P)))
      change z ^ Nat.card (center P) = 1 at h
      rwa [IsExtraspecial.center_order_p 2 P] at h
    have hc : Commute x z := mem_center_iff.mp hzC x
    rw [hc.mul_pow, hx, hz2, one_mul]
  · intro hy
    exact ⟨y, hy, rfl⟩

private theorem model_count :
    (Finset.univ.filter fun x : QuaternionGroup 2 × DihedralGroup 4 =>
      (x.1 ^ 2 = 1 ↔ x.2 ^ 2 = 1)).card = 24 := by decide +kernel

namespace IsExtraspecial

/-- The rank-two extraspecial group of order 32 has exactly five nonidentity
Frattini cosets with square-one representatives. -/
public theorem card_frattiniInvolutionPoints_of_card_thirty_two
    {P : Type*} [Group P] [Finite P] [IsExtraspecial 2 P]
    (hrank : ∀ E : Subgroup P, IsElementaryAbelian 2 E → Nat.card E < 8)
    (hP : Nat.card P = 32) : Nat.card (frattiniInvolutionPoints P) = 5 := by
  classical
  obtain ⟨U, V, ⟨eU⟩, ⟨eV⟩, hcomm, hgen, _⟩ :=
    IsExtraspecial.dihedral_quaternion_factors_of_card_thirty_two hrank hP
  let : U.Normal := normalizer_eq_top_iff.mp (top_unique (by
    rw [← hgen]
    exact sup_le U.le_normalizer (hcomm.trans (centralizer_le_normalizer _))))
  let u : QuaternionGroup 2 →* P := U.subtype.comp eU.symm.toMonoidHom
  let v : DihedralGroup 4 →* P := V.subtype.comp eV.symm.toMonoidHom
  have huv (a : QuaternionGroup 2) (b : DihedralGroup 4) : Commute (u a) (v b) :=
    hcomm (eV.symm b).property _ (eU.symm a).property
  let f : QuaternionGroup 2 × DihedralGroup 4 →* P := {
    toFun := fun x => u x.1 * v x.2
    map_one' := by simp
    map_mul' := by
      intro x y
      simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
      calc
        u x.1 * u y.1 * (v x.2 * v y.2) =
            u x.1 * (u y.1 * v x.2) * v y.2 := by simp only [mul_assoc]
        _ = u x.1 * (v x.2 * u y.1) * v y.2 := by rw [(huv y.1 x.2).eq]
        _ = (u x.1 * v x.2) * (u y.1 * v y.2) := by simp only [mul_assoc] }
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_normal_left.mp (hgen ▸ mem_top x)
    refine ⟨(eU ⟨a, ha⟩, eV ⟨b, hb⟩), ?_⟩
    change (eU.symm (eU ⟨a, ha⟩) : P) * (eV.symm (eV ⟨b, hb⟩) : P) = x
    simpa only [eU.symm_apply_apply, eV.symm_apply_apply] using hab
  let g := (QuotientGroup.mk' (frattini P)).comp f
  have hg : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp hf
  have hker : Nat.card g.ker = 4 := by
    have h := card_preimage_of_surjective g hg Set.univ
    simp only [Set.preimage_univ, Nat.card_coe_set_eq, Set.ncard_univ] at h
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := QuaternionGroup 2),
      QuaternionGroup.card, DihedralGroup.nat_card,
      IsExtraspecial.card_frattini_quotient_of_card_thirty_two hP] at h
    omega
  let S : Set (P ⧸ frattini P) :=
    {y | ∃ x : P, x ^ 2 = 1 ∧ QuotientGroup.mk' (frattini P) x = y}
  have hpre : g ⁻¹' S = {x | x.1 ^ 2 = 1 ↔ x.2 ^ 2 = 1} := by
    ext x
    change (∃ y : P, y ^ 2 = 1 ∧
      QuotientGroup.mk' (frattini P) y = QuotientGroup.mk' (frattini P) (f x)) ↔ _
    rw [square_one_lift_iff]
    change (u x.1 * v x.2) ^ 2 = 1 ↔ _
    rw [square_product_iff _ _ (huv _ _)]
    have hu : Function.Injective u := U.subtype_injective.comp eU.symm.injective
    have hv : Function.Injective v := V.subtype_injective.comp eV.symm.injective
    simp only [← map_pow, (map_eq_one_iff u hu), (map_eq_one_iff v hv), Set.mem_ofPred_eq]
  have hS : Nat.card S = 6 := by
    have h := card_preimage_of_surjective g hg S
    rw [hker, hpre, Nat.card_eq_fintype_card, Fintype.card_subtype] at h
    simp only [Set.mem_ofPred_eq] at h
    rw [model_count] at h
    omega
  have hset : S = insert 1 (frattiniInvolutionPoints P) := by
    ext y
    change (∃ x : P, x ^ 2 = 1 ∧ QuotientGroup.mk' (frattini P) x = y) ↔ _
    simp only [Set.mem_insert_iff, mem_frattiniInvolutionPoints]
    by_cases hy : y = 1
    · subst y
      simp only [true_or, iff_true]
      exact ⟨1, one_pow 2, map_one _⟩
    · simp only [ne_eq, hy, false_or, not_false_eq_true, true_and]
  have hnot : (1 : P ⧸ frattini P) ∉ frattiniInvolutionPoints P :=
    fun h => ((mem_frattiniInvolutionPoints _).mp h).1 rfl
  rw [hset] at hS
  change (insert 1 (frattiniInvolutionPoints P)).ncard = 6 at hS
  rw [Set.ncard_insert_of_notMem hnot] at hS
  change (frattiniInvolutionPoints P).ncard = 5
  omega

end IsExtraspecial
