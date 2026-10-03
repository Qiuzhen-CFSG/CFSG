module

public import Theory.Representation.FourNineInversion
public import Theory.GroupAction.NineInvolutionLines
public import Stellmacher.SectionOne.CThreeCtwoSLTwo
public import Stellmacher.SectionOne.SL2PairProduct

/-!
# Splitting the faithful elementary nine-by-four complement

A normal elementary group W of order nine, complemented by an elementary
subgroup S of order four acting faithfully on W, gives the full group
SL2(2) × SL2(2). The complement and faithfulness conditions are explicit;
the separate odd-complement theorem proves them in the Section 1 setting.

The faithful four-on-nine action contains scalar inversion z. Choose a
different nonidentity involution a, and set b=a*z. Coprime a-action splits
W into its fixed and commutator lines, each of order three. The actors a
and b invert opposite lines and fix the other line. Each line joined to
its inverting involution is SL2(2). The two factors commute and generate
the full group; its order thirty-six makes their product map bijective.
The short private helper proves normalization and full commutator directly
from inversion of an order-three subgroup.

This is the group-identification step in Stellmacher (1.6), journal p.18.
Source: `refs/latex/stellmacher-n-group.tex`.
-/

open scoped IsMulCommutative Pointwise commutatorElement
namespace Stellmacher.SectionOne
universe u

private theorem normalizes_full_of_inverts_three
    {G : Type u} [Group G] [Finite G] (F : Subgroup G) (x : G)
    (hF : Nat.card F = 3) (hx2 : x ^ 2 = 1)
    (hinv : ∀ f ∈ F, x * f * x⁻¹ = f⁻¹) :
    Subgroup.zpowers x ≤ Subgroup.normalizer (F : Set G) ∧
      ⁅F, Subgroup.zpowers x⁆ = F := by
  have hxx : x * x = 1 := by simpa only [pow_two] using hx2
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_left hxx
  have hnorm : Subgroup.zpowers x ≤ Subgroup.normalizer (F : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro f
    constructor
    · intro hf
      rw [hinv f hf]
      exact F.inv_mem hf
    · intro hf
      have ht := F.inv_mem hf
      rw [← hinv (x * f * x⁻¹) hf, hxi] at ht
      have heq : x * (x * f * x) * x = f := by
        calc
          x * (x * f * x) * x = (x * x) * f * (x * x) := by group
          _ = f := by rw [hxx]; simp
      exact heq ▸ ht
  refine ⟨hnorm, le_antisymm
    (Subgroup.le_normalizer_iff_commutator_le_left.mp hnorm) ?_⟩
  intro f hf
  have hf3 : f ^ 3 = 1 := by
    have hpow : (⟨f, hf⟩ : F) ^ 3 = 1 := by rw [← hF]; exact pow_card_eq_one'
    exact congrArg Subtype.val hpow
  have hcomm : ⁅f⁻¹, x⁆ = f := by
    rw [commutatorElement_def, inv_inv]
    calc
      f⁻¹ * x * f * x⁻¹ = f⁻¹ * (x * f * x⁻¹) := by group
      _ = f⁻¹ * f⁻¹ := by rw [hinv f hf]
      _ = f := by
        have heq : f * (f * f) = 1 := by simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using hf3
        have ht := eq_inv_of_mul_eq_one_left heq
        simpa only [mul_inv_rev] using ht.symm
  rw [← hcomm]
  exact Subgroup.commutator_mem_commutator (F.inv_mem hf) (Subgroup.mem_zpowers x)

public theorem mulEquiv_sl2Two_prod_of_elementary_nine_complement_four
    {G : Type u} [Group G] [Finite G]
    (W S : Subgroup G) [W.Normal]
    [IsElementaryAbelian 3 W] [IsElementaryAbelian 2 S]
    (hW : Nat.card W = 9) (hS : Nat.card S = 4)
    (hcomp : W.IsComplement' S)
    (hfaith : S ⊓ Subgroup.centralizer (W : Set G) = ⊥) :
    Nonempty (G ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) ×
      Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) := by
  classical
  have hfaithAct : fixingSubgroup S (Set.univ : Set W) = ⊥ := by
    apply le_antisymm _ bot_le
    intro s hs
    apply Subtype.ext
    apply hfaith.le
    refine ⟨s.property, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro w hw
    have hsw := congrArg Subtype.val
      ((mem_fixingSubgroup_iff (M := S) (s := (Set.univ : Set W))).mp hs ⟨w, hw⟩ trivial)
    change (s : G) * w * (s : G)⁻¹ = w at hsw
    exact (mul_inv_eq_iff_eq_mul.mp hsw).symm
  have hactfaith (x y : S) (hxy : ∀ w : W, x • w = y • w) : x = y := by
    have hfix : y⁻¹ * x ∈ fixingSubgroup S (Set.univ : Set W) := by
      rw [mem_fixingSubgroup_iff]
      intro w _
      rw [mul_smul, hxy, inv_smul_smul]
    exact (inv_mul_eq_one.mp (hfaithAct.le hfix)).symm
  obtain ⟨z, hz1, hzinv⟩ := Representation.exists_inversion_of_elementary_card_four_card_nine
    hS hW hfaithAct
  have hSthree : 3 ≤ ENat.card S := by
    rw [ENat.card_eq_coe_natCard, hS]
    decide
  obtain ⟨a, ha1, haz⟩ := ENat.exists_ne_ne_of_three_le hSthree 1 z
  have hsq (x : S) : x ^ 2 = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 S) x
  have hane : ¬ ∀ w : W, a • w = w := by
    intro ha
    exact ha1 (hactfaith a 1 (by simpa using ha))
  have haninv : ¬ ∀ w : W, a • w = w⁻¹ := by
    intro ha
    exact haz (hactfaith a z (fun w => (ha w).trans (hzinv w).symm))
  obtain ⟨hCcard, hDcard, hainv⟩ := involution_fixed_commutator_card_three
    a (hsq a) hW hane haninv
  let P : Subgroup S := Subgroup.zpowers a
  let C : Subgroup W := FixedPoints.subgroup P W
  let D : Subgroup W := commutatorAction P W
  let b : S := a * z
  have hb1 : b ≠ 1 := by
    intro hb
    have hazinv : a = z⁻¹ := mul_eq_one_iff_eq_inv.mp hb
    have hzinvself : z⁻¹ = z := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hsq z)
    exact haz (hazinv.trans hzinvself)
  have hab : a ≠ b := by
    intro hab
    have hz : z = 1 := mul_left_cancel (show a * z = a * 1 by simpa [b] using hab.symm)
    exact hz1 hz
  have hafix (w : W) (hw : w ∈ C) : a • w = w := hw ⟨a, Subgroup.mem_zpowers a⟩
  have hbinv (w : W) (hw : w ∈ C) : b • w = w⁻¹ := by
    change (a * z) • w = _
    rw [mul_smul, hzinv, smul_inv', hafix w hw]
  have hbfix (w : W) (hw : w ∈ D) : b • w = w := by
    change (a * z) • w = _
    rw [mul_smul, hzinv, smul_inv', hainv w hw, inv_inv]
  let F₁ : Subgroup G := D.map W.subtype
  let F₂ : Subgroup G := C.map W.subtype
  let B₁ : Subgroup G := Subgroup.zpowers (a : G)
  let B₂ : Subgroup G := Subgroup.zpowers (b : G)
  have hF₁card : Nat.card F₁ = 3 :=
    (Subgroup.card_map_of_injective W.subtype_injective).trans hDcard
  have hF₂card : Nat.card F₂ = 3 :=
    (Subgroup.card_map_of_injective W.subtype_injective).trans hCcard
  have hBcard (x : S) (hx : x ≠ 1) : Nat.card (Subgroup.zpowers (x : G)) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (congrArg Subtype.val (hsq x)) (fun heq => hx (Subtype.ext heq))
  have hB₁card : Nat.card B₁ = 2 := hBcard a ha1
  have hB₂card : Nat.card B₂ = 2 := hBcard b hb1
  have hF₁W : F₁ ≤ W := Subgroup.map_subtype_le D
  have hF₂W : F₂ ≤ W := Subgroup.map_subtype_le C
  have hB₁S : B₁ ≤ S := Subgroup.zpowers_le.mpr a.property
  have hB₂S : B₂ ≤ S := Subgroup.zpowers_le.mpr b.property
  have hFjoin : F₁ ⊔ F₂ = W := by
    have hPcard : Nat.card P = 2 := by rw [Nat.card_zpowers, orderOf_eq_prime (hsq a) ha1]
    have hcop : Nat.Coprime (Nat.card P) (Nat.card W) := by rw [hPcard, hW]; decide
    have hc := isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := W) (A := P)
      (Group.isSolvable_of_comm fun x y => IsMulCommutative.is_comm.comm x y) hcop inferInstance
    change D.map W.subtype ⊔ C.map W.subtype = W
    rw [← Subgroup.map_sup, sup_comm, hc.sup_eq_top]
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hBjoin : B₁ ⊔ B₂ = S := by
    apply Subgroup.eq_of_le_of_card_ge (sup_le hB₁S hB₂S)
    have hne : B₁ ≠ B₂ := by
      intro heq
      have hbmem : (b : G) ∈ B₁ := heq ▸ Subgroup.mem_zpowers (b : G)
      have hba : b = a := by
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hbmem
        have hoa : orderOf (a : G) = 2 := orderOf_eq_prime
          (congrArg Subtype.val (hsq a)) (fun heq => ha1 (Subtype.ext heq))
        have hred := zpow_mod_orderOf (a : G) n
        rw [hoa] at hred
        rcases Int.emod_two_eq_zero_or_one n with h0 | h1
        · have hb0 : b = 1 := Subtype.ext (by simpa [h0] using hn.symm.trans hred.symm)
          exact (hb1 hb0).elim
        · exact Subtype.ext (by simpa [h1] using hn.symm.trans hred.symm)
      exact hab hba.symm
    have hlt : B₁ < B₁ ⊔ B₂ := lt_of_le_of_ne le_sup_left (by
      intro heq
      exact hne (Subgroup.eq_of_le_of_card_ge (le_sup_right.trans heq.ge) (by omega)).symm)
    have hc : Nat.card B₁ < Nat.card (B₁ ⊔ B₂ : Subgroup G) := by
      have hle := Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hlt.le)
      by_contra hnot
      exact hlt.ne (Subgroup.eq_of_le_of_card_ge hlt.le (by omega))
    have hd := Subgroup.card_dvd_of_le (sup_le hB₁S hB₂S)
    rw [hB₁card] at hc
    rw [hS] at hd ⊢
    obtain ⟨k, hk, heq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show Nat.card (B₁ ⊔ B₂ : Subgroup G) ∣ 2 ^ 2 by exact hd)
    interval_cases k
    · change Nat.card (B₁ ⊔ B₂ : Subgroup G) = 1 at heq
      omega
    · change Nat.card (B₁ ⊔ B₂ : Subgroup G) = 2 at heq
      omega
    · change Nat.card (B₁ ⊔ B₂ : Subgroup G) = 4 at heq
      omega
  have hF₁inv : ∀ f ∈ F₁, (a : G) * f * (a : G)⁻¹ = f⁻¹ := by
    rintro f ⟨w, hw, rfl⟩
    exact congrArg Subtype.val (hainv w hw)
  have hF₂inv : ∀ f ∈ F₂, (b : G) * f * (b : G)⁻¹ = f⁻¹ := by
    rintro f ⟨w, hw, rfl⟩
    exact congrArg Subtype.val (hbinv w hw)
  obtain ⟨hB₁norm, hF₁full⟩ := normalizes_full_of_inverts_three F₁ (a : G)
    hF₁card (congrArg Subtype.val (hsq a)) hF₁inv
  obtain ⟨hB₂norm, hF₂full⟩ := normalizes_full_of_inverts_three F₂ (b : G)
    hF₂card (congrArg Subtype.val (hsq b)) hF₂inv
  let E₁ := F₁ ⊔ B₁
  let E₂ := F₂ ⊔ B₂
  have hE₁ : IsSL2Two E₁ := isSL2Two_sup_of_card_three_card_two_full_commutator
    F₁ B₁ hF₁card hB₁card hB₁norm hF₁full
  have hE₂ : IsSL2Two E₂ := isSL2Two_sup_of_card_three_card_two_full_commutator
    F₂ B₂ hF₂card hB₂card hB₂norm hF₂full
  have hFF : ⁅F₁, F₂⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro f hf
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact congrArg Subtype.val (mul_comm (⟨g, hF₂W hg⟩ : W) (⟨f, hF₁W hf⟩ : W))
  have hBB : ⁅B₁, B₂⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro f hf
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact congrArg Subtype.val (mul_comm (⟨g, hB₂S hg⟩ : S) (⟨f, hB₁S hf⟩ : S))
  have hB₁F₂ : ⁅B₁, F₂⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.zpowers_le,
      Subgroup.mem_centralizer_iff]
    rintro g ⟨w, hw, rfl⟩
    have heq := congrArg Subtype.val (hafix w hw)
    change (a : G) * (w : G) * (a : G)⁻¹ = w at heq
    exact (mul_inv_eq_iff_eq_mul.mp heq).symm
  have hB₂F₁ : ⁅B₂, F₁⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.zpowers_le,
      Subgroup.mem_centralizer_iff]
    rintro g ⟨w, hw, rfl⟩
    have heq := congrArg Subtype.val (hbfix w hw)
    change (b : G) * (w : G) * (b : G)⁻¹ = w at heq
    exact (mul_inv_eq_iff_eq_mul.mp heq).symm
  have hEcomm : ⁅E₁, E₂⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    have hcross (X Y : Subgroup G) (hh : ⁅X, Y⁆ = ⊥) :
        X ≤ Subgroup.centralizer (Y : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hh
    apply sup_le
    · apply Subgroup.le_centralizer_iff.mpr
      apply sup_le
      · exact Subgroup.le_centralizer_iff.mp (hcross F₁ F₂ hFF)
      · exact hcross B₂ F₁ hB₂F₁
    · apply Subgroup.le_centralizer_iff.mpr
      apply sup_le
      · exact Subgroup.le_centralizer_iff.mp (hcross B₁ F₂ hB₁F₂)
      · exact Subgroup.le_centralizer_iff.mp (hcross B₁ B₂ hBB)
  have hEjoin : E₁ ⊔ E₂ = ⊤ := by
    change (F₁ ⊔ B₁) ⊔ (F₂ ⊔ B₂) = ⊤
    rw [sup_sup_sup_comm, hFjoin, hBjoin]
    exact hcomp.sup_eq_top
  have hGcard : Nat.card G = 36 := by
    have hc := hcomp.card_mul_card
    rw [hW, hS] at hc
    exact hc.symm
  exact mulEquiv_sl2Two_prod_of_commuting_sup_top E₁ E₂ hE₁ hE₂ hEcomm hEjoin hGcard

end Stellmacher.SectionOne

