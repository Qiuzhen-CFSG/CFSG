module
public import Theory.GroupAction.AutomorphismFixedCardinality
public import Theory.GroupAction.KleinFourAbelianCardinality
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Tactic.Ring

/-!
# The Brauer--Wielandt order relation for odd-order p-groups

Two commuting involutive automorphisms of a finite odd-order p-group satisfy
`|G| |C_G(a,b)|² = |C_G(a)| |C_G(b)| |C_G(ab)|`. Their images may be trivial;
no faithfulness or distinctness assumption is required. This is the p-group
step of the Brauer--Wielandt relation stated in Gorenstein--Walter, Section 2,
Lemma 3, used in the Alperin--Brauer--Gorenstein development.

Induct on the order of the p-group. Its nontrivial center makes the central
quotient strictly smaller. Automorphisms restrict to the center and descend
to the quotient, preserving their commutation and involutivity. Apply the
abelian relation on the center and the induction hypothesis on the quotient.
The fixed and common-fixed cardinality formulas across the quotient map,
proved from unique fixed/inverted factorization, multiply those two identities
to give the formula on the original group.
-/

namespace Theory.GroupAction
open MulAut
private def centerAut {G : Type*} [Group G] (a : MulAut G) : MulAut (Subgroup.center G) :=
  (a.subgroupMap (Subgroup.center G)).trans
    (MulEquiv.subgroupCongr (Subgroup.characteristic_iff_map_eq.mp inferInstance a))
private theorem centerAut_apply {G : Type*} [Group G] (a : MulAut G)
    (x : Subgroup.center G) : (centerAut a x : G) = a x := rfl

private def quotientAut {G : Type*} [Group G] (a : MulAut G)
    (ha : Function.Involutive a) : MulAut (G ⧸ Subgroup.center G) := by
  let f := QuotientGroup.map (Subgroup.center G) (Subgroup.center G) a.toMonoidHom
    (by
      intro x hx
      change a x ∈ Subgroup.center G
      have hm : (Subgroup.center G).map a.toMonoidHom = Subgroup.center G :=
        Subgroup.characteristic_iff_map_eq.mp inferInstance a
      rw [← hm]
      exact ⟨x, hx, rfl⟩)
  have hf : Function.Involutive f := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x => change (QuotientGroup.mk' _) (a (a x)) = _; rw [ha]; rfl
  exact { f with invFun := f, left_inv := hf, right_inv := hf }
private theorem quotientAut_apply {G : Type*} [Group G] (a : MulAut G)
    (ha : Function.Involutive a) (x : G) :
    quotientAut a ha (QuotientGroup.mk' (Subgroup.center G) x) =
      QuotientGroup.mk' (Subgroup.center G) (a x) := rfl

private theorem card_restrict_fixed {G : Type*} [Group G] (K : Subgroup G)
    (a : MulAut G) (c : MulAut K) (h : ∀ x : K, (c x : G) = a x) :
    Nat.card (fixedSubgroup c) = Nat.card ↥(K ⊓ fixedSubgroup a) := by
  apply Nat.card_congr
  exact { toFun := fun x => ⟨x.1.1, x.1.2, by
            apply (mem_fixedSubgroup _ _).mpr
            rw [← h]
            exact congrArg Subtype.val ((mem_fixedSubgroup c x.1).mp x.2)⟩
          invFun := fun x => ⟨⟨x.1, x.2.1⟩, by
            apply (mem_fixedSubgroup _ _).mpr
            apply Subtype.ext
            rw [h]
            exact (mem_fixedSubgroup a x.1).mp x.2.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }

private theorem card_restrict_common_fixed {G : Type*} [Group G] (K : Subgroup G)
    (a b : MulAut G) (c d : MulAut K)
    (hac : ∀ x : K, (c x : G) = a x) (hbd : ∀ x : K, (d x : G) = b x) :
    Nat.card ↥(fixedSubgroup c ⊓ fixedSubgroup d) =
      Nat.card ↥(K ⊓ (fixedSubgroup a ⊓ fixedSubgroup b)) := by
  apply Nat.card_congr
  exact { toFun := fun x => ⟨x.1.1, x.1.2, by
            apply (mem_fixedSubgroup _ _).mpr
            rw [← hac]
            exact congrArg Subtype.val ((mem_fixedSubgroup c x.1).mp x.2.1), by
            apply (mem_fixedSubgroup _ _).mpr
            rw [← hbd]
            exact congrArg Subtype.val ((mem_fixedSubgroup d x.1).mp x.2.2)⟩
          invFun := fun x => ⟨⟨x.1, x.2.1⟩, by
            apply (mem_fixedSubgroup _ _).mpr
            apply Subtype.ext
            rw [hac]
            exact (mem_fixedSubgroup a x.1).mp x.2.2.1, by
            apply (mem_fixedSubgroup _ _).mpr
            apply Subtype.ext
            rw [hbd]
            exact (mem_fixedSubgroup b x.1).mp x.2.2.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
private theorem centerAut_involutive {G : Type*} [Group G] (a : MulAut G)
    (ha : Function.Involutive a) : Function.Involutive (centerAut a) := by
  intro x
  apply Subtype.ext
  exact ha x
private theorem centerAut_commute {G : Type*} [Group G] (a b : MulAut G)
    (hab : Commute a b) : Commute (centerAut a) (centerAut b) := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  exact congrArg (fun e : MulAut G => e x) hab.eq
private theorem quotientAut_involutive {G : Type*} [Group G] (a : MulAut G)
    (ha : Function.Involutive a) : Function.Involutive (quotientAut a ha) := by
  intro x
  induction x using QuotientGroup.induction_on with
  | H x =>
    change quotientAut a ha (quotientAut a ha (QuotientGroup.mk' _ x)) = QuotientGroup.mk' _ x
    rw [quotientAut_apply, quotientAut_apply, ha]
private theorem quotientAut_commute {G : Type*} [Group G] (a b : MulAut G)
    (ha : Function.Involutive a) (hb : Function.Involutive b) (hab : Commute a b) :
    Commute (quotientAut a ha) (quotientAut b hb) := by
  apply MulEquiv.ext
  intro x
  induction x using QuotientGroup.induction_on with
  | H x =>
    change quotientAut a ha (quotientAut b hb (QuotientGroup.mk' _ x)) =
      quotientAut b hb (quotientAut a ha (QuotientGroup.mk' _ x))
    simp only [quotientAut_apply]
    exact congrArg (QuotientGroup.mk' _) (congrArg (fun e : MulAut G => e x) hab.eq)
private theorem product_involutive {G : Type*} [Group G] (a b : MulAut G)
    (ha : Function.Involutive a) (hb : Function.Involutive b) (hab : Commute a b) :
    Function.Involutive (a*b) := by
  intro x
  change a (b (a (b x))) = x
  have hc (z : G) : a (b z) = b (a z) := congrArg (fun e : MulAut G => e z) hab.eq
  rw [← hc, ha, hb]
/-- The Brauer--Wielandt fixed-subgroup order formula for an odd-order finite
p-group with two commuting involutive automorphisms. -/
public theorem brauerWielandt_fixedSubgroup_card_of_isPGroup {p : ℕ} [Fact p.Prime] {G : Type*} [hG : Group G] [Finite G]
    (hP : IsPGroup p G) (hodd : Odd (Nat.card G)) (a b : MulAut G)
    (ha : Function.Involutive a) (hb : Function.Involutive b) (hab : Commute a b) :
    Nat.card G * Nat.card ↥(fixedSubgroup a ⊓ fixedSubgroup b)^2 =
      Nat.card (fixedSubgroup a) * Nat.card (fixedSubgroup b) *
        Nat.card (fixedSubgroup (a*b)) := by
  induction G using Finite.induction_subsingleton_or_nontrivial generalizing hG with
  | hbase => simp only [Nat.card_unique, one_pow, one_mul]
  | hstep G ih =>
    have hQlt : Nat.card (G ⧸ Subgroup.center G) < Nat.card G := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center G)]
      apply lt_mul_of_one_lt_right Nat.card_pos
      exact (Subgroup.one_lt_card_iff_ne_bot _).mpr (ne_of_gt hP.bot_lt_center)
    have hoddQ : Odd (Nat.card (G ⧸ Subgroup.center G)) :=
      Odd.of_dvd_nat hodd (Subgroup.card_quotient_dvd_card (Subgroup.center G))
    have hoddZ : Odd (Nat.card (Subgroup.center G)) :=
      Odd.of_dvd_nat hodd (Subgroup.card_subgroup_dvd_card (Subgroup.center G))
    have hQ := ih _ hQlt (hP.to_quotient (Subgroup.center G)) hoddQ
      (quotientAut a ha) (quotientAut b hb)
      (quotientAut_involutive a ha) (quotientAut_involutive b hb)
      (quotientAut_commute a b ha hb hab)
    have hZ := brauerWielandt_fixedSubgroup_card_of_isMulCommutative hoddZ
      (centerAut a) (centerAut b) (centerAut_involutive a ha)
      (centerAut_involutive b hb) (centerAut_commute a b hab)
    let f := QuotientGroup.mk' (Subgroup.center G)
    have hac (x : G) : f (a x) = quotientAut a ha (f x) :=
      (quotientAut_apply a ha x).symm
    have hbd (x : G) : f (b x) = quotientAut b hb (f x) :=
      (quotientAut_apply b hb x).symm
    have hf : Function.Surjective f := QuotientGroup.mk'_surjective _
    have hker : f.ker = Subgroup.center G := QuotientGroup.ker_mk' _
    have hA := fixedSubgroup_card_eq_quotient_mul_kernel hodd hoddQ a (quotientAut a ha)
      ha (quotientAut_involutive a ha) f hf hac
    rw [hker, ← card_restrict_fixed _ a (centerAut a) (centerAut_apply a)] at hA
    have hB := fixedSubgroup_card_eq_quotient_mul_kernel hodd hoddQ b (quotientAut b hb)
      hb (quotientAut_involutive b hb) f hf hbd
    rw [hker, ← card_restrict_fixed _ b (centerAut b) (centerAut_apply b)] at hB
    have hAB := fixedSubgroup_card_eq_quotient_mul_kernel hodd hoddQ (a*b)
      (quotientAut a ha * quotientAut b hb) (product_involutive a b ha hb hab)
      (product_involutive _ _ (quotientAut_involutive a ha) (quotientAut_involutive b hb)
        (quotientAut_commute a b ha hb hab)) f hf (fun x => by
          change f (a (b x)) = quotientAut a ha (quotientAut b hb (f x))
          rw [hac, hbd])
    rw [hker, ← card_restrict_fixed _ (a*b) (centerAut a * centerAut b)
      (fun _ => rfl)] at hAB
    have hF := common_fixedSubgroup_card_eq_quotient_mul_kernel hodd hoddQ a b
      (quotientAut a ha) (quotientAut b hb) ha hb
      (quotientAut_involutive a ha) (quotientAut_involutive b hb) hab f hf hac hbd
    rw [hker, ← card_restrict_common_fixed _ a b (centerAut a) (centerAut b)
      (centerAut_apply a) (centerAut_apply b)] at hF
    calc
      Nat.card G * Nat.card ↥(fixedSubgroup a ⊓ fixedSubgroup b)^2 =
          (Nat.card (G ⧸ Subgroup.center G) *
            Nat.card ↥(fixedSubgroup (quotientAut a ha) ⊓ fixedSubgroup (quotientAut b hb))^2) *
          (Nat.card (Subgroup.center G) *
            Nat.card ↥(fixedSubgroup (centerAut a) ⊓ fixedSubgroup (centerAut b))^2) := by
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center G), hF]
        ring
      _ = Nat.card (fixedSubgroup a) * Nat.card (fixedSubgroup b) *
          Nat.card (fixedSubgroup (a*b)) := by
        rw [hQ, hZ, hA, hB, hAB]
        ring
end Theory.GroupAction
