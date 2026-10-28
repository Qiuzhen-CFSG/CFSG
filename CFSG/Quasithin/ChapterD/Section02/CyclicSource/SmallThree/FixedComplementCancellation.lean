module
public import CFSG.Quasithin.ChapterD.Section02.SmallSupportDecomposition

/-!
# Cancelling a canonical cubic on its support

The normalized-factor branch of Aschbacher--Smith D.2.25, printed p.190,
uses an order-three element whose action is confined to one canonical
four-element support and the common fixed complement. The centralizer of
the irreducible cubic on its four-element support has order three: it acts
freely on the three nonidentity points and contains the faithful cubic.
Consequently its action there can be cancelled by an element of that factor.

The corrected cubic fixes every canonical support and has precisely the
original displacement on the fixed complement. If that displacement has
four elements, the corrected cubic is itself canonical. It must therefore
fix the common fixed complement, a contradiction. This proves the marked
cancellation required by D.2.25 without choosing coordinates in GL₄(2).
The involution rank budget and construction of the residual cubic remain
with the source assembly, which supplies the explicit hypotheses below.
-/

open scoped IsMulCommutative
open Subgroup
namespace CFSG.Quasithin.ChapterD
variable {G V : Type*} [Group G] [Group V] [MulDistribMulAction G V]
  [Finite G] [Finite V] [IsElementaryAbelian 2 V] [FaithfulSMul G V]

/-- The centralizer of the canonical cubic acts on its four-element support
through that same cubic. -/
public theorem smallThree_exists_same_support_action
    {X : Subgroup G} (hX : X ∈ smallSupportFactors G V 1)
    (x : G) (hx : ∀ z ∈ X, Commute x z) :
    ∃ z ∈ X, ∀ v ∈ commutatorAction X V, z • v = x • v := by
  let U := commutatorAction X V
  let _ : IsInvariant X V U := commutatorAction_isInvariant
  let ρ := MulDistribMulAction.toMulAut X U
  let C : Subgroup (MulAut U) := centralizer (ρ.range : Set (MulAut U))
  have hirred (D : Subgroup U) (hD : IsInvariant X U D) : D = ⊥ ∨ D = ⊤ := by
    let _ := hD
    exact ActionSupport.invariant_eq_bot_or_top_of_small_binary_actor
      (Or.inl ⟨by simpa using hX.2.1, by simpa using hX.2.2⟩)
      (ActionSupport.fixed_eq_bot_on_coprime_support X
        (smallSupportFactor_coprime (Or.inl rfl) hX)) D
  have hC : Nat.card C ∣ 3 := by
    have hd := ActionSupport.card_dvd_card_sub_one_of_commuting_irreducible
      (A := X) (H := C) (W := U) (by
        intro a c v
        exact congrArg (fun f : MulAut U => f v)
          (Subgroup.mem_centralizer_iff.mp c.property (ρ a) ⟨a, rfl⟩)) hirred
    simpa [U, show Nat.card (commutatorAction X V) = 4 from by simpa using hX.2.2] using hd
  let _ : IsCyclic X := smallSupportFactor_isCyclic (Or.inl rfl) hX
  let _ : IsMulCommutative X := inferInstance
  let φ : X →* C := ρ.codRestrict C (by
    intro a
    apply mem_centralizer_iff.mpr
    rintro _ ⟨b, rfl⟩
    exact (map_mul ρ b a).symm.trans ((congrArg ρ (mul_comm b a)).trans (map_mul ρ a b)))
  have hφ : Function.Injective φ := by
    apply (MonoidHom.ker_eq_bot_iff φ).mp
    apply bot_unique
    intro a ha
    apply Subtype.ext
    apply smallSupportFactor_eq_one_of_fixes_support (Or.inl rfl) hX a
    intro v hv
    have he : ρ a = 1 := congrArg Subtype.val (show φ a = 1 from ha)
    exact congrArg Subtype.val (congrArg (fun f : MulAut U => f ⟨v, hv⟩) he)
  have hsur : Function.Surjective φ := by
    exact (hφ.bijective_of_nat_card_le (by
      calc Nat.card C ≤ 3 := Nat.le_of_dvd (by decide) hC
           _ = Nat.card X := by simpa using hX.2.1.symm)).2
  let T := zpowers x
  have hnorm : T ≤ normalizer (X : Set G) := by
    apply zpowers_le.mpr
    apply centralizer_le_normalizer
    exact mem_centralizer_iff.mpr (fun z hz => (hx z hz).symm.eq)
  let _ : IsInvariant T V U := commutatorAction_isInvariant_of_normalizing_actor T X hnorm
  let χ := MulDistribMulAction.toMulAut T U
  have hxC : χ ⟨x, mem_zpowers x⟩ ∈ C := by
    apply mem_centralizer_iff.mpr
    rintro _ ⟨a, rfl⟩
    ext v
    change (a : G) • (x • (v : V)) = x • ((a : G) • (v : V))
    rw [← mul_smul, ← mul_smul, (hx a a.property).eq]
  obtain ⟨z, hz⟩ := hsur ⟨χ ⟨x, mem_zpowers x⟩, hxC⟩
  refine ⟨z, z.property, fun v hv => ?_⟩
  exact congrArg Subtype.val
    (congrArg (fun f : C => (f : MulAut U) ⟨v, hv⟩) hz)

/-- Cancelling the selected factor leaves a cubic with exactly its original
support on the fixed complement. It would itself be a canonical factor and
therefore fix that complement, a contradiction. -/
public theorem smallThree_fixedComplement_cancellation
    {X : Subgroup G} (hX : X ∈ smallSupportFactors G V 1)
    (x : G) (hxF : x ∈ fittingSubgroup G) (hx3 : x ^ 3 = 1)
    (hxX : ∀ z ∈ X, Commute x z)
    (hxother : ∀ P ∈ smallSupportFactors G V 1, P ≠ X →
      ∀ v ∈ commutatorAction P V, x • v = v)
    (hsplit : FixedPoints.subgroup (smallSupportGroup G V 1) V ⊔
      commutatorAction (smallSupportGroup G V 1) V = ⊤)
    (hxcard : Nat.card (commutatorSubgroup (zpowers x) V
      (FixedPoints.subgroup (smallSupportGroup G V 1) V)) = 4) : False := by
  classical
  let Y := smallSupportGroup G V 1
  let W := FixedPoints.subgroup Y V
  let S := commutatorAction Y V
  obtain ⟨z, hz, hzx⟩ := smallThree_exists_same_support_action hX x hxX
  let a := z⁻¹ * x
  have hzY : z ∈ Y := (le_sSup hX) hz
  have hzW (v : V) (hv : v ∈ W) : z • v = v := hv ⟨z, hzY⟩
  have haz : Commute z⁻¹ x := (hxX z hz).symm.inv_left
  have haW (n : ℤ) (v : V) (hv : v ∈ W) : a ^ n • v = x ^ n • v := by
    dsimp [a]
    rw [haz.mul_zpow, haz.zpow_zpow n n, mul_smul]
    rw [smul_eq_self_of_mem_zpowers (show (z⁻¹) ^ n ∈ zpowers z from
      (zpowers z).zpow_mem ((zpowers z).inv_mem (mem_zpowers z)) n) (hzW v hv)]
  have haS : ∀ v ∈ S, a • v = v := by
    have hle : S ≤ FixedPoints.subgroup (zpowers a) V := by
      rw [show S = ⨆ P : smallSupportFactors G V 1, commutatorAction P.val V from
        smallSupportGroup_support_eq_iSup 1]
      refine iSup_le fun P v hv b => ?_
      apply smul_eq_self_of_mem_zpowers b.property
      change (z⁻¹ * x) • v = v
      rw [mul_smul]
      by_cases he : P.val = X
      · rw [← hzx v (he ▸ hv), inv_smul_smul]
      · rw [hxother P.val P.property he v hv]
        have hzfix := smallSupportFactors_cross_fixed (Or.inl rfl) hX P.property (Ne.symm he) hv
        exact hzfix ⟨z⁻¹, X.inv_mem hz⟩
    intro v hv
    exact hle hv ⟨a, mem_zpowers a⟩
  have heq : commutatorAction (zpowers a) V = commutatorSubgroup (zpowers x) V W := by
    apply le_antisymm
    · rw [commutatorAction_eq_closure]
      apply (closure_le _).mpr
      rintro _ ⟨b, v, rfl⟩
      obtain ⟨n, hn⟩ := b.property
      have hv : v ∈ W ⊔ S := hsplit ▸ mem_top v
      let _ : W.Normal := normal_of_isMulCommutative _
      obtain ⟨w, hw, s, hs, rfl⟩ := mem_sup_of_normal_left.mp hv
      have hbs : (b : G) • s = s := smul_eq_self_of_mem_zpowers b.property (haS s hs)
      have hbw : (b : G) • w = x ^ n • w := hn ▸ haW n w hw
      have hid : (w * s)⁻¹ * (b • (w * s)) = w⁻¹ * (x ^ n • w) := by
        change (w * s)⁻¹ * ((b : G) • (w * s)) = _
        rw [smul_mul', hbs, hbw, mul_inv_rev]
        calc
          s⁻¹ * w⁻¹ * (((x ^ n) • w) * s) = (s⁻¹ * s) * (w⁻¹ * ((x ^ n) • w)) := by ac_rfl
          _ = w⁻¹ * ((x ^ n) • w) := by rw [inv_mul_cancel, one_mul]
      rw [hid]
      exact subset_closure ⟨⟨x ^ n, (zpowers x).zpow_mem (mem_zpowers x) n⟩, w, hw, rfl⟩
    · apply (closure_le _).mpr
      rintro _ ⟨b, v, hv, rfl⟩
      obtain ⟨n, hn⟩ := b.property
      rw [commutatorAction_eq_closure]
      refine subset_closure ⟨⟨a ^ n, (zpowers a).zpow_mem (mem_zpowers a) n⟩, v, ?_⟩
      change v⁻¹ * ((b : G) • v) = v⁻¹ * (a ^ n • v)
      change x ^ n = (b : G) at hn
      rw [haW n v hv, hn]
  have haCard : Nat.card (commutatorAction (zpowers a) V) = 4 := heq ▸ hxcard
  have ha3 : a ^ 3 = 1 := by
    dsimp [a]
    rw [haz.mul_pow, inv_pow, hx3, mul_one]
    have hz3 : z ^ 3 = 1 := by
      have hd := X.orderOf_dvd_natCard hz
      have hX3 : Nat.card X = 3 := by simpa using hX.2.1
      rw [hX3] at hd
      exact orderOf_dvd_iff_pow_eq_one.mp hd
    rw [hz3, inv_one]
  have ha_ne : a ≠ 1 := by
    intro he
    have hb : commutatorAction (zpowers a) V = ⊥ := by
      rw [commutatorAction_eq_closure]
      apply bot_unique
      apply (closure_le _).mpr
      rintro _ ⟨b, v, rfl⟩
      have hb : (b : G) = 1 := by simpa [he] using b.property
      simp [Subgroup.smul_def, hb]
    rw [hb, card_bot] at haCard
    omega
  have haOrder : orderOf a = 3 :=
    (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one ha3) |>.resolve_left
      (fun h => ha_ne (orderOf_eq_one_iff.mp h))
  have haFactor : zpowers a ∈ smallSupportFactors G V 1 := by
    refine ⟨zpowers_le.mpr ((fittingSubgroup G).mul_mem
      ((fittingSubgroup G).inv_mem (hX.1 hz)) hxF), ?_, ?_⟩
    · simp [Nat.card_zpowers, haOrder]
    · simpa using haCard
  have haY : a ∈ Y := (le_sSup haFactor) (mem_zpowers a)
  have hxW (v : V) (hv : v ∈ W) : x • v = v := by
    have hh := haW 1 v hv
    simpa using hh.symm.trans (show a ^ (1 : ℤ) • v = v from by
      simpa using hv ⟨a, haY⟩)
  have hbot : commutatorSubgroup (zpowers x) V W = ⊥ := by
    apply bot_unique
    apply (closure_le _).mpr
    rintro _ ⟨b, v, hv, rfl⟩
    have hh := smul_eq_self_of_mem_zpowers b.property (hxW v hv)
    change v⁻¹ * ((b : G) • v) = 1
    rw [hh, inv_mul_cancel]
  change Nat.card (commutatorSubgroup (zpowers x) V W) = 4 at hxcard
  rw [hbot, card_bot] at hxcard
  omega
end CFSG.Quasithin.ChapterD
