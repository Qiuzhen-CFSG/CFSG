module

public import Stellmacher.Recognition.Parrott.LocalSecondCentralizer.Quotient.Normalizer.Actor
public import Stellmacher.Recognition.Parrott.LocalSecondCentralizer.Quotient.Sylow
public import Theory.GroupTheory.FourGroupNormalizerIndex
public import Theory.GroupTheory.FixedPointFreeCyclicJoin

/-!
# Pointwise core-center control in the actual quotient normalizer

Write Y for the supplied Sylow image in L/⟨v⟩ and E for its central four-group.
Every nonidentity element of E has centralizer Y. Its orbit in E bounds
|N(E):Y| by three, while the supplied three-group attains that bound.
Thus N(E)=Y⟨q⟩. The fixed-point-free action of q makes every element outside
Y conjugate under Y to a nonidentity power of q; such an element cannot
centralize a nonidentity element of Y.

The normalizer of C_Y(x) preserves E by the existing two-overgroup theorem.
Its intersection with C(x) therefore lies in Y and centralizes E pointwise.
This discharges the normalizer premise in the actual quotient-centralizer
assembly without an abelian Sylow assumption or a distinct-fusion premise.
The final assembly remains in LocalSecondCentralizer.QuotientCentralizers.

Source: Parrott (1972), Lemma 8, printed p.683, observation (i) and the
distinct-conjugacy-class argument preceding the normal-complement step.
-/

open Subgroup
open scoped Pointwise

namespace Stellmacher.Recognition.ParrottSecondTransferData
variable {X : Type*} [Group X] [Finite X]

private theorem fixed_free_cubic_centralizer (Y : Subgroup X) (q : X)
    (hqY : q ∈ normalizer (Y : Set X)) (hq3 : orderOf q = 3)
    (hfree : ∀ y ∈ Y, Commute q y → y = 1)
    {x : X} (hxY : x ∈ Y) (hx1 : x ≠ 1) :
    centralizer ({x} : Set X) ⊓ (Y ⊔ zpowers q) ≤ Y := by
  intro g hg
  have hQY : zpowers q ≤ normalizer (Y : Set X) := zpowers_le.mpr hqY
  have hgprod : g ∈ (Y : Set X) * (zpowers q : Set X) := by
    rw [← coe_mul_of_right_le_normalizer_left Y (zpowers q) hQY]
    exact hg.2
  obtain ⟨y, hy, a, ha, rfl⟩ := hgprod
  by_cases ha1 : a = 1
  · simpa [ha1] using hy
  have ha_free : ∀ u ∈ Y, Commute a u → u = 1 := by
    intro u hu hcomm
    have hcard : Nat.card (zpowers q) = 3 := (Nat.card_zpowers q).trans hq3
    have hqa : (⟨q, mem_zpowers q⟩ : zpowers q) ∈ zpowers (⟨a, ha⟩ : zpowers q) :=
      mem_zpowers_of_prime_card hcard
      (show (⟨a, ha⟩ : zpowers q) ≠ 1 from fun he => ha1 (congrArg Subtype.val he))
    obtain ⟨k, hk⟩ := hqa
    have hk' : a ^ k = q := congrArg Subtype.val hk
    exact hfree u hu (hk' ▸ hcomm.zpow_left k)
  let φ := Y.normalizerMonoidHom ⟨a, hQY ha⟩
  have hφ : MonoidHom.FixedPointFree φ := by
    intro u hu
    apply Subtype.ext
    apply ha_free u u.property
    exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hu)
  obtain ⟨c, hc⟩ := hφ.commutatorMap_surjective (⟨y, hy⟩ : Y)
  have hc' : (c : X) / (a * (c : X) * a⁻¹) = y := congrArg Subtype.val hc
  have hconj : y * a = (c : X) * a * (c : X)⁻¹ := by
    rw [← hc']
    simp [div_eq_mul_inv, mul_assoc]
  have hcomm : Commute a ((c : X)⁻¹ * x * (c : X)) := by
    have hh : Commute (y * a) x := mem_centralizer_singleton_iff.mp hg.1
    have hh' := hh.conj (c : X)⁻¹
    simpa [hconj, mul_assoc] using hh'
  have hzero := ha_free _ (Y.mul_mem (Y.mul_mem (Y.inv_mem c.property) hxY)
    c.property) hcomm
  have hxzero : x = 1 := by
    have hh := congrArg (MulAut.conj (c : X)) hzero
    simpa [MulAut.conj_apply, mul_assoc] using hh
  exact (hx1 hxzero).elim

private theorem four_normalizer_eq_cubic_join (Y E : Subgroup X)
    (hY : IsPGroup 2 Y) (hEcard : Nat.card E = 4)
    (hYE : Y ≤ centralizer (E : Set X))
    (hcent : ∀ e ∈ E, e ≠ 1 → centralizer ({e} : Set X) ≤ Y)
    (q : X) (hq3 : orderOf q = 3)
    (hqY : q ∈ normalizer (Y : Set X))
    (hqE : q ∈ normalizer (E : Set X)) :
    normalizer (E : Set X) = Y ⊔ zpowers q := by
  have hYN : Y ≤ normalizer (E : Set X) :=
    hYE.trans (Subgroup.centralizer_le_normalizer _)
  have hJN : Y ⊔ zpowers q ≤ normalizer (E : Set X) :=
    sup_le hYN (zpowers_le.mpr hqE)
  apply (eq_of_le_of_card_ge hJN _).symm
  have hEnontriv : E ≠ ⊥ := by
    intro he
    rw [he, card_bot] at hEcard
    omega
  obtain ⟨e, he, he1⟩ := E.bot_or_exists_ne_one.resolve_left hEnontriv
  have hCe : centralizer ({e} : Set X) = Y := by
    apply le_antisymm (hcent e he he1)
    intro y hy
    exact mem_centralizer_singleton_iff.mpr ((hYE hy e he).symm)
  have hi := centralizer_relIndex_le_card_sub_one
    (normalizer (E : Set X)) E le_rfl e he he1
  rw [hCe, hEcard] at hi
  have hcard := relIndex_mul_relIndex (⊥ : Subgroup X) Y
    (normalizer (E : Set X)) bot_le hYN
  rw [relIndex_bot_left, relIndex_bot_left] at hcard
  have hdis : Disjoint Y (zpowers q) := by
    apply disjoint_of_coprime_natCard
    obtain ⟨r, hr⟩ := hY.exists_card_eq
    rw [hr, Nat.card_zpowers, hq3]
    exact (show Nat.Coprime 2 3 by decide).pow_left r
  rw [card_sup_of_disjoint_of_normalizes Y (zpowers q) hdis (zpowers_le.mpr hqY),
    Nat.card_zpowers, hq3, ← hcard]
  exact Nat.mul_le_mul_left _ hi

end Stellmacher.Recognition.ParrottSecondTransferData

namespace Stellmacher.Recognition.ParrottSecondTransferData
variable {G : Type*} [Group G] [Finite G] {z : G}
  {d : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData d}
  (t : ParrottSecondTransferData n)

/-- The core-center normalizer has no new centralizers of nonidentity Sylow elements. -/
public theorem quotientCoreCenter_normalizer_centralizer_le
    (h : ParrottCentralizerHypotheses z) {x : t.Quotient}
    (hx : x ∈ t.quotientSylow) (hx1 : x ≠ 1) :
    centralizer ({x} : Set t.Quotient) ⊓
        normalizer (t.quotientCoreCenter : Set t.Quotient) ≤ t.quotientSylow := by
  obtain ⟨q, hq3, hqY, hfree⟩ := t.exists_quotient_three_actor
  have hY : IsPGroup 2 t.quotientSylow :=
    t.S.isPGroup'.map (QuotientGroup.mk' (zpowers t.v))
  have hYE : t.quotientSylow ≤ centralizer (t.quotientCoreCenter : Set t.Quotient) :=
    le_centralizer_iff.mp t.quotientCoreCenter_le_centralizer
  have hqE := t.quotient_two_overgroup_normalizer h t.quotientSylow hY
    t.quotientCoreCenter_le_sylow hqY
  have hN := four_normalizer_eq_cubic_join t.quotientSylow t.quotientCoreCenter hY
    t.quotientCoreCenter_card hYE
    (fun _ he he1 => t.quotientCoreCenter_centralizer_le h he he1) q hq3 hqY hqE
  rw [hN]
  exact fixed_free_cubic_centralizer t.quotientSylow q hqY hq3 hfree hx hx1

/-- The actual local-centralizer normalizer fixes the core center pointwise. -/
public theorem quotient_localCentralizer_normalizer_le_centralizer
    (h : ParrottCentralizerHypotheses z) {x : t.Quotient}
    (hx : x ∈ t.quotientSylow) (hx1 : x ≠ 1) :
    centralizer ({x} : Set t.Quotient) ⊓
        normalizer (t.quotientLocalCentralizer x : Set t.Quotient) ≤
      centralizer (t.quotientCoreCenter : Set t.Quotient) := by
  have hnorm := t.quotient_two_overgroup_normalizer h
    (t.quotientLocalCentralizer x) (t.quotientLocalCentralizer_isTwoGroup x)
    (t.quotientCoreCenter_le_localCentralizer hx)
  exact (inf_le_inf_left _ hnorm).trans
    ((t.quotientCoreCenter_normalizer_centralizer_le h hx hx1).trans
      (le_centralizer_iff.mp t.quotientCoreCenter_le_centralizer))

/-- The normalizer premise required by the quotient involution-centralizer assembly. -/
public theorem quotient_involution_normalizer_centralization
    (h : ParrottCentralizerHypotheses z) :
    ∀ x ∈ t.quotientSylow, orderOf x = 2 → x ∉ t.quotientCoreCenter →
      centralizer ({x} : Set t.Quotient) ⊓
          normalizer (t.quotientLocalCentralizer x : Set t.Quotient) ≤
        centralizer (t.quotientCoreCenter : Set t.Quotient) := by
  intro x hx hx2 _
  apply t.quotient_localCentralizer_normalizer_le_centralizer h hx
  intro he
  simp [he] at hx2

end Stellmacher.Recognition.ParrottSecondTransferData
