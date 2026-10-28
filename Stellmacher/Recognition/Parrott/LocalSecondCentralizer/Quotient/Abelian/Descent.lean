module

public import Stellmacher.Recognition.Parrott.LocalSecondCentralizer.Quotient.Abelian.Displacement

/-!
# Small abelian images in the literal transfer quotient

An abelian overgroup of the pair normalizer, of order at most 32 and
containing v, maps to an abelian overgroup of the local quotient centralizer
of order at most 16. The kernel is the actual central subgroup ⟨v⟩ of
order two. For an outside lift k, the group ⟨k⟩Z(Y) is abelian and has
order at most 32, since k⁴=1 and |Z(Y)|=8.

The final theorem isolates the two containments of source observation (ii).
It does not assume any quotient-centralizer calculation or Sylow promotion.
Both local containments remain explicit premises.

Source: Parrott (1972), Lemma 8, printed p.683.
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSecondTransferData
variable {G : Type*} [Group G] [Finite G] {z : G}
  {d : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData d}
  (t : ParrottSecondTransferData n)

/-- An element of Y of order dividing four and the center of Y generate
an abelian subgroup of order at most 32. -/
public theorem sylowCenter_sup_zpowers_small {k : G} (hk : k ∈ t.sylowImage)
    (hk4 : k ^ 4 = 1) :
    IsMulCommutative (zpowers k ⊔ t.sylowCenter : Subgroup G) ∧
      Nat.card (zpowers k ⊔ t.sylowCenter : Subgroup G) ≤ 32 := by
  let Z := t.sylowCenter
  let R := zpowers k
  have hZR : Z ≤ centralizer (R : Set G) :=
    t.sylowCenter_le_centralizer.trans (centralizer_le (zpowers_le.mpr hk))
  let : IsMulCommutative Z := by
    change IsMulCommutative ((center t.sylowImage).map t.sylowImage.subtype)
    infer_instance
  have hab : IsMulCommutative (R ⊔ Z : Subgroup G) := by
    apply le_centralizer_iff_isMulCommutative.mp
    apply sup_le
    · exact le_centralizer_iff.mpr (sup_le R.le_centralizer hZR)
    · exact le_centralizer_iff.mpr (sup_le (le_centralizer_iff.mp hZR) Z.le_centralizer)
  refine ⟨hab, ?_⟩
  have hR : Nat.card R ≤ 4 := by
    rw [show R = zpowers k from rfl, Nat.card_zpowers]
    exact Nat.le_of_dvd (by decide) (orderOf_dvd_of_pow_eq_one hk4)
  have hZ : Nat.card Z = 8 := t.sylowCenter_card
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes R Z
    (hZR.trans (Subgroup.centralizer_le_normalizer _))
  have hi : 1 ≤ Nat.card (R ⊓ Z : Subgroup G) := Nat.card_pos
  change Nat.card (R ⊔ Z : Subgroup G) ≤ 32
  nlinarith

/-- A small abelian overgroup of the actual pair normalizer descends to
the required small abelian local centralizer. The central kernel has order two. -/
public theorem quotientLocalCentralizer_small_of_pairNormalizer_le
    {k : t.L} (hk2 : orderOf (QuotientGroup.mk' (zpowers t.v) k) = 2)
    (A : Subgroup G) [IsMulCommutative A] (hvA : n.v ∈ A)
    (hA : Nat.card A ≤ 32) (hp : t.pairNormalizer (t.embedding k) ≤ A) :
    IsMulCommutative (t.quotientLocalCentralizer (QuotientGroup.mk' (zpowers t.v) k)) ∧
      Nat.card (t.quotientLocalCentralizer (QuotientGroup.mk' (zpowers t.v) k)) ≤ 16 := by
  let q := QuotientGroup.mk' (zpowers t.v)
  let B := A.comap t.embedding
  let D := t.quotientLocalCentralizer (q k)
  have hDB : D ≤ B.map q := by
    intro x hx
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (zpowers t.v) x
    apply mem_map_of_mem q
    apply hp
    rw [← t.localCentralizer_preimage_map hk2]
    exact mem_map_of_mem t.embedding hx
  let : IsMulCommutative B := A.comap_injective_isMulCommutative t.embedding_injective
  let : IsMulCommutative (B.map q) := inferInstance
  have hD : IsMulCommutative D := le_centralizer_iff_isMulCommutative.mp
    (hDB.trans ((B.map q).le_centralizer.trans (centralizer_le hDB)))
  have hBcard : Nat.card B ≤ 32 := by
    let f : B → A := fun b => ⟨t.embedding b, b.property⟩
    have hf : Function.Injective f := by
      intro a b he
      exact Subtype.ext (t.embedding_injective (congrArg A.subtype he))
    exact (Nat.card_le_card_of_injective f hf).trans hA
  have hkerB : q.ker ≤ B := by
    rw [QuotientGroup.ker_mk']
    apply zpowers_le.mpr
    change t.embedding t.v ∈ A
    rwa [t.v_image]
  have hkerCard : Nat.card q.ker = 2 := by
    rw [QuotientGroup.ker_mk', Nat.card_zpowers,
      ← orderOf_injective t.embedding t.embedding_injective, t.v_image, n.v_order]
  have hc := relIndex_mul_relIndex (⊥ : Subgroup t.L) q.ker B bot_le hkerB
  rw [relIndex_bot_left, relIndex_bot_left, relIndex_ker, hkerCard] at hc
  have hbound : Nat.card (B.map q) ≤ 16 := by omega
  exact ⟨hD, (card_le_of_le hDB).trans hbound⟩

/-- Observation (ii), in its two local branches, supplies exactly the `hsmall`
premise of `quotient_involution_centralizers_of_local_calculations`.
This is a conditional descent theorem; the two pair-normalizer calculations
must still be proved from the source hypotheses. -/
public theorem quotientLocalCentralizer_small_of_pair_normalizers
    (helementary : ∀ k ∈ t.sylowImage, k ∉ t.sylowCenter → k ∈ d.F →
      t.pairNormalizer k ≤ d.F)
    (houter : ∀ k ∈ t.sylowImage, k ∉ d.F → k ^ 2 ∈ zpowers n.v →
      t.pairNormalizer k ≤ zpowers k ⊔ t.sylowCenter) :
    ∀ x ∈ t.quotientSylow, orderOf x = 2 → x ∉ t.quotientCoreCenter →
      IsMulCommutative (t.quotientLocalCentralizer x) ∧
        Nat.card (t.quotientLocalCentralizer x) ≤ 16 := by
  intro x hx hx2 hxZ
  obtain ⟨k, hk, rfl⟩ := hx
  have hkY : t.embedding k ∈ t.sylowImage := mem_map_of_mem t.embedding hk
  have hkZ : t.embedding k ∉ t.sylowCenter := t.lift_not_mem_sylowCenter hxZ
  let : IsElementaryAbelian 2 d.F := d.elementary
  by_cases hkF : t.embedding k ∈ d.F
  · exact t.quotientLocalCentralizer_small_of_pairNormalizer_le hx2 d.F n.v_mem_inf.2
      (by rw [d.card]) (helementary _ hkY hkZ hkF)
  · have hksq : (t.embedding k) ^ 2 ∈ zpowers n.v := by
      have hk2 : k ^ 2 ∈ zpowers t.v := by
        apply (QuotientGroup.eq_one_iff _).mp
        change QuotientGroup.mk' (zpowers t.v) (k ^ 2) = 1
        rw [map_pow, ← hx2, pow_orderOf_eq_one]
      simpa only [MonoidHom.map_zpowers, t.v_image, map_pow] using
        (mem_map_of_mem t.embedding hk2)
    have hk4 : (t.embedding k) ^ 4 = 1 := by
      have he : ((t.embedding k) ^ 2) ^ 2 = 1 :=
        elemPow_eq_one_of_isElementaryAbelian ((t.embedding k) ^ 2)
        ((zpowers_le.mpr n.v_mem_inf.2) hksq)
      simpa only [← pow_mul, Nat.reduceMul] using he
    obtain ⟨hab, hcard⟩ := t.sylowCenter_sup_zpowers_small hkY hk4
    let := hab
    exact t.quotientLocalCentralizer_small_of_pairNormalizer_le hx2
      (zpowers (t.embedding k) ⊔ t.sylowCenter)
      (mem_sup_right t.v_mem_sylowCenter) hcard (houter _ hkY hkF hksq)

end Stellmacher.Recognition.ParrottSecondTransferData
