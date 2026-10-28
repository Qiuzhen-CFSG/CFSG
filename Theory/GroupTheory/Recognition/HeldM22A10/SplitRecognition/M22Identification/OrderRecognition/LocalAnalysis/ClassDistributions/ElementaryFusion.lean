module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.ClassDistributions.Model
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.FourFusion
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.ElementCentralizers

/-!
# Elementary ambient fusion in Janko's Case II

An element of order six has an involutory cube. Conjugating that cube to
the marked involution reduces fusion to a finite calculation in its
centralizer. The local class of `bd` has order four and cannot fuse with
`z 1 * d`: the latter has an abelian centralizer, which would force the
centralizer of `bd` into the marked centralizer and contradict its order.
Both arguments take ambient involution fusion explicitly.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 5, pp.8–9.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification
open LocalModelDichotomy
namespace CaseII.Distribution

local instance : DecidableEq TwistedModel := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right) SemidirectProduct.ext_iff.symm
local instance : Fintype TwistedModel := Fintype.ofEquiv
  (BinaryFour × SymmetricFour) SemidirectProduct.equivProd.symm

private theorem model_six_roots (x : TwistedModel) (hx : x ^ 3 = z 0)
    (hne : x ^ 2 ≠ 1) : IsConj x (c * z 0) := by
  have h : ∀ i : Fin 17, localRepresentative i ^ 3 = z 0 →
      localRepresentative i ^ 2 ≠ 1 → i = 7 := by decide +kernel
  have hc := localClass_conjugate x
  have h3 : localRepresentative (localClass x) ^ 3 = z 0 := by
    have hp := hc.pow 3
    rw [hx] at hp
    exact (hp.eq_of_left_mem_center z_zero_mem_center).symm
  have h2 : localRepresentative (localClass x) ^ 2 ≠ 1 := by
    intro h2
    have hp := hc.pow 2
    rw [h2] at hp
    exact hne (hp.eq_of_right_mem_center Set.one_mem_center)
  rw [h _ h3 h2] at hc
  exact hc

universe u
variable {G : Type u} [Group G] [Finite G]

/-- Conjugating the cube reduces order-six fusion to the local model. -/
public theorem six_fusion (D : LocalData G) (k : TwistedModel ≃* D.centralizer)
    (h2 : ∀ x : G, orderOf x = 2 → IsConj x D.z)
    (x : G) (hx : orderOf x = 6) : IsConj x (into D k (c * z 0)) := by
  have hx3 : orderOf (x ^ 3) = 2 := by
    rw [orderOf_pow' x (by decide), hx]
    norm_num
  obtain ⟨g, hg⟩ := isConj_iff.mp (h2 _ hx3)
  let y := (MulAut.conj g) x
  have hy3 : y ^ 3 = D.z := by
    rw [show y ^ 3 = (MulAut.conj g) (x ^ 3) from (map_pow _ _ _).symm]
    exact hg
  have hyC : y ∈ D.centralizer := by
    apply mem_centralizer_singleton_iff.mpr
    rw [← hy3]
    exact (Commute.refl y).pow_right 3
  obtain ⟨v, hv⟩ := k.surjective ⟨y, hyC⟩
  have hvy : into D k v = y := congrArg Subtype.val hv
  have hv3 : v ^ 3 = z 0 := by
    apply into_injective D k
    rw [map_pow, hvy, into_z_zero D k]
    exact hy3
  have hv2 : v ^ 2 ≠ 1 := by
    intro h
    have hv6 : orderOf v = 6 := by
      rw [← orderOf_injective (into D k) (into_injective D k), hvy]
      exact ((MulAut.conj g).orderOf_eq x).trans hx
    have hh := orderOf_dvd_of_pow_eq_one h
    rw [hv6] at hh
    norm_num at hh
  have hxy : IsConj x (into D k v) := isConj_iff.mpr ⟨g, hvy.symm⟩
  exact hxy.trans ((into D k).map_isConj (model_six_roots v hv3 hv2))

private theorem commutative_centralizer_zd (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (x y : G)
    (hx : Commute x (into D k (z 1 * d)))
    (hy : Commute y (into D k (z 1 * d))) : Commute x y := by
  have hp : (z 1 * d) ^ 2 = z 0 := representative_powers 1
  have he := centralizer_root_map D k (z 1 * d) 2 hp
  have hx' : x ∈ centralizer ({into D k (z 1 * d)} : Set G) := mem_centralizer_singleton_iff.mpr hx.eq
  have hy' : y ∈ centralizer ({into D k (z 1 * d)} : Set G) := mem_centralizer_singleton_iff.mpr hy.eq
  rw [he] at hx' hy'
  obtain ⟨v, hv, rfl⟩ := hx'
  obtain ⟨w, hw, rfl⟩ := hy'
  have h : ∀ v : TwistedModel,
      v * (z 1 * d) = (z 1 * d) * v → ∀ w : TwistedModel,
      w * (z 1 * d) = (z 1 * d) * w → v * w = w * v := by decide +kernel
  exact (Commute.map (show Commute v w from h _
    (mem_centralizer_singleton_iff.mp hv) _ (mem_centralizer_singleton_iff.mp hw)) (into D k))

/-- The local class of `bd` belongs to the class with centralizer order 32.
If its centralizer were the abelian centralizer of `z 1 * d`, all of it
would centralize `z 0`, contradicting the local centralizer order eight. -/
public theorem bd_fusion (D : LocalData G) (k : TwistedModel ≃* D.centralizer)
    (h2 : ∀ x : G, orderOf x = 2 → IsConj x D.z) :
    IsConj (into D k (b * d)) (into D k (z 3 * a)) := by
  have ho : orderOf (into D k (b * d)) = 4 := by
    rw [orderOf_injective (into D k) (into_injective D k)]
    exact localRepresentative_order 12
  rcases four_fusion_of_involution_fusion D k h2 _ ho with h | h
  · exact h
  exfalso
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  let e := MulAut.conj g
  have he : e (into D k (b * d)) = into D k (z 1 * d) := hg
  have hz : Commute D.z (into D k (b * d)) := by
    rw [← into_z_zero D k]
    exact (show Commute (z 0) (b * d) from (z_zero_mem_center.comm _)).map (into D k)
  have hle : centralizer ({into D k (b * d)} : Set G) ≤ D.centralizer := by
    intro x hx
    have hc : Commute x (into D k (b * d)) := mem_centralizer_singleton_iff.mp hx
    have hc' : Commute (e x) (e (into D k (b * d))) := hc.map e.toMonoidHom
    have hz' : Commute (e D.z) (e (into D k (b * d))) := hz.map e.toMonoidHom
    rw [he] at hc' hz'
    have hcomm := commutative_centralizer_zd D k (e x) (e D.z) hc' hz'
    apply mem_centralizer_singleton_iff.mpr
    apply e.injective
    simpa only [map_mul] using hcomm.eq
  have hmap : centralizer ({into D k (b * d)} : Set G) =
      (centralizer ({b * d} : Set TwistedModel)).map (into D k) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨v, hv⟩ := k.surjective ⟨x, hle hx⟩
      have hvx : into D k v = x := congrArg Subtype.val hv
      refine ⟨v, mem_centralizer_singleton_iff.mpr ?_, hvx⟩
      apply into_injective D k
      simpa only [map_mul, hvx] using (mem_centralizer_singleton_iff.mp hx)
    · rintro x ⟨v, hv, rfl⟩
      apply mem_centralizer_singleton_iff.mpr
      exact (Commute.map (show Commute v (b * d) from
        mem_centralizer_singleton_iff.mp hv) (into D k)).eq
  have hcard : Nat.card (centralizer ({into D k (b * d)} : Set G)) = 8 := by
    let : DecidablePred (· ∈ centralizer ({b * d} : Set TwistedModel)) := fun x =>
      decidable_of_iff (x * (b * d) = (b * d) * x) mem_centralizer_singleton_iff.symm
    rw [hmap, ← Nat.card_congr
      ((centralizer ({b * d} : Set TwistedModel)).equivMapOfInjective
        (into D k) (into_injective D k)).toEquiv, Nat.card_eq_fintype_card]
    decide +kernel
  have hec : Nat.card (centralizer ({into D k (b * d)} : Set G)) =
      Nat.card (centralizer ({into D k (z 1 * d)} : Set G)) := by
    apply Nat.card_congr (Equiv.subtypeEquiv e.toEquiv ?_)
    intro t
    change t ∈ centralizer ({into D k (b * d)} : Set G) ↔
      e t ∈ centralizer ({into D k (z 1 * d)} : Set G)
    simp only [mem_centralizer_singleton_iff, ← he, ← map_mul, e.injective.eq_iff]
  have h16 := centralizer_orders D k 1
  change Nat.card (centralizer ({into D k (z 1 * d)} : Set G)) = 16 at h16
  omega

end CaseII.Distribution
end Theory.GroupTheory.HeldM22A10.M22Identification
