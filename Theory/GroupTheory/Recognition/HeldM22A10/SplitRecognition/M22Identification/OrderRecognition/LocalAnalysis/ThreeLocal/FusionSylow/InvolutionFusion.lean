module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.Contracts
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.ClassDistributions.Model

/-!
# Involutions in the centralizer of the Case II element of order three

The coordinate model has one class of elements of order three. Ambient
involution fusion therefore conjugates any commuting three-involution pair to
`(c,z)`. In particular, all involutions of C_G(c) are conjugate within C_G(c).
The centralizer of each such involution is abelian of order twelve, as verified
in the coordinate model. These are local inputs for the Suzuki argument, not
an identification of C_G(c).

In addition, the centralizer of any subgroup of order nine has odd order:
an involution centralizing it would put that subgroup inside an involution
centralizer of order 384.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 3, pp.7–8.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification
open LocalModelDichotomy
namespace CaseII

public theorem model_three_fusion (x : TwistedModel) (hx : orderOf x = 3) : IsConj x c := by
  have h := Distribution.localClass_conjugate x
  have ho : orderOf (Distribution.localRepresentative (Distribution.localClass x)) = 3 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp h
    rw [← hg]
    exact ((MulAut.conj g).orderOf_eq x).trans hx
  rw [Distribution.localRepresentative_order] at ho
  have hi : Distribution.localClass x = 6 := by
    generalize Distribution.localClass x = i at ho ⊢
    have ht : ∀ i : Fin 17,
        ![1, 2, 2, 2, 2, 2, 3, 6, 6, 6, 4, 4, 4, 4, 4, 4, 8] i = 3 → i = 6 := by
      decide
    exact ht i ho
  rw [hi] at h
  exact h

universe u
variable {G : Type u} [Group G]

public theorem conjugate_three_involution_pair (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer)
    (h2 : ∀ t : G, orderOf t = 2 → IsConj t D.z)
    (x : G) (hx : orderOf x = 3)
    (t : G) (ht : orderOf t = 2) (hxt : Commute x t) :
    ∃ g : G, g * x * g⁻¹ = into D k c ∧ g * t * g⁻¹ = D.z := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (h2 t ht)
  let y := (MulAut.conj g) x
  have hyC : y ∈ D.centralizer := by
    apply mem_centralizer_singleton_iff.mpr
    rw [← hg]
    change (MulAut.conj g) x * (MulAut.conj g) t =
      (MulAut.conj g) t * (MulAut.conj g) x
    simpa only [← map_mul] using congrArg (MulAut.conj g) hxt.eq
  obtain ⟨v, hv⟩ := k.surjective ⟨y, hyC⟩
  have hvy : into D k v = y := congrArg Subtype.val hv
  have hvo : orderOf v = 3 := by
    rw [← orderOf_injective (into D k) (into_injective D k) v, hvy,
      MulEquiv.orderOf_eq, hx]
  obtain ⟨s, hs⟩ := isConj_iff.mp (model_three_fusion v hvo)
  have hsc : into D k s * y * (into D k s)⁻¹ = into D k c := by
    rw [← hvy]
    simpa only [map_mul, map_inv] using congrArg (into D k) hs
  have hsz : into D k s * D.z * (into D k s)⁻¹ = D.z := by
    apply mul_inv_eq_iff_eq_mul.mpr
    exact mem_centralizer_singleton_iff.mp (k s).property
  refine ⟨into D k s * g, ?_, ?_⟩
  · simpa only [y, MulAut.conj_apply, mul_inv_rev, mul_assoc] using hsc
  · have hh : into D k s * (g * t * g⁻¹) * (into D k s)⁻¹ = D.z := by
      rw [hg]
      exact hsz
    simpa only [mul_inv_rev, mul_assoc] using hh

public theorem three_fusion_of_commuting_involution (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer)
    (h2 : ∀ t : G, orderOf t = 2 → IsConj t D.z)
    (x : G) (hx : orderOf x = 3)
    (t : G) (ht : orderOf t = 2) (hxt : Commute x t) :
    IsConj x (into D k c) := by
  obtain ⟨g, hg, _⟩ := conjugate_three_involution_pair D k h2 x hx t ht hxt
  exact isConj_iff.mpr ⟨g, hg⟩

@[expose] public def markedInvolutionInThreeCentralizer (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) : centralizer ({into D k c} : Set G) :=
  ⟨D.z, mem_centralizer_singleton_iff.mpr
    (mem_centralizer_singleton_iff.mp (k c).property).symm⟩

public theorem three_centralizer_involution_fusion (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer)
    (h2 : ∀ t : G, orderOf t = 2 → IsConj t D.z)
    (t : centralizer ({into D k c} : Set G)) (ht : orderOf t = 2) :
    IsConj t (markedInvolutionInThreeCentralizer D k) := by
  have hc : orderOf (into D k c) = 3 :=
    (orderOf_injective (into D k) (into_injective D k) c).trans actor_orders.2.2.1
  obtain ⟨g, hgc, hgt⟩ := conjugate_three_involution_pair D k h2
    (into D k c) hc t (by simpa only [orderOf_coe] using ht)
    (mem_centralizer_singleton_iff.mp t.property).symm
  have hg : g ∈ centralizer ({into D k c} : Set G) :=
    mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hgc)
  exact isConj_iff.mpr ⟨⟨g, hg⟩, Subtype.ext hgt⟩


local instance : DecidableEq TwistedModel := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right) SemidirectProduct.ext_iff.symm
local instance : Fintype TwistedModel := Fintype.ofEquiv
  (BinaryFour × SymmetricFour) SemidirectProduct.equivProd.symm

@[expose] public def modelThreeCentralizer : Subgroup TwistedModel := centralizer {c}

local instance : DecidablePred (· ∈ modelThreeCentralizer) := fun x =>
  decidable_of_iff (x * c = c * x) mem_centralizer_singleton_iff.symm

public theorem modelThreeCentralizer_card : Nat.card modelThreeCentralizer = 12 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

public theorem modelThreeCentralizer_commutative : IsMulCommutative modelThreeCentralizer := by
  have h : ∀ x y : modelThreeCentralizer,
      (x : TwistedModel) * y = y * x := by decide +kernel
  exact ⟨⟨fun x y => Subtype.ext (h x y)⟩⟩

public noncomputable def markedThreeInvolutionCentralizerEquiv (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) :
    modelThreeCentralizer ≃*
      centralizer ({markedInvolutionInThreeCentralizer D k} :
        Set (centralizer ({into D k c} : Set G))) := by
  let f : modelThreeCentralizer →*
      centralizer ({markedInvolutionInThreeCentralizer D k} :
        Set (centralizer ({into D k c} : Set G))) :=
    { toFun := fun v =>
        ⟨⟨into D k v, mem_centralizer_singleton_iff.mpr (by
            simpa only [map_mul] using congrArg (into D k)
              (mem_centralizer_singleton_iff.mp v.property))⟩,
          mem_centralizer_singleton_iff.mpr (Subtype.ext
            (mem_centralizer_singleton_iff.mp (k v).property))⟩
      map_one' := Subtype.ext (Subtype.ext (map_one (into D k)))
      map_mul' := fun x y => Subtype.ext (Subtype.ext
        (map_mul (into D k) (x : TwistedModel) (y : TwistedModel))) }
  apply MulEquiv.ofBijective f
  constructor
  · intro x y h
    exact Subtype.ext (into_injective D k
      (congrArg (fun v => ((v.val : centralizer ({into D k c} : Set G)) : G)) h))
  · intro x
    have hz : ((x.val : centralizer ({into D k c} : Set G)) : G) ∈ D.centralizer :=
      mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property))
    obtain ⟨v, hv⟩ := k.surjective ⟨x.val, hz⟩
    have hvx : into D k v = (x.val : G) := congrArg Subtype.val hv
    have hvc : v ∈ modelThreeCentralizer := by
      apply mem_centralizer_singleton_iff.mpr
      apply into_injective D k
      simp only [map_mul, hvx]
      exact mem_centralizer_singleton_iff.mp x.val.property
    exact ⟨⟨v, hvc⟩, Subtype.ext (Subtype.ext hvx)⟩

public theorem marked_three_involution_centralizer_card (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) :
    Nat.card (centralizer ({markedInvolutionInThreeCentralizer D k} :
      Set (centralizer ({into D k c} : Set G)))) = 12 := by
  rw [← Nat.card_congr (markedThreeInvolutionCentralizerEquiv D k).toEquiv]
  exact modelThreeCentralizer_card


public theorem marked_three_involution_centralizer_commutative (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) :
    IsMulCommutative (centralizer ({markedInvolutionInThreeCentralizer D k} :
      Set (centralizer ({into D k c} : Set G)))) := by
  let e := markedThreeInvolutionCentralizerEquiv D k
  refine ⟨⟨fun x y => ?_⟩⟩
  apply e.symm.injective
  simp only [map_mul]
  exact modelThreeCentralizer_commutative.is_comm.comm (e.symm x) (e.symm y)

private theorem centralizer_card_and_commutative_of_isConj {A : Type*} [Group A]
    {x y : A} (h : IsConj x y) :
    Nat.card (centralizer ({x} : Set A)) = Nat.card (centralizer ({y} : Set A)) ∧
    (IsMulCommutative (centralizer ({y} : Set A)) →
      IsMulCommutative (centralizer ({x} : Set A))) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  let e := MulAut.conj g
  have he : e x = y := hg
  let f : centralizer ({x} : Set A) ≃* centralizer ({y} : Set A) :=
    { toEquiv := Equiv.subtypeEquiv e.toEquiv (by
        intro t
        change t ∈ centralizer ({x} : Set A) ↔ e t ∈ centralizer ({y} : Set A)
        simp only [mem_centralizer_singleton_iff, ← he, ← map_mul, e.injective.eq_iff])
      map_mul' := fun a b => Subtype.ext (map_mul e (a : A) (b : A)) }
  refine ⟨Nat.card_congr f.toEquiv, fun hcomm => ?_⟩
  refine ⟨⟨fun a b => ?_⟩⟩
  apply f.injective
  simp only [map_mul]
  exact hcomm.is_comm.comm (f a) (f b)

public theorem three_centralizer_involution_structure (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer)
    (h2 : ∀ t : G, orderOf t = 2 → IsConj t D.z)
    (t : centralizer ({into D k c} : Set G)) (ht : orderOf t = 2) :
    Nat.card (centralizer ({t} : Set (centralizer ({into D k c} : Set G)))) = 12 ∧
      IsMulCommutative (centralizer ({t} : Set (centralizer ({into D k c} : Set G)))) := by
  have h := centralizer_card_and_commutative_of_isConj
    (three_centralizer_involution_fusion D k h2 t ht)
  exact ⟨h.1.trans (marked_three_involution_centralizer_card D k),
    h.2 (marked_three_involution_centralizer_commutative D k)⟩

public theorem involution_centralizer_card (D : LocalData G)
    (h2 : ∀ t : G, orderOf t = 2 → IsConj t D.z)
    (t : G) (ht : orderOf t = 2) : Nat.card (centralizer ({t} : Set G)) = 384 :=
  (centralizer_card_and_commutative_of_isConj (h2 t ht)).1.trans D.centralizer_card

public theorem not_two_dvd_centralizer_nine [Finite G] (D : LocalData G)
    (h2 : ∀ t : G, orderOf t = 2 → IsConj t D.z)
    (P : Subgroup G) (hP : Nat.card P = 9) :
    ¬2 ∣ Nat.card (centralizer (P : Set G)) := by
  intro heven
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card'
    (G := centralizer (P : Set G)) 2 heven
  have hPC : P ≤ centralizer ({(t : G)} : Set G) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr (t.property x hx)
  have hd := card_dvd_of_le hPC
  rw [hP, involution_centralizer_card D h2 t
    (by simpa only [orderOf_coe] using ht)] at hd
  norm_num at hd

end CaseII
end Theory.GroupTheory.HeldM22A10.M22Identification
