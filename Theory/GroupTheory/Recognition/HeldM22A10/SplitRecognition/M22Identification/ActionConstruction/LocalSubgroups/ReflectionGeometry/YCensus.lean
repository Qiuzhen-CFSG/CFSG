module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.LocalSubgroups.ReflectionGeometry.Basic
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.ActorCentralizers.Coverage
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.LocalSubgroups

/-!
# The complete order census of Janko's subgroup EQ*Z*

The normalizer quotient supplied by the local analysis is the actual A6
quotient. Its involution conjugacy lifts inside N(E), carrying every coset Et
for an involution t outside E to the coordinate coset Ea. A calculation on
sixteen binary vectors shows that Ea has four involutions and twelve elements
of order four. Conjugation preserves both E and element orders, so this gives
the same census in every such Et.

The reflection inverts every power of the common order-three actor. Hence the
three cosets Ew^i z all have involutory representatives outside E. The actual
multiplication bijections E × ⟨w⟩ → B and B ⊕ B → Y count these cosets without
assuming a model for Y. Adding the proved B census gives one identity,
27 involutions, 32 elements of order three and 36 elements of order four;
the same argument proves vanishing at every other order.

The final theorem applies the result to the existing LocalConfiguration
consumer. Reflection existence, the conjugate-intersection equality and the
independent X census remain with their respective source assembly owners.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 8, Lemma 17, p.17;
DOI 10.1016/0021-8693(68)90002-1.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.LocalSubgroups
open LocalModelDichotomy
local instance : DecidableEq TwistedModel := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right) SemidirectProduct.ext_iff.symm

private theorem model_fourth : ∀ v : BinaryFour,
    (SemidirectProduct.inl v * CaseII.a) ^ 4 = 1 := by decide +kernel
private theorem model_ne : ∀ v : BinaryFour,
    SemidirectProduct.inl v * CaseII.a ≠ 1 := by decide +kernel
private theorem model_square_count :
    Fintype.card {v : BinaryFour // (SemidirectProduct.inl v * CaseII.a) ^ 2 = 1} = 4 := by
  decide +kernel

private theorem model_order (v : BinaryFour) :
    orderOf (SemidirectProduct.inl v * CaseII.a) =
      if (SemidirectProduct.inl v * CaseII.a) ^ 2 = 1 then 2 else 4 := by
  split_ifs with h
  · exact orderOf_eq_prime h (model_ne v)
  · exact orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using h)
      (by simpa using model_fourth v)

private theorem model_count (n : ℕ) :
    Nat.card {v : BinaryFour // orderOf (SemidirectProduct.inl v * CaseII.a) = n} =
      if n = 2 then 4 else if n = 4 then 12 else 0 := by
  classical
  have ho2 (v : BinaryFour) :
      orderOf (SemidirectProduct.inl v * CaseII.a) = 2 ↔
        (SemidirectProduct.inl v * CaseII.a) ^ 2 = 1 := by
    rw [model_order]; split_ifs <;> simp_all
  have ho4 (v : BinaryFour) :
      orderOf (SemidirectProduct.inl v * CaseII.a) = 4 ↔
        ¬(SemidirectProduct.inl v * CaseII.a) ^ 2 = 1 := by
    rw [model_order]; split_ifs <;> simp_all
  by_cases h2 : n = 2
  · subst n
    rw [Nat.card_congr (Equiv.subtypeEquivRight ho2), Nat.card_eq_fintype_card]
    exact model_square_count
  by_cases h4 : n = 4
  · subst n
    rw [Nat.card_congr (Equiv.subtypeEquivRight ho4), Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl, model_square_count]
    decide
  have : IsEmpty {v : BinaryFour // orderOf (SemidirectProduct.inl v * CaseII.a) = n} := ⟨by
    rintro ⟨v, hv⟩
    rw [model_order] at hv
    split_ifs at hv <;> omega⟩
  simp [h2, h4]

universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

private noncomputable def binaryEquiv : BinaryFour ≃* CaseII.E D k :=
  MonoidHom.ofInjective ((CaseII.into_injective D k).comp SemidirectProduct.inl_injective)

omit [Finite G] in
private theorem coset_count_a (n : ℕ) :
    Nat.card {v : CaseII.E D k // orderOf ((v : G) * CaseII.into D k CaseII.a) = n} =
      if n = 2 then 4 else if n = 4 then 12 else 0 := by
  rw [← model_count n]
  apply Nat.card_congr
  apply (binaryEquiv D k).toEquiv.symm.subtypeEquiv
  intro v
  have he : CaseII.into D k (SemidirectProduct.inl ((binaryEquiv D k).symm v)) = (v : G) :=
    MonoidHom.apply_ofInjective_symm _ v
  change orderOf ((v : G) * CaseII.into D k CaseII.a) = n ↔
    orderOf (SemidirectProduct.inl ((binaryEquiv D k).symm v) * CaseII.a) = n
  rw [← orderOf_injective (CaseII.into D k) (CaseII.into_injective D k), map_mul, he]

private theorem coset_count (L : LocalAnalysisData D k) (t : G)
    (htN : t ∈ normalizer (CaseII.E D k : Set G)) (ht : orderOf t = 2)
    (htE : t ∉ CaseII.E D k) (n : ℕ) :
    Nat.card {v : CaseII.E D k // orderOf ((v : G) * t) = n} =
      if n = 2 then 4 else if n = 4 then 12 else 0 := by
  obtain ⟨K, hK, ⟨eK⟩⟩ := L.normalizer_E
  have hE : ENormalizerAction D k := CaseII.eNormalizerAction_of_quotient D k
    ⟨hK.symm.QuotientMulEquiv.trans eK⟩
  obtain ⟨g, hg⟩ := CaseII.normalizer_involution_outside_E_conjugate_a D k hE t htN ht htE
  rw [← coset_count_a D k n]
  apply Nat.card_congr
  apply ((CaseII.E D k).normalizerMonoidHom g).toEquiv.subtypeEquiv
  intro v
  have he : (((CaseII.E D k).normalizerMonoidHom g) v : G) * CaseII.into D k CaseII.a =
      (MulAut.conj (g : G)) ((v : G) * t) := by
    change ((g : G) * (v : G) * (g : G)⁻¹) * _ = _
    rw [← hg]
    simp only [map_mul, MulAut.conj_apply]
  change orderOf ((v : G) * t) = n ↔
    orderOf ((((CaseII.E D k).normalizerMonoidHom g) v : G) * CaseII.into D k CaseII.a) = n
  rw [he, MulEquiv.orderOf_eq]


open scoped Pointwise

variable (w : FusedNineIntersectionActor D k)

private noncomputable def BCoordinates : zpowers w.actor × CaseII.E D k ≃ B D k w := by
  let f : zpowers w.actor × CaseII.E D k → B D k w := fun x =>
    ⟨(x.2 : G) * x.1, mul_mem_sup x.2.property x.1.property⟩
  have hd : Disjoint (CaseII.E D k) (zpowers w.actor) :=
    disjoint_of_coprime_natCard (by rw [CaseII.E_card, Nat.card_zpowers, w.actor_order]; decide)
  apply Equiv.ofBijective f
  constructor
  · intro a b hab
    have he : ((a.2, a.1) : CaseII.E D k × zpowers w.actor) = (b.2, b.1) :=
      mul_injective_of_disjoint hd (congrArg Subtype.val hab)
    exact Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he)
  · intro b
    have hb : (b : G) ∈ (CaseII.E D k : Set G) * (zpowers w.actor : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ (zpowers_le.mpr w.normalizes_E)]
      exact b.property
    obtain ⟨v, hv, q, hq, he⟩ := hb
    exact ⟨(⟨q, hq⟩, ⟨v, hv⟩), Subtype.ext he⟩

private theorem reflectionCoset_count (L : LocalAnalysisData D k) (z : G)
    (hz2 : orderOf z = 2) (hzE : z ∈ normalizer (CaseII.E D k : Set G))
    (hzF : z ∉ normalizer (CaseII.F D k : Set G))
    (hinv : z * w.actor * z⁻¹ = w.actor⁻¹) (n : ℕ) :
    Nat.card {b : B D k w // orderOf ((b : G) * z) = n} =
      3 * (if n = 2 then 4 else if n = 4 then 12 else 0) := by
  classical
  let := Fintype.ofFinite (zpowers w.actor)
  have hzB : z ∉ B D k w := fun hz => hzF (B_le_normalizer_F D k w hz)
  have hc (q : zpowers w.actor) :
      Nat.card {v : CaseII.E D k // orderOf ((v : G) * ((q : G) * z)) = n} =
        if n = 2 then 4 else if n = 4 then 12 else 0 := by
    have hqE : (q : G) ∈ normalizer (CaseII.E D k : Set G) :=
      (zpowers_le.mpr w.normalizes_E) q.property
    have hqB : (q : G) ∈ B D k w := (show zpowers w.actor ≤ B D k w from le_sup_right) q.property
    have hqzB : (q : G) * z ∉ B D k w := by
      intro h
      apply hzB
      simpa using (B D k w).mul_mem ((B D k w).inv_mem hqB) h
    have hqinv : z * (q : G) * z⁻¹ = (q : G)⁻¹ := by
      obtain ⟨i, hi⟩ := q.property
      rw [← hi]
      change (MulAut.conj z) (w.actor ^ i) = (w.actor ^ i)⁻¹
      rw [map_zpow]
      change (z * w.actor * z⁻¹) ^ i = _
      rw [hinv, inv_zpow]
    have hzsq : z ^ 2 = 1 := hz2 ▸ pow_orderOf_eq_one z
    have hsq : ((q : G) * z) ^ 2 = 1 := by
      calc
        _ = (q : G) * (z * (q : G) * z⁻¹) * z ^ 2 := by simp only [pow_two]; group
        _ = 1 := by rw [hqinv, hzsq]; group
    exact coset_count D k L _ ((normalizer (CaseII.E D k : Set G)).mul_mem hqE hzE)
      (orderOf_eq_prime hsq (fun h => hqzB (h ▸ (B D k w).one_mem)))
      (fun h => hqzB ((show CaseII.E D k ≤ B D k w from le_sup_left) h)) n
  rw [← Nat.card_congr ((BCoordinates D k w).subtypeEquivOfSubtype
    (p := fun b : B D k w => orderOf ((b : G) * z) = n))]
  change Nat.card {x : zpowers w.actor × CaseII.E D k //
    orderOf ((x.2 : G) * (x.1 : G) * z) = n} = _
  simp_rw [mul_assoc]
  rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype
    (fun q v => orderOf (((v : CaseII.E D k) : G) * (((q : zpowers w.actor) : G) * z)) = n)),
    Nat.card_sigma]
  simp_rw [hc]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card,
    Nat.card_zpowers, w.actor_order]

private noncomputable def YCoordinates (z : G)
    (hz2 : orderOf z = 2) (hzE : z ∈ normalizer (CaseII.E D k : Set G))
    (hzQ : z ∈ normalizer (zpowers w.actor : Set G))
    (hzF : z ∉ normalizer (CaseII.F D k : Set G)) :
    B D k w ⊕ B D k w ≃ Y D k w z := by
  let f : B D k w ⊕ B D k w → Y D k w z := Sum.elim
    (fun b => ⟨b, (show B D k w ≤ Y D k w z from le_sup_left) b.property⟩)
    (fun b => ⟨(b : G) * z, mul_mem_sup b.property (mem_zpowers z)⟩)
  have hzB : z ∉ B D k w := fun hz => hzF (B_le_normalizer_F D k w hz)
  have hcross (b c : B D k w) : (b : G) ≠ (c : G) * z := by
    intro h
    apply hzB
    have hm := (B D k w).mul_mem ((B D k w).inv_mem c.property) b.property
    simpa [h] using hm
  apply Equiv.ofBijective f
  constructor
  · intro a b h
    have he := congrArg Subtype.val h
    cases a with
    | inl a => cases b with
      | inl b => exact congrArg Sum.inl (Subtype.ext he)
      | inr b => exact (hcross a b he).elim
    | inr a => cases b with
      | inl b => exact (hcross b a he.symm).elim
      | inr b => exact congrArg Sum.inr (Subtype.ext (mul_right_cancel he))
  · intro y
    rcases (mem_Y_iff D k w z hz2 hzE hzQ y).mp y.property with hy | ⟨b, hb, he⟩
    · exact ⟨Sum.inl ⟨y, hy⟩, rfl⟩
    · exact ⟨Sum.inr ⟨b, hb⟩, Subtype.ext he⟩

/-- The complete order census of the literal subgroup EQ*Z* in Janko's Lemma 17. -/
public theorem Y_count_of_reflection (L : LocalAnalysisData D k) (z : G)
    (hz2 : orderOf z = 2) (hzE : z ∈ normalizer (CaseII.E D k : Set G))
    (hzQ : z ∈ normalizer (zpowers w.actor : Set G))
    (hzF : z ∉ normalizer (CaseII.F D k : Set G))
    (hinv : z * w.actor * z⁻¹ = w.actor⁻¹) (n : ℕ) :
    Nat.card {y : Y D k w z // orderOf y = n} = localOrderCount 27 32 36 0 n := by
  have hc := Nat.card_congr ((YCoordinates D k w z hz2 hzE hzQ hzF).subtypeEquivOfSubtype
    (p := fun y : Y D k w z => orderOf (y : G) = n))
  rw [Nat.card_congr Equiv.subtypeSum, Nat.card_sum] at hc
  change Nat.card {b : B D k w // orderOf (b : G) = n} +
    Nat.card {b : B D k w // orderOf ((b : G) * z) = n} =
    Nat.card {y : Y D k w z // orderOf (y : G) = n} at hc
  simp_rw [orderOf_coe] at hc
  rw [← hc, B_count, reflectionCoset_count D k w L z hz2 hzE hzF hinv]
  unfold localOrderCount
  split_ifs <;> omega

/-- Apply the census to the existing local-configuration consumer. Only the
independent X census and conjugate-intersection equality remain explicit. -/
public theorem localConfiguration_of_reflection_with_Y_census
    (L : LocalAnalysisData D k) (z : G)
    (hz2 : orderOf z = 2) (hzE : z ∈ normalizer (CaseII.E D k : Set G))
    (hzQ : z ∈ normalizer (zpowers w.actor : Set G))
    (hzF : z ∉ normalizer (CaseII.F D k : Set G))
    (hinv : z * w.actor * z⁻¹ = w.actor⁻¹)
    (hinter : X D k ⊓ (X D k).map (MulAut.conj z).toMonoidHom = B D k w)
    (hXcount : ∀ n : ℕ, Nat.card {x : X D k // orderOf x = n} =
      localOrderCount 75 320 180 384 n) : Nonempty (LocalConfiguration G) :=
  localConfiguration_of_reflection D k L w z hzF hinter hXcount
    (Y_card_of_reflection D k w z hz2 hzE hzQ hzF)
    (Y_count_of_reflection D k w L z hz2 hzE hzQ hzF hinv)

end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.LocalSubgroups
