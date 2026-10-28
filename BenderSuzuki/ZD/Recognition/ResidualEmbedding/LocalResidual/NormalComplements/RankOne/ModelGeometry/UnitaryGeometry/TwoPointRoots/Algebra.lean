module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.Basic
public import BenderSuzuki.SE.Proposition84Torus
public import BenderSuzuki.SE.StrongEmbeddingIntersections
public import Theory.GroupTheory.FixedInvertedFactorization

/-!
# Commutators and fixed factors of a two-point subgroup

If the elements of a subgroup inverted by an involution form an odd-order
subgroup T, then T is the literal commutator with that involution. Each
commutator generator is inverted; conversely an inverted element is a
commutator square and odd order makes squaring surjective. Fixed/inverted
factorization supplies the exact fixed-subgroup cardinality. The lifting
lemma keeps an arbitrary surjection and its central odd kernel explicit.

The projective and special unitary applications are in ProjectiveTori and
SpecialCommutators. Source: GLS4, Chapter 4, Lemma 3.2(d),(e), and the
odd central-cover usage in Chapter 2, Section 16.
-/

open Subgroup BenderSuzuki BenderSuzuki.PFAppendixIII BenderSuzuki.PFchapter1section1
open scoped commutatorElement
namespace BenderSuzuki.ZD.RankOneModelGeometry
variable {G : Type*} [Group G] [Finite G]

public theorem commutator_eq_of_inverted (D T : Subgroup G) (t : G)
    (ht : IsInvolution t) (htD : t ∈ normalizer D)
    (hT : ∀ x, x ∈ T ↔ x ∈ D ∧ rightConjugateElem x t = x⁻¹)
    (hodd : Odd (Nat.card T)) : ⁅D, zpowers t⁆ = T := by
  classical
  apply le_antisymm
  · rw [commutator_le]
    intro x hx s hs
    have horder : orderOf t = 2 := (orderOf_eq_prime_iff).2 ⟨ht.sq_eq_one, ht.ne_one⟩
    rw [mem_zpowers_iff_mem_range_orderOf, horder] at hs
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hs
    have hklt := Finset.mem_range.mp hk
    interval_cases k
    · simp
    · simp only [pow_one]
      apply (hT _).mpr
      refine ⟨le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr htD)
        (commutator_mem_commutator hx (mem_zpowers t)), ?_⟩
      have htt : t * t = 1 := by simpa [pow_two] using ht.sq_eq_one
      simp only [rightConjugateElem, commutatorElement_def, mul_inv_rev, inv_inv,
        ht.inv_eq_self, mul_assoc, htt, mul_one]
  · intro x hx
    obtain ⟨y, hy⟩ := hodd.coprime_two_right.pow_left_bijective.surjective (⟨x, hx⟩ : T)
    have hysq : (y : G) ^ 2 = x := congrArg Subtype.val hy
    have hyinv := ((hT y).mp y.property).2
    have he : ⁅(y : G),t⁆ = (y : G)^2 := by
      calc
        ⁅(y : G),t⁆ = (y : G) * (t⁻¹ * (y : G) * t)⁻¹ := by
          simp [commutatorElement_def, ht.inv_eq_self, mul_assoc]
        _ = (y : G)^2 := by rw [show t⁻¹ * (y : G) * t = (y : G)⁻¹ from hyinv, inv_inv, pow_two]
    rw [← hysq, ← he]
    exact commutator_mem_commutator ((hT y).mp y.property).1 (mem_zpowers t)

public theorem twoPoint_commutator_of_inverted (B T : Subgroup G) (t : G)
    (ht : IsInvolution t)
    (hT : (T : Set G) = {x | x ∈ B ∧ x ∈ rightConjugate B t ∧ rightConjugateElem x t = x⁻¹})
    (hodd : Odd (Nat.card T)) : ⁅twoPoint B t, zpowers t⁆ = T := by
  apply commutator_eq_of_inverted (twoPoint B t) T t ht
    (inf_rightConjugate_mem_normalizer_of_isInvolution B ht)
  · intro x
    rw [show x ∈ T ↔ x ∈ B ∧ x ∈ rightConjugate B t ∧ rightConjugateElem x t = x⁻¹ from Set.ext_iff.mp hT x]
    exact and_assoc.symm
  · exact hodd


public theorem card_fixed_mul_inverted (D T : Subgroup G) (t : G)
    (ht : IsInvolution t) (htD : t ∈ normalizer D) (hodd : Odd (Nat.card D))
    (hT : ∀ x, x ∈ T ↔ x ∈ D ∧ rightConjugateElem x t = x⁻¹) :
    Nat.card D = Nat.card (D ⊓ centralizer ({t} : Set G) : Subgroup G) * Nat.card T := by
  let a : MulAut D := D.normalizerMonoidHom ⟨t, htD⟩
  have ha (x : D) : (a x : G) = rightConjugateElem (x : G) t := by
    change t * (x : G) * t⁻¹ = t⁻¹ * (x : G) * t
    rw [ht.inv_eq_self]
  have hai : Function.Involutive a := by
    intro x
    apply Subtype.ext
    rw [ha, ha]
    have htt : t * t = 1 := by simpa [pow_two] using ht.sq_eq_one
    simp only [rightConjugateElem, ht.inv_eq_self]
    calc
      _ = (t * t) * (x : G) * (t * t) := by group
      _ = (x : G) := by rw [htt]; simp
  let C := D ⊓ centralizer ({t} : Set G)
  let f : C × T → D := fun p => ⟨p.1.val * p.2.val,
    D.mul_mem p.1.property.1 ((hT _).mp p.2.property).1⟩
  have hfix (c : C) : a ⟨c.val, c.property.1⟩ = ⟨c.val, c.property.1⟩ := by
    apply Subtype.ext
    rw [ha]
    have hc := mem_centralizer_singleton_iff.mp c.property.2
    simp only [rightConjugateElem]
    rw [mul_assoc, hc, inv_mul_cancel_left]
  have hinv (i : T) : a ⟨i.val, ((hT _).mp i.property).1⟩ =
      (⟨i.val, ((hT _).mp i.property).1⟩ : D)⁻¹ := by
    apply Subtype.ext
    rw [ha]
    exact ((hT _).mp i.property).2
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨u,v⟩ ⟨u',v'⟩ he
      obtain ⟨p, _, hu⟩ := Theory.GroupTheory.existsUnique_fixed_inverted_mul_of_odd_card
        hodd a hai (f (u,v))
      have h1 := hu (⟨u.val,u.property.1⟩, ⟨v.val,((hT _).mp v.property).1⟩)
        ⟨hfix u, hinv v, rfl⟩
      have h2 := hu (⟨u'.val,u'.property.1⟩, ⟨v'.val,((hT _).mp v'.property).1⟩)
        ⟨hfix u', hinv v', he.symm⟩
      have hh := h1.trans h2.symm
      exact Prod.ext (Subtype.ext (congrArg (fun z : D × D => (z.1:G)) hh))
        (Subtype.ext (congrArg (fun z : D × D => (z.2:G)) hh))
    · intro x
      obtain ⟨⟨u,v⟩,⟨hu,hv,he⟩,_⟩ :=
        Theory.GroupTheory.existsUnique_fixed_inverted_mul_of_odd_card hodd a hai x
      have hc : (u : G) ∈ centralizer ({t} : Set G) := by
        rw [mem_centralizer_singleton_iff]
        have hh := congrArg Subtype.val hu
        rw [ha] at hh
        change t⁻¹ * (u : G) * t = (u : G) at hh
        exact inv_mul_eq_iff_eq_mul.mp (by simpa [mul_assoc] using hh)
      exact ⟨(⟨u,u.property,hc⟩,
        ⟨v,(hT _).mpr ⟨v.property, by simpa only [ha, Subgroup.coe_inv] using congrArg Subtype.val hv⟩⟩),he⟩
  exact (Nat.card_eq_of_bijective f hf).symm.trans (Nat.card_prod _ _)


public theorem invertedTorus_lift_surjective {H : Type*} [Group H]
    (f : G →* H) (hf : Function.Surjective f)
    (hcentral : f.ker ≤ center G) (hodd : Odd (Nat.card f.ker))
    (t : G) (T : Subgroup H) (hc : IsCyclic T)
    (hi : ∀ y ∈ T, rightConjugateElem y (f t) = y⁻¹) :
    ∃ L : Subgroup G, (∀ x, x ∈ L ↔ f x ∈ T ∧ rightConjugateElem x t = x⁻¹) ∧
      IsCyclic L ∧ Nat.card L = Nat.card T := by
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  have he (x : G) : e (QuotientGroup.mk' f.ker x) = f x := rfl
  let S := T.map e.symm.toMonoidHom
  have hS (y : G ⧸ f.ker) : y ∈ S ↔ e y ∈ T := by
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, SetLike.mem_coe] using hx
    · intro hy
      exact ⟨e y, hy, e.symm_apply_apply y⟩
  let eS := T.equivMapOfInjective e.symm.toMonoidHom e.symm.injective
  have hiS (y : G ⧸ f.ker) (hy : y ∈ S) :
      rightConjugateElem y (QuotientGroup.mk' f.ker t) = y⁻¹ := by
    apply e.injective
    simpa only [rightConjugateElem, map_mul, map_inv, he] using hi (e y) ((hS y).mp hy)
  obtain ⟨L, hL, hcL, hcardL⟩ := invertedTorus_lift_of_central_odd_kernel f.ker
    hcentral hodd t S (eS.isCyclic.mp hc) hiS
  refine ⟨L, ?_, hcL, hcardL.trans (Nat.card_congr eS.toEquiv.symm)⟩
  intro x
  change x ∈ (L : Set G) ↔ _
  rw [hL]
  change (QuotientGroup.mk' f.ker x ∈ S ∧ _) ↔ _
  rw [hS]
  rfl


end BenderSuzuki.ZD.RankOneModelGeometry
