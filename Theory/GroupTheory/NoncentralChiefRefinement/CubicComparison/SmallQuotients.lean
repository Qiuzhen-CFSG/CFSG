module

public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.Count
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.Actor
public import Theory.GroupTheory.NoncentralChiefRefinement.fourGroup
public import Theory.GroupTheory.NoncentralChiefRefinement.ResidualRestriction.Transport

/-!
# Chief counts above symmetric-three and alternating-four quotients

For an actual cubic subgroup above a normal two-kernel, the complete chief
count is the cubic fixed index on the kernel in the symmetric-three case.
The alternating-four case contributes one further factor, its normal Klein
four-group. These formulas retain the original cubic subgroup, so they can
be compared inside a common ambient group.

Source application: Aschbacher–Smith, 13.7.10(8), printed p.942.
-/

@[expose] public section
open Subgroup
namespace NoncentralChiefRefinement.CubicComparison
variable {G K : Type*} [Group G] [Finite G] [Group K] [Finite K]

omit [Finite G] in
/-- Changing to an overgroup preserves the literal relative fixed index. -/
theorem length_subgroupOf (A R H : Subgroup G) (hAH : A ≤ H) (hRH : R ≤ H) :
    conjugationCubicLength (A.subgroupOf H) (R.subgroupOf H) =
      conjugationCubicLength A R := by
  have hc : centralizer (A.subgroupOf H : Set H) =
      (centralizer (A : Set G)).comap H.subtype := by
    ext x
    constructor
    · intro hx a ha
      exact congrArg Subtype.val (hx ⟨a,hAH ha⟩ ha)
    · intro hx a ha
      exact Subtype.ext (hx a ha)
  unfold conjugationCubicLength
  rw [hc, relIndex_comap, map_subgroupOf_eq_of_le hRH]

/-- Every complete chief series above a symmetric-three quotient has precisely
its kernel's cubic fixed length. -/
theorem symmetricThree_count (f : G →* Equiv.Perm (Fin 3))
    (hf : Function.Surjective f) (hp : IsPGroup 2 f.ker)
    (A : Subgroup G) (hA : Nat.card A = 3)
    (s : ChiefSeries G) (h0 : s.head = ⊥) (h1 : s.last = ⊤) :
    s.noncentralTwoCount = conjugationCubicLength A f.ker := by
  let X := A.map f
  have hX : Nat.card X = 3 := GLS3.Chapter5.cubic_image_card_of_two_kernel f hp A hA
  have hi : X.index = 2 := by
    have hc := X.card_mul_index
    rw [hX] at hc
    have hg : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm]
      decide
    rw [hg] at hc
    omega
  let : X.Normal := normal_of_index_eq_two hi
  have hq : IsPGroup 2 ((Equiv.Perm (Fin 3)) ⧸ X) :=
    IsPGroup.of_card (n := 1) (by simp only [← index_eq_card, hi, pow_one])
  have hterm : HasCentralPChiefFactors 2 (G ⧸ f.ker) :=
    centralTwoChiefFactors_of_not_four_dvd (by
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv,
        Nat.card_eq_fintype_card, Fintype.card_perm]
      decide)
  exact complete_count_eq_length (f := f) (X := X) (A := A) f.ker hp hf hp hX hq
    (IsPGroup.of_card (n := 1) (by simpa using hA)) rfl hterm s h0 h1

open GLS3.Chapter5

private theorem alternatingFour_quotient_card :
    Nat.card ((alternatingGroup (Fin 4)) ⧸ alternatingFourKlein) = 3 := by
  have hc := alternatingFourKlein.card_mul_index
  rw [alternatingFourKlein_card, index_eq_card, nat_card_alternatingGroup] at hc
  norm_num at hc ⊢
  omega

private theorem klein_fixed (B : Subgroup (alternatingGroup (Fin 4)))
    (hB : Nat.card B = 3) (u : alternatingFourKlein)
    (hu : ∀ b ∈ B, b * (u : alternatingGroup (Fin 4)) * b⁻¹ = u) : u = 1 := by
  let C := (centralizer (B : Set (alternatingGroup (Fin 4)))).subgroupOf alternatingFourKlein
  have hc := cubic_length_one_of_card_three B hB
  change Nat.log 4 C.index = 1 at hc
  have hge := Nat.pow_log_le_self 4 (Subgroup.FiniteIndex.index_ne_zero (H := C))
  rw [hc] at hge
  have hcard := C.card_mul_index
  rw [alternatingFourKlein_card] at hcard
  have hpos : 0 < Nat.card C := Nat.card_pos
  have hC : C = ⊥ := eq_bot_of_card_eq C (by nlinarith)
  have huC : u ∈ C := by
    intro b hb
    exact mul_inv_eq_iff_eq_mul.mp (hu b hb)
  rwa [hC, mem_bot] at huC

/-- The normal Klein four-group contributes exactly one to cubic fixed length
above the actual kernel of an alternating-four quotient. -/
theorem alternatingFour_kernel_length (f : G →* alternatingGroup (Fin 4))
    (hf : Function.Surjective f) (hp : IsPGroup 2 f.ker)
    (A : Subgroup G) (hA : Nat.card A = 3) :
    conjugationCubicLength A (alternatingFourKlein.comap f) =
      conjugationCubicLength A f.ker + 1 := by
  let P := alternatingFourKlein.comap f
  have hP : IsPGroup 2 P :=
    (IsPGroup.of_card (p := 2) (n := 2) alternatingFourKlein_card).comap_of_ker_isPGroup f hp
  have hAP : A ≤ normalizer (P : Set G) := le_normalizer_of_normal
  have hAN : A ≤ normalizer (f.ker : Set G) := le_normalizer_of_normal
  have hNP : f.ker ≤ P := ker_le_comap f alternatingFourKlein
  let φ : P →* alternatingFourKlein :=
    { toFun := fun x => ⟨f x, x.property⟩
      map_one' := Subtype.ext f.map_one
      map_mul' := fun x y => Subtype.ext (f.map_mul x y) }
  have hφ : Function.Surjective φ := by
    intro u
    obtain ⟨x,hx⟩ := hf u
    exact ⟨⟨x, by change f x ∈ alternatingFourKlein; rw [hx]; exact u.property⟩,
      Subtype.ext hx⟩
  have hk : f.ker.subgroupOf P = φ.ker := by
    ext x
    change f (x : G) = 1 ↔ φ x = 1
    constructor
    · exact fun hx => Subtype.ext hx
    · exact fun hx => congrArg (fun u : alternatingFourKlein => (u : alternatingGroup (Fin 4))) hx
  let e : (P ⧸ f.ker.subgroupOf P) ≃* alternatingFourKlein :=
    QuotientGroup.liftEquiv _ hφ hk
  let := quotientConjugationAction A P f.ker hAP hAN
  have he (a : A) (x : P ⧸ f.ker.subgroupOf P) :
      (e (a • x) : alternatingGroup (Fin 4)) =
        f a * (e x : alternatingGroup (Fin 4)) * (f a)⁻¹ := by
    obtain ⟨p,rfl⟩ := QuotientGroup.mk'_surjective (f.ker.subgroupOf P) x
    change f ((a : G) * (p : G) * (a : G)⁻¹) = f a * f p * (f a)⁻¹
    simp only [map_mul, map_inv]
  have hfix : FixedPoints.subgroup A (P ⧸ f.ker.subgroupOf P) = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    apply e.injective
    rw [map_one]
    apply klein_fixed (A.map f) (GLS3.Chapter5.cubic_image_card_of_two_kernel f hp A hA) (e x)
    rintro _ ⟨a,ha,rfl⟩
    rw [← he ⟨a,ha⟩ x, hx ⟨a,ha⟩]
  have hsection : sectionCubicLength A f.ker P = 1 := by
    rw [sectionCubicLength_eq_quotient_of_twoGroup A P f.ker
      (IsPGroup.of_card (n := 1) (by simpa using hA)) hP hNP hAP hAN]
    unfold FixedPoints.cubicLength
    rw [hfix, index_bot, Nat.card_congr e.toEquiv, alternatingFourKlein_card]
    decide
  have hmono := conjugationCubicLength_mono A hNP
  unfold sectionCubicLength at hsection
  change conjugationCubicLength A P = conjugationCubicLength A f.ker + 1
  omega

/-- A complete chief series above an alternating-four quotient has one more
noncentral binary factor than the cubic length on the original kernel. -/
theorem alternatingFour_count (f : G →* alternatingGroup (Fin 4))
    (hf : Function.Surjective f) (hp : IsPGroup 2 f.ker)
    (A : Subgroup G) (hA : Nat.card A = 3)
    (s : ChiefSeries G) (h0 : s.head = ⊥) (h1 : s.last = ⊤) :
    s.noncentralTwoCount = conjugationCubicLength A f.ker + 1 := by
  let K := (alternatingGroup (Fin 4)) ⧸ alternatingFourKlein
  let q : G →* K := (QuotientGroup.mk' alternatingFourKlein).comp f
  have hq : Function.Surjective q := (QuotientGroup.mk'_surjective _).comp hf
  have hk : q.ker = alternatingFourKlein.comap f := by
    ext x
    exact QuotientGroup.eq_one_iff (f x)
  have hpq : IsPGroup 2 q.ker := by
    rw [hk]
    exact (IsPGroup.of_card (p := 2) (n := 2) alternatingFourKlein_card).comap_of_ker_isPGroup f hp
  have hX : Nat.card (⊤ : Subgroup K) = 3 := by
    rw [card_top]
    exact alternatingFour_quotient_card
  have hAX : A.map q = ⊤ := eq_of_le_of_card_ge le_top
    (by rw [GLS3.Chapter5.cubic_image_card_of_two_kernel q hpq A hA, hX])
  have htop : IsPGroup 2 (K ⧸ (⊤ : Subgroup K)) := IsPGroup.of_card (n := 0) (by simp)
  have hterm : HasCentralPChiefFactors 2 (G ⧸ q.ker) :=
    centralTwoChiefFactors_of_not_four_dvd (by
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective q hq).toEquiv,
        alternatingFour_quotient_card]
      decide)
  have hc := complete_count_eq_length (f := q) (X := (⊤ : Subgroup K)) (A := A)
    q.ker hpq hq hpq hX htop (IsPGroup.of_card (n := 1) (by simpa using hA))
    hAX hterm s h0 h1
  rw [hk, alternatingFour_kernel_length f hf hp A hA] at hc
  exact hc

end NoncentralChiefRefinement.CubicComparison
