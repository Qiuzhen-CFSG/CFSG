import Submission.ZStar.CentralIdempotentSupport
import Submission.ZStar.DefectSupport
import Submission.ZStar.AugmentationScratch

/-!
# Subgroup Brauer restriction

This file contains the finite-orbit calculation behind the subgroup form of
the Brauer map.  It is independent of block theory: a `p`-subgroup acting by
conjugation has only singleton orbits surviving in characteristic `p`.
-/

noncomputable section

open scoped BigOperators

namespace Submission.ZStar
namespace SubgroupBrauerMap

universe u v w

attribute [local instance] Fintype.ofFinite

/-- Weighted orbit cancellation for an arbitrary finite action of a finite
`p`-group.  In characteristic `p`, an invariant sum is supported on the fixed
points of the action. -/
theorem sum_eq_sum_fixedPoints_of_smul_invariant
    {p : ℕ} [Fact p.Prime]
    {R : Type u} [CommRing R] [CharP R p]
    {P : Type v} [Group P] [Finite P]
    (hP : IsPGroup p P)
    {α : Type w} [MulAction P α] [Finite α]
    (F : α → R)
    (hF : ∀ q : P, ∀ x : α, F (q • x) = F x) :
    ∑ x : α, F x = ∑ x : MulAction.fixedPoints P α, F x := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  letI : Fintype (MulAction.fixedPoints P α) := Fintype.ofFinite _
  letI : Fintype (MulAction.orbitRel.Quotient P α) := Fintype.ofFinite _
  let g : α → MulAction.orbitRel.Quotient P α := Quotient.mk''
  have hpartition :
      (∑ y : MulAction.orbitRel.Quotient P α,
        ∑ x : {x : α // g x = y}, F x) = ∑ x : α, F x := by
    exact Fintype.sum_fiberwise g F
  rw [← hpartition]
  have hkey : ∀ x : α,
      Fintype.card {y : α // g y = g x} =
        Fintype.card (MulAction.orbit P x) := by
    intro x
    simp only [g, Quotient.eq'']
    congr
  have hfiber_mk (x : α) :
      (∑ y : {y : α // g y = g x}, F y) =
        if x ∈ MulAction.fixedPoints P α then F x else 0 := by
    have hconst (y : {y : α // g y = g x}) : F y = F x := by
      have hy : MulAction.orbitRel P α y.1 x := Quotient.exact' y.2
      rcases hy with ⟨q, hqx⟩
      rw [← hqx]
      exact hF q x
    have hsum :
        (∑ y : {y : α // g y = g x}, F y) =
          (Fintype.card {y : α // g y = g x} : R) * F x := by
      calc
        (∑ y : {y : α // g y = g x}, F y) =
            ∑ _y : {y : α // g y = g x}, F x := by
          apply Fintype.sum_congr
          exact hconst
        _ = (Fintype.card {y : α // g y = g x} : R) * F x := by
          simp [nsmul_eq_mul]
    by_cases hfixed : x ∈ MulAction.fixedPoints P α
    · have hcard : Fintype.card {y : α // g y = g x} = 1 := by
        rw [hkey x]
        exact MulAction.mem_fixedPoints_iff_card_orbit_eq_one.mp hfixed
      rw [hsum, hcard]
      simp [hfixed]
    · obtain ⟨k, hk⟩ := hP.card_orbit x
      have hk' : Fintype.card (MulAction.orbit P x) = p ^ k := by
        simpa [Nat.card_eq_fintype_card] using hk
      have hk0 : k ≠ 0 := by
        intro hk0
        apply hfixed
        rw [MulAction.mem_fixedPoints_iff_card_orbit_eq_one, hk', hk0,
          pow_zero]
      have hpdivOrbit : p ∣ Fintype.card (MulAction.orbit P x) := by
        rw [hk']
        exact dvd_pow_self p hk0
      have hpdivFiber : p ∣ Fintype.card {y : α // g y = g x} := by
        rw [hkey x]
        exact hpdivOrbit
      have hcast : (Fintype.card {y : α // g y = g x} : R) = 0 :=
        (CharP.cast_eq_zero_iff R p _).mpr hpdivFiber
      rw [hsum, hcast]
      simp [hfixed]
  let orbitSum : MulAction.orbitRel.Quotient P α → R := fun y =>
    ∑ x : {x : α // g x = y}, F x
  have hinj : ∀
      (a₁ : MulAction.fixedPoints P α) (_ha₁ : a₁ ∈ Finset.univ)
        (_hne₁ : F a₁ ≠ 0)
      (a₂ : MulAction.fixedPoints P α) (_ha₂ : a₂ ∈ Finset.univ)
        (_hne₂ : F a₂ ≠ 0),
      g a₁.1 = g a₂.1 → a₁ = a₂ := by
    intro a₁ _ _ a₂ _ _ h
    apply Subtype.ext
    exact (MulAction.mem_fixedPoints'.mp a₂.2) a₁.1 (Quotient.exact' h)
  have hsurj : ∀ y : MulAction.orbitRel.Quotient P α,
      y ∈ Finset.univ → orbitSum y ≠ 0 →
        ∃ a : MulAction.fixedPoints P α,
          ∃ ha : a ∈ Finset.univ,
            ∃ hne : F a ≠ 0, g a.1 = y := by
    intro y
    induction y using Quotient.inductionOn' with
    | _ x =>
        intro _ hy
        change orbitSum (g x) ≠ 0 at hy
        have hsum : orbitSum (g x) =
            if x ∈ MulAction.fixedPoints P α then F x else 0 := by
          simpa [orbitSum] using hfiber_mk x
        by_cases hfixed : x ∈ MulAction.fixedPoints P α
        · refine ⟨⟨x, hfixed⟩, Finset.mem_univ _, ?_, rfl⟩
          rw [hsum, if_pos hfixed] at hy
          exact hy
        · rw [hsum, if_neg hfixed] at hy
          exact (hy rfl).elim
  have hvalue : ∀
      (a : MulAction.fixedPoints P α) (_ha : a ∈ Finset.univ)
        (_hne : F a ≠ 0),
      F a = orbitSum (g a.1) := by
    intro a _ _
    simpa [orbitSum, a.2] using (hfiber_mk a.1).symm
  exact Eq.symm (Finset.sum_bij_ne_zero
    (s := (Finset.univ : Finset (MulAction.fixedPoints P α)))
    (t := (Finset.univ : Finset (MulAction.orbitRel.Quotient P α)))
    (f := fun a : MulAction.fixedPoints P α => F a)
    (g := orbitSum)
    (fun a _ _ => g a.1)
    (fun _ _ _ => Finset.mem_univ _)
    hinj hsurj hvalue)

/-- The action of a subgroup on the ambient group by conjugation.  It is kept
as an explicit local instance so it does not compete with other actions on
the same types. -/
@[reducible] private def subgroupConjugationMulAction
    {G : Type v} [Group G] (Q : Subgroup G) : MulAction Q G where
  smul q g := (q : G) * g * (q : G)⁻¹
  one_smul g := by
    change (1 : G) * g * (1 : G)⁻¹ = g
    group
  mul_smul q r g := by
    change ((q * r : Q) : G) * g * ((q * r : Q) : G)⁻¹ =
      (q : G) * ((r : G) * g * (r : G)⁻¹) * (q : G)⁻¹
    simp only [Subgroup.coe_mul]
    group

private theorem monoidAlgebra_mul_apply_eq_sum
    {R : Type u} {G : Type v} [Semiring R] [Group G] [Finite G]
    (a b : MonoidAlgebra R G) (h : G) :
    (a * b) h = ∑ g : G, a g * b (g⁻¹ * h) := by
  rw [MonoidAlgebra.mul_apply_left]
  exact Finsupp.sum_fintype a
    (fun g r => r * b (g⁻¹ * h)) (by simp)

/-- The fixed points of subgroup conjugation are the elements of the subgroup
centralizer. -/
private noncomputable def fixedPointsEquivCentralizer
    {G : Type v} [Group G] (Q : Subgroup G) :
    letI : MulAction Q G := subgroupConjugationMulAction Q
    MulAction.fixedPoints Q G ≃ Subgroup.centralizer (Q : Set G) := by
  letI : MulAction Q G := subgroupConjugationMulAction Q
  exact
    { toFun := fun g => ⟨g, by
          rw [Subgroup.mem_centralizer_iff]
          intro q hq
          let qQ : Q := ⟨q, hq⟩
          have hfixed := g.2 qQ
          change (qQ : G) * (g : G) * (qQ : G)⁻¹ = (g : G) at hfixed
          calc
            q * (g : G) = ((qQ : G) * (g : G) * (qQ : G)⁻¹) * q := by
              simp only [qQ]
              group
            _ = (g : G) * q := by rw [hfixed] ⟩
      invFun := fun g => ⟨g, by
          intro q
          change (q : G) * (g : G) * (q : G)⁻¹ = (g : G)
          have hcomm : (q : G) * (g : G) = (g : G) * (q : G) :=
            Subgroup.mem_centralizer_iff.mp g.2 (q : G) q.2
          rw [hcomm]
          simp ⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- Weighted orbit cancellation for subgroup conjugation.  In characteristic
`p`, a conjugation-invariant sum over `G` equals its restriction to
`C_G(Q)` whenever `Q` is a `p`-subgroup. -/
theorem sum_eq_sum_subgroupCentralizer_of_conj_invariant
    {p : ℕ} [Fact p.Prime]
    {R : Type u} [CommRing R] [CharP R p]
    {G : Type v} [Group G] [Finite G]
    (Q : Subgroup G) (hQ : IsPGroup p Q)
    (F : G → R)
    (hF : ∀ q : Q, ∀ g : G,
      F ((q : G) * g * (q : G)⁻¹) = F g) :
    ∑ g : G, F g =
      ∑ h : Subgroup.centralizer (Q : Set G), F (h : G) := by
  letI : MulAction Q G := subgroupConjugationMulAction Q
  calc
    ∑ g : G, F g =
        ∑ g : MulAction.fixedPoints Q G, F (g : G) :=
      sum_eq_sum_fixedPoints_of_smul_invariant hQ F (by
        intro q g
        exact hF q g)
    _ = ∑ h : Subgroup.centralizer (Q : Set G), F (h : G) := by
      exact Equiv.sum_comp (fixedPointsEquivCentralizer Q)
        (fun h : Subgroup.centralizer (Q : Set G) => F (h : G))

/-- The subgroup Brauer calculation: in characteristic `p`, coefficient
restriction to `C_G(Q)` preserves products of central group-algebra elements
for every `p`-subgroup `Q`. -/
theorem subgroupCentralizerRestriction_mul_of_mem_center
    {p : ℕ} [Fact p.Prime]
    {R : Type u} [CommRing R] [CharP R p]
    {G : Type v} [Group G] [Finite G]
    (Q : Subgroup G) (hQ : IsPGroup p Q)
    (a b : MonoidAlgebra R G)
    (ha : a ∈ Set.center (MonoidAlgebra R G))
    (hb : b ∈ Set.center (MonoidAlgebra R G)) :
    DefectSupport.subgroupCentralizerRestriction R Q (a * b) =
      DefectSupport.subgroupCentralizerRestriction R Q a *
        DefectSupport.subgroupCentralizerRestriction R Q b := by
  classical
  ext h
  rw [DefectSupport.subgroupCentralizerRestriction_apply,
    monoidAlgebra_mul_apply_eq_sum,
    monoidAlgebra_mul_apply_eq_sum]
  simp only [DefectSupport.subgroupCentralizerRestriction_apply,
    Subgroup.coe_inv, Subgroup.coe_mul]
  let F : G → R := fun g => a g * b (g⁻¹ * (h : G))
  have hF : ∀ q : Q, ∀ g : G,
      F ((q : G) * g * (q : G)⁻¹) = F g := by
    intro q g
    have haCoeff :=
      CentralIdempotentSupport.coeff_conj_eq_of_mem_center
        a ha (q : G) g
    have hcomm : (q : G) * (h : G) = (h : G) * (q : G) :=
      Subgroup.mem_centralizer_iff.mp h.2 (q : G) q.2
    have hcommInv : (q : G)⁻¹ * (h : G) = (h : G) * (q : G)⁻¹ :=
      (show Commute (q : G) (h : G) from hcomm).inv_left.eq
    have harg :
        ((q : G) * g * (q : G)⁻¹)⁻¹ * (h : G) =
          (q : G) * (g⁻¹ * (h : G)) * (q : G)⁻¹ := by
      simp only [mul_inv_rev, inv_inv, mul_assoc]
      rw [hcommInv]
    have hbCoeff :=
      CentralIdempotentSupport.coeff_conj_eq_of_mem_center
        b hb (q : G) (g⁻¹ * (h : G))
    dsimp [F]
    rw [haCoeff, harg, hbCoeff]
  have hsum := sum_eq_sum_subgroupCentralizer_of_conj_invariant
    Q hQ F hF
  simpa only [F] using hsum

/-- Coefficient restriction sends the unit to the unit.  This part does not
use the `p`-subgroup hypothesis. -/
@[simp] theorem subgroupCentralizerRestriction_one
    {R : Type u} {G : Type v} [Semiring R] [Group G]
    (Q : Subgroup G) :
    DefectSupport.subgroupCentralizerRestriction R Q
        (1 : MonoidAlgebra R G) = 1 := by
  classical
  ext h
  change (Finsupp.single 1 1 : G →₀ R) (h : G) =
    (Finsupp.single 1 1 :
      Subgroup.centralizer (Q : Set G) →₀ R) h
  simp only [Finsupp.single_apply]
  congr 1
  apply propext
  constructor
  · intro hh
    apply Subtype.ext
    simpa using hh
  · intro hh
    subst h
    rfl

/-- Restricting the coefficients of a central group-algebra element to the
centralizer of a subgroup again gives a central element. -/
theorem subgroupCentralizerRestriction_mem_center
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (Q : Subgroup G) (e : MonoidAlgebra R G)
    (he : e ∈ Set.center (MonoidAlgebra R G)) :
    DefectSupport.subgroupCentralizerRestriction R Q e ∈
      Set.center
        (MonoidAlgebra R (Subgroup.centralizer (Q : Set G))) := by
  classical
  apply Semigroup.mem_center_iff.mpr
  intro a
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [mul_add, add_mul, ha, hb]
  | single x r =>
      ext h
      rw [MonoidAlgebra.single_mul_apply,
        MonoidAlgebra.mul_single_apply]
      simp only [DefectSupport.subgroupCentralizerRestriction_apply]
      have hcoeff :=
        CentralIdempotentSupport.coeff_conj_eq_of_mem_center
          e he (x : G) ((x : G)⁻¹ * (h : G))
      have harg :
          (x : G) * ((x : G)⁻¹ * (h : G)) * (x : G)⁻¹ =
            (h : G) * (x : G)⁻¹ := by
        group
      rw [harg] at hcoeff
      simp only [Subgroup.coe_inv, Subgroup.coe_mul] at ⊢
      rw [hcoeff]
      exact mul_comm _ _

/-- The subgroup Brauer restriction sends central idempotents to
idempotents. -/
theorem subgroupCentralizerRestriction_isIdempotent_of_mem_center
    {p : ℕ} [Fact p.Prime]
    {R : Type u} [CommRing R] [CharP R p]
    {G : Type v} [Group G] [Finite G]
    (Q : Subgroup G) (hQ : IsPGroup p Q)
    (e : MonoidAlgebra R G)
    (hecenter : e ∈ Set.center (MonoidAlgebra R G))
    (heidem : IsIdempotentElem e) :
    IsIdempotentElem
      (DefectSupport.subgroupCentralizerRestriction R Q e) := by
  calc
    DefectSupport.subgroupCentralizerRestriction R Q e *
          DefectSupport.subgroupCentralizerRestriction R Q e =
        DefectSupport.subgroupCentralizerRestriction R Q (e * e) :=
      (subgroupCentralizerRestriction_mul_of_mem_center
        Q hQ e e hecenter hecenter).symm
    _ = DefectSupport.subgroupCentralizerRestriction R Q e :=
      congrArg _ heidem

/-- The subgroup Brauer map, bundled as a ring homomorphism from the ambient
center to the group algebra of the subgroup centralizer. -/
noncomputable def subgroupCentralizerRestrictionOnCenter
    (p : ℕ) [Fact p.Prime]
    (R : Type u) {G : Type v}
    [CommRing R] [CharP R p] [Group G] [Finite G]
    (Q : Subgroup G) (hQ : IsPGroup p Q) :
    Subring.center (MonoidAlgebra R G) →+*
      MonoidAlgebra R (Subgroup.centralizer (Q : Set G)) where
  toFun e := DefectSupport.subgroupCentralizerRestriction R Q
    (e : MonoidAlgebra R G)
  map_one' := subgroupCentralizerRestriction_one Q
  map_mul' := by
    intro a b
    change DefectSupport.subgroupCentralizerRestriction R Q
        ((a : MonoidAlgebra R G) * (b : MonoidAlgebra R G)) =
      DefectSupport.subgroupCentralizerRestriction R Q
          (a : MonoidAlgebra R G) *
        DefectSupport.subgroupCentralizerRestriction R Q
          (b : MonoidAlgebra R G)
    exact subgroupCentralizerRestriction_mul_of_mem_center
      Q hQ (a : MonoidAlgebra R G) (b : MonoidAlgebra R G) a.2 b.2
  map_zero' := by
    change DefectSupport.subgroupCentralizerRestriction R Q
      (0 : MonoidAlgebra R G) = 0
    exact map_zero (DefectSupport.subgroupCentralizerRestriction R Q)
  map_add' := by
    intro a b
    change DefectSupport.subgroupCentralizerRestriction R Q
        ((a : MonoidAlgebra R G) + (b : MonoidAlgebra R G)) =
      DefectSupport.subgroupCentralizerRestriction R Q
          (a : MonoidAlgebra R G) +
        DefectSupport.subgroupCentralizerRestriction R Q
          (b : MonoidAlgebra R G)
    exact map_add (DefectSupport.subgroupCentralizerRestriction R Q)
      (a : MonoidAlgebra R G) (b : MonoidAlgebra R G)

@[simp] theorem subgroupCentralizerRestrictionOnCenter_apply
    {p : ℕ} [Fact p.Prime]
    {R : Type u} [CommRing R] [CharP R p]
    {G : Type v} [Group G] [Finite G]
    (Q : Subgroup G) (hQ : IsPGroup p Q)
    (e : Subring.center (MonoidAlgebra R G)) :
    subgroupCentralizerRestrictionOnCenter p R Q hQ e =
      DefectSupport.subgroupCentralizerRestriction R Q
        (e : MonoidAlgebra R G) := rfl

/-- Center-to-center form of the subgroup Brauer map. -/
noncomputable def subgroupCentralizerRestrictionCenterHom
    (p : ℕ) [Fact p.Prime]
    (R : Type u) {G : Type v}
    [CommRing R] [CharP R p] [Group G] [Finite G]
    (Q : Subgroup G) (hQ : IsPGroup p Q) :
    Subring.center (MonoidAlgebra R G) →+*
      Subring.center
        (MonoidAlgebra R (Subgroup.centralizer (Q : Set G))) where
  toFun e := ⟨DefectSupport.subgroupCentralizerRestriction R Q
      (e : MonoidAlgebra R G),
    subgroupCentralizerRestriction_mem_center
      Q (e : MonoidAlgebra R G) e.2⟩
  map_one' := by
    apply Subtype.ext
    exact subgroupCentralizerRestriction_one Q
  map_mul' := by
    intro a b
    apply Subtype.ext
    exact subgroupCentralizerRestriction_mul_of_mem_center
      Q hQ (a : MonoidAlgebra R G) (b : MonoidAlgebra R G) a.2 b.2
  map_zero' := by
    apply Subtype.ext
    exact map_zero (DefectSupport.subgroupCentralizerRestriction R Q)
  map_add' := by
    intro a b
    apply Subtype.ext
    exact map_add (DefectSupport.subgroupCentralizerRestriction R Q)
      (a : MonoidAlgebra R G) (b : MonoidAlgebra R G)

@[simp] theorem subgroupCentralizerRestrictionCenterHom_apply
    {p : ℕ} [Fact p.Prime]
    {R : Type u} [CommRing R] [CharP R p]
    {G : Type v} [Group G] [Finite G]
    (Q : Subgroup G) (hQ : IsPGroup p Q)
    (e : Subring.center (MonoidAlgebra R G)) :
    (subgroupCentralizerRestrictionCenterHom p R Q hQ e :
      MonoidAlgebra R (Subgroup.centralizer (Q : Set G))) =
      DefectSupport.subgroupCentralizerRestriction R Q
        (e : MonoidAlgebra R G) := rfl

/-! Augmentation and support consequences.  These are useful because the
principal idempotent is characterized by augmentation one. -/

theorem augmentation_subgroupCentralizerRestriction
    {p : ℕ} [Fact p.Prime]
    {R : Type u} [CommRing R] [CharP R p]
    {G : Type v} [Group G] [Finite G]
    (Q : Subgroup G) (hQ : IsPGroup p Q)
    (e : MonoidAlgebra R G)
    (he : e ∈ Set.center (MonoidAlgebra R G)) :
    AugmentationScratch.augmentation R
        (Subgroup.centralizer (Q : Set G))
        (DefectSupport.subgroupCentralizerRestriction R Q e) =
      AugmentationScratch.augmentation R G e := by
  rw [AugmentationScratch.augmentation_apply,
    AugmentationScratch.augmentation_apply]
  symm
  exact sum_eq_sum_subgroupCentralizer_of_conj_invariant Q hQ
    (fun g : G => e g) (fun q g =>
      CentralIdempotentSupport.coeff_conj_eq_of_mem_center e he q g)

theorem hasTwoCoefficientSupport_of_augmentation_ne_zero
    {R : Type u} [CommRing R] [CharP R 2]
    {G : Type v} [Group G] [Finite G]
    (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (e : MonoidAlgebra R G)
    (he : e ∈ Set.center (MonoidAlgebra R G))
    (haug : AugmentationScratch.augmentation R G e ≠ 0) :
    DefectSupport.HasTwoCoefficientSupport e Q := by
  rw [DefectSupport.hasTwoCoefficientSupport_iff_restriction_ne_zero]
  refine ⟨hQ, ?_⟩
  intro hzero
  have hrestrictAug := congrArg
    (AugmentationScratch.augmentation R
      (Subgroup.centralizer (Q : Set G))) hzero
  rw [map_zero,
    augmentation_subgroupCentralizerRestriction Q hQ e he] at hrestrictAug
  exact haug hrestrictAug

/-- Every Sylow `2`-subgroup is a maximal Brauer-support subgroup of a
central element with nonzero augmentation.  In particular this recovers the
standard fact that defect groups of the principal block are Sylow. -/
theorem sylow_isMaximalTwoCoefficientSupport_of_augmentation_ne_zero
    [Fact (Nat.Prime 2)]
    {R : Type u} [CommRing R] [CharP R 2]
    {G : Type v} [Group G] [Finite G]
    (P : Sylow 2 G)
    (e : MonoidAlgebra R G)
    (he : e ∈ Set.center (MonoidAlgebra R G))
    (haug : AugmentationScratch.augmentation R G e ≠ 0) :
    DefectSupport.IsMaximalTwoCoefficientSupport e (P : Subgroup G) := by
  refine ⟨hasTwoCoefficientSupport_of_augmentation_ne_zero
      (P : Subgroup G) P.isPGroup' e he haug, ?_⟩
  intro Q hQ
  obtain ⟨P', hQP'⟩ := hQ.1.exists_le_sylow
  calc
    Nat.card Q ≤ Nat.card (P' : Subgroup G) :=
      Subgroup.card_le_of_le hQP'
    _ = 2 ^ (Nat.card G).factorization 2 :=
      Sylow.card_eq_multiplicity P'
    _ = Nat.card (P : Subgroup G) :=
      (Sylow.card_eq_multiplicity P).symm

/-- Conversely, every maximal support subgroup of an augmentation-nonzero
central element is a Sylow `2`-subgroup. -/
theorem exists_sylow_eq_of_isMaximalTwoCoefficientSupport_of_augmentation_ne_zero
    [Fact (Nat.Prime 2)]
    {R : Type u} [CommRing R] [CharP R 2]
    {G : Type v} [Group G] [Finite G]
    (e : MonoidAlgebra R G)
    (he : e ∈ Set.center (MonoidAlgebra R G))
    (haug : AugmentationScratch.augmentation R G e ≠ 0)
    (Q : Subgroup G)
    (hQ : DefectSupport.IsMaximalTwoCoefficientSupport e Q) :
    ∃ P : Sylow 2 G, (P : Subgroup G) = Q := by
  let P : Sylow 2 G := Classical.choice (inferInstance : Nonempty (Sylow 2 G))
  have hPSupport : DefectSupport.HasTwoCoefficientSupport e (P : Subgroup G) :=
    hasTwoCoefficientSupport_of_augmentation_ne_zero
      (P : Subgroup G) P.isPGroup' e he haug
  have hlower : Nat.card (P : Subgroup G) ≤ Nat.card Q :=
    hQ.2 (P : Subgroup G) hPSupport
  obtain ⟨P', hQP'⟩ := hQ.1.1.exists_le_sylow
  have hupper : Nat.card Q ≤ Nat.card (P : Subgroup G) := by
    calc
      Nat.card Q ≤ Nat.card (P' : Subgroup G) :=
        Subgroup.card_le_of_le hQP'
      _ = 2 ^ (Nat.card G).factorization 2 :=
        Sylow.card_eq_multiplicity P'
      _ = Nat.card (P : Subgroup G) :=
        (Sylow.card_eq_multiplicity P).symm
  have hcardQ : Nat.card Q = 2 ^ (Nat.card G).factorization 2 := by
    calc
      Nat.card Q = Nat.card (P : Subgroup G) :=
        Nat.le_antisymm hupper hlower
      _ = 2 ^ (Nat.card G).factorization 2 :=
        Sylow.card_eq_multiplicity P
  exact ⟨Sylow.ofCard Q hcardQ, rfl⟩

/-- A central factor which is still visible at a maximal support subgroup has
the same maximal support.  Any larger support of the factor would, by
multiplicativity of the subgroup Brauer map, also be a support of the parent
central element. -/
theorem isMaximalTwoCoefficientSupport_of_central_factor
    [Fact (Nat.Prime 2)]
    {R : Type u} [CommRing R] [CharP R 2]
    {G : Type v} [Group G] [Finite G]
    (f b : MonoidAlgebra R G)
    (hfcenter : f ∈ Set.center (MonoidAlgebra R G))
    (hbcenter : b ∈ Set.center (MonoidAlgebra R G))
    (hfb : f * b = f)
    (Q : Subgroup G)
    (hbMax : DefectSupport.IsMaximalTwoCoefficientSupport b Q)
    (hfQ : DefectSupport.HasTwoCoefficientSupport f Q) :
    DefectSupport.IsMaximalTwoCoefficientSupport f Q := by
  refine ⟨hfQ, ?_⟩
  intro Rsub hfR
  have hfRestrNe :
      DefectSupport.subgroupCentralizerRestriction R Rsub f ≠ 0 :=
    (DefectSupport.hasTwoCoefficientSupport_iff_restriction_ne_zero f Rsub).mp
      hfR |>.2
  have hbRestrNe :
      DefectSupport.subgroupCentralizerRestriction R Rsub b ≠ 0 := by
    intro hzero
    apply hfRestrNe
    have hmul := subgroupCentralizerRestriction_mul_of_mem_center
      Rsub hfR.1 f b hfcenter hbcenter
    rw [hfb, hzero, mul_zero] at hmul
    exact hmul
  apply hbMax.2 Rsub
  rw [DefectSupport.hasTwoCoefficientSupport_iff_restriction_ne_zero]
  exact ⟨hfR.1, hbRestrNe⟩

/-- At a maximal support subgroup, the Brauer image of a central idempotent
is a nonzero central idempotent.  This is the precise algebraic bridge from
coefficient support to a block-defect witness. -/
theorem maximalSupport_restriction_isNonzeroCentralIdempotent
    [Fact (Nat.Prime 2)]
    {R : Type u} [CommRing R] [CharP R 2]
    {G : Type v} [Group G] [Finite G]
    (e : MonoidAlgebra R G)
    (hecenter : e ∈ Set.center (MonoidAlgebra R G))
    (heidem : IsIdempotentElem e)
    (Q : Subgroup G)
    (hQ : DefectSupport.IsMaximalTwoCoefficientSupport e Q) :
    (DefectSupport.subgroupCentralizerRestriction R Q e ∈
        Set.center
          (MonoidAlgebra R (Subgroup.centralizer (Q : Set G)))) ∧
      IsIdempotentElem (DefectSupport.subgroupCentralizerRestriction R Q e) ∧
      DefectSupport.subgroupCentralizerRestriction R Q e ≠ 0 := by
  refine ⟨subgroupCentralizerRestriction_mem_center Q e hecenter, ?_, ?_⟩
  · exact subgroupCentralizerRestriction_isIdempotent_of_mem_center
      Q hQ.1.1 e hecenter heidem
  · exact
      (DefectSupport.hasTwoCoefficientSupport_iff_restriction_ne_zero e Q).mp
        hQ.1 |>.2

/-- Specialized principal-block form of the preceding theorem. -/
theorem reducedPrincipalBlockElement_sylow_isMaximalTwoCoefficientSupport
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (P : Sylow 2 G) :
    DefectSupport.IsMaximalTwoCoefficientSupport
      (BrauerBlockReduction.reducedPrincipalBlockElement d)
      (P : Subgroup G) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply sylow_isMaximalTwoCoefficientSupport_of_augmentation_ne_zero
    P (BrauerBlockReduction.reducedPrincipalBlockElement d)
    (BrauerBlockReduction.reducedPrincipalBlockElement_mem_center d)
  rw [AugmentationScratch.reducedPrincipalBlockElement_augmentation_eq_one d]
  exact one_ne_zero

end SubgroupBrauerMap
end Submission.ZStar
