module
public import Theory.Character.ModularBlock.PGroupInvariantSum
public import Theory.Character.ModularBlock.IdempotentTrace
public import Theory.Character.ModularBlock.DefectSupport
public import Theory.Character.ModularBlock.Basic

/-!
# Subgroup Brauer homomorphisms

For a p-subgroup Q of a finite group G and coefficients of characteristic p,
restriction to the centralizer of Q preserves products of central group
algebra elements. It preserves the unit, centrality, idempotents, and
augmentation, yielding a ring homomorphism on centers.

Use the explicit conjugation action of Q on G. Its fixed points are exactly
the subgroup centralizer. Invariant weighted orbit cancellation reduces the
convolution coefficient sum to that centralizer, proving multiplicativity.
The same cancellation applied to coefficients proves augmentation
preservation. Centrality follows directly from coefficient conjugacy
invariance. The action is private and local, while the two bundled
restriction maps expose their coefficient behavior for later Brauer maps.

Ported from revision c3503435 of public/lean-eval/glauberman_zStar,
Submission/ZStar/SubgroupBrauerMap.lean. This is the generic algebraic
restriction calculation, independent of principal block constructions.
-/

public section
noncomputable section
open scoped BigOperators
namespace ModularBlock.SubgroupBrauerMap
universe u v w
attribute [local instance] Fintype.ofFinite

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
    (a * b).coeff h = ∑ g : G, a.coeff g * b.coeff (g⁻¹ * h) := by
  rw [MonoidAlgebra.coeff_mul_apply_left]
  exact Finsupp.sum_fintype a.coeff
    (fun g r => r * b.coeff (g⁻¹ * h)) (by simp)

/-- The fixed points of subgroup conjugation are the elements of the subgroup
centralizer. -/
private noncomputable def fixedPointsEquivCentralizer
    {G : Type v} [Group G] (Q : Subgroup G) :
    let : MulAction Q G := subgroupConjugationMulAction Q
    MulAction.fixedPoints Q G ≃ Subgroup.centralizer (Q : Set G) := by
  let : MulAction Q G := subgroupConjugationMulAction Q
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
  let : MulAction Q G := subgroupConjugationMulAction Q
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
  let F : G → R := fun g => a.coeff g * b.coeff (g⁻¹ * (h : G))
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
      rw [MonoidAlgebra.coeff_single_mul_apply,
        MonoidAlgebra.coeff_mul_single_apply]
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
@[expose] noncomputable def subgroupCentralizerRestrictionOnCenter
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
@[expose] noncomputable def subgroupCentralizerRestrictionCenterHom
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
    groupAlgebraAugmentation R
        (Subgroup.centralizer (Q : Set G))
        (DefectSupport.subgroupCentralizerRestriction R Q e) =
      groupAlgebraAugmentation R G e := by
  rw [groupAlgebraAugmentation_apply,
    groupAlgebraAugmentation_apply]
  symm
  exact sum_eq_sum_subgroupCentralizer_of_conj_invariant Q hQ
    (fun g : G => e.coeff g) (fun q g =>
      CentralIdempotentSupport.coeff_conj_eq_of_mem_center e he q g)

end ModularBlock.SubgroupBrauerMap

