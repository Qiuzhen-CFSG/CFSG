import Submission.ZStar.CentralIdempotentSupport

/-!
# A characteristic-two Brauer restriction for an involution

This scratch file proves the combinatorial core of Feit III.7.1 in the
special case needed by the Z-star argument: restricting the coefficients of
a central group-algebra element to an involution centralizer is multiplicative
after reduction to characteristic two.
-/

noncomputable section

open scoped BigOperators

namespace Submission.ZStar

namespace BrauerMapScratch

universe u v

attribute [local instance] Fintype.ofFinite

/-- Coefficient restriction from a group algebra to the centralizer of an
element.  It is always additive; multiplicativity on central elements in
characteristic two is proved below for involutions. -/
def centralizerRestriction
    (R : Type u) {G : Type v} [Semiring R] [Group G]
    (z : G) :
    MonoidAlgebra R G →+ MonoidAlgebra R
      (Subgroup.centralizer ({z} : Set G)) :=
  Finsupp.comapDomain.addMonoidHom
    (Subgroup.centralizer ({z} : Set G)).subtype_injective

@[simp] theorem centralizerRestriction_apply
    {R : Type u} {G : Type v} [Semiring R] [Group G]
    (z : G) (a : MonoidAlgebra R G)
    (h : Subgroup.centralizer ({z} : Set G)) :
    centralizerRestriction R z a h = a (h : G) := rfl

/-- Coefficient restriction commutes with change of coefficient ring.  This
is the reduction-modulo-`2` square used for block idempotents. -/
theorem centralizerRestriction_mapRingHom
    {R : Type u} {S : Type*} {G : Type v}
    [Semiring R] [Semiring S] [Group G]
    (f : R →+* S) (z : G) (a : MonoidAlgebra R G) :
    centralizerRestriction S z (MonoidAlgebra.mapRingHom G f a) =
      MonoidAlgebra.mapRingHom
        (Subgroup.centralizer ({z} : Set G)) f
        (centralizerRestriction R z a) := by
  ext h
  simp [centralizerRestriction_apply,
    MonoidAlgebra.mapRingHom_apply]

@[simp] theorem centralizerRestriction_one
    {R : Type u} {G : Type v} [Semiring R] [Group G]
    (z : G) :
    centralizerRestriction R z (1 : MonoidAlgebra R G) = 1 := by
  classical
  ext h
  change (Finsupp.single 1 1 : G →₀ R) (h : G) =
    (Finsupp.single 1 1 :
      Subgroup.centralizer ({z} : Set G) →₀ R) h
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

/-- Restricting the coefficients of a central group-algebra element to a
centralizer still gives a central element of the centralizer group algebra. -/
theorem centralizerRestriction_mem_center
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (z : G) (e : MonoidAlgebra R G)
    (he : e ∈ Set.center (MonoidAlgebra R G)) :
    centralizerRestriction R z e ∈
      Set.center
        (MonoidAlgebra R (Subgroup.centralizer ({z} : Set G))) := by
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
      simp only [centralizerRestriction_apply]
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

private theorem monoidAlgebra_mul_apply_eq_sum
    {R : Type u} {G : Type v} [Semiring R] [Group G] [Finite G]
    (a b : MonoidAlgebra R G) (h : G) :
    (a * b) h = ∑ g : G, a g * b (g⁻¹ * h) := by
  rw [MonoidAlgebra.mul_apply_left]
  exact Finsupp.sum_fintype a
    (fun g r => r * b (g⁻¹ * h)) (by simp)

private theorem conjugateBy_involution_involutive
    {G : Type v} [Group G] {z : G} (hz : z * z = 1) (g : G) :
    z * (z * g * z⁻¹) * z⁻¹ = g := by
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  rw [hzinv]
  calc
    z * (z * g * z) * z = (z * z) * g * (z * z) := by
      simp only [mul_assoc]
    _ = g := by rw [hz]; simp

private theorem conjugateBy_eq_self_of_mem_centralizer
    {G : Type v} [Group G] {z g : G} (hz : z * z = 1)
    (hg : g ∈ Subgroup.centralizer ({z} : Set G)) :
    z * g * z⁻¹ = g := by
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hcomm : g * z = z * g :=
    Subgroup.mem_centralizer_singleton_iff.mp hg
  rw [hzinv, ← hcomm]
  simp only [mul_assoc]
  rw [hz, mul_one]

private theorem mem_centralizer_of_conjugateBy_eq_self
    {G : Type v} [Group G] {z g : G} (hz : z * z = 1)
    (hg : z * g * z⁻¹ = g) :
    g ∈ Subgroup.centralizer ({z} : Set G) := by
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have h := congrArg (fun x : G => x * z) hg
  have hzg : z * g = g * z := by
    simpa only [hzinv, mul_assoc, hz, mul_one] using h
  exact hzg.symm

/-- Orbit cancellation under conjugation by an involution.  Centrality makes
the summand constant on each conjugation orbit, and every orbit outside the
centralizer has size two, hence contributes zero in characteristic two. -/
private theorem sum_eq_sum_centralizer_of_conj_invariant
    {R : Type u} {G : Type v}
    [CommRing R] [CharP R 2] [Group G] [Finite G] [DecidableEq G]
    (z : G)
    [DecidablePred (fun g : G =>
      g ∈ Subgroup.centralizer ({z} : Set G))]
    (hz : z * z = 1) (F : G → R)
    (hF : ∀ g : G, F (z * g * z⁻¹) = F g) :
    ∑ g : G, F g =
      ∑ g ∈ (Finset.univ : Finset G) with
        g ∈ Subgroup.centralizer ({z} : Set G), F g := by
  classical
  let moved : Finset G := Finset.univ.filter
    (fun g => g ∉ Subgroup.centralizer ({z} : Set G))
  have hmoved : ∑ g ∈ moved, F g = 0 := by
    refine Finset.sum_involution
      (s := moved) (f := F)
      (g := fun g _hg => z * g * z⁻¹) ?_ ?_ ?_ ?_
    · intro g _hg
      rw [hF]
      exact CharTwo.add_self_eq_zero _
    · intro g hg _hFg hfixed
      apply (Finset.mem_filter.mp hg).2
      exact mem_centralizer_of_conjugateBy_eq_self hz hfixed
    · intro g hg
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hconjMem
      have hfixed := conjugateBy_eq_self_of_mem_centralizer hz hconjMem
      have hinv := conjugateBy_involution_involutive hz g
      apply (Finset.mem_filter.mp hg).2
      rw [← hinv, hfixed]
      exact hconjMem
    · intro g _hg
      exact conjugateBy_involution_involutive hz g
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset G)
      (fun g => g ∈ Subgroup.centralizer ({z} : Set G)) F
  calc
    ∑ g : G, F g =
        (∑ g ∈ (Finset.univ : Finset G) with
            g ∈ Subgroup.centralizer ({z} : Set G), F g) +
          ∑ g ∈ (Finset.univ : Finset G) with
            g ∉ Subgroup.centralizer ({z} : Set G), F g := hsplit.symm
    _ = ∑ g ∈ (Finset.univ : Finset G) with
          g ∈ Subgroup.centralizer ({z} : Set G), F g := by
      change _ + (∑ g ∈ moved, F g) = _
      rw [hmoved, add_zero]

/-- Public subtype-sum form of involution-orbit cancellation. -/
theorem sum_centralizer_of_conj_invariant
    {R : Type u} {G : Type v}
    [CommRing R] [CharP R 2] [Group G] [Finite G]
    (z : G) (hz : z * z = 1) (F : G → R)
    (hF : ∀ g : G, F (z * g * z⁻¹) = F g) :
    ∑ g : G, F g =
      ∑ h : Subgroup.centralizer ({z} : Set G), F (h : G) := by
  classical
  letI : Fintype (Subgroup.centralizer ({z} : Set G)) :=
    Fintype.ofFinite _
  calc
    ∑ g : G, F g =
        ∑ g ∈ (Finset.univ : Finset G) with
          g ∈ Subgroup.centralizer ({z} : Set G), F g :=
      sum_eq_sum_centralizer_of_conj_invariant z hz F hF
    _ = ∑ h : Subgroup.centralizer ({z} : Set G), F (h : G) := by
      rw [← Finset.sum_subtype_eq_sum_filter]
      apply Finset.sum_congr
      · ext h
        simp
      · intro h _hh
        rfl

/-- Special-case Brauer homomorphism: in characteristic two, coefficient
restriction to the centralizer of an involution preserves products of central
group-algebra elements. -/
theorem centralizerRestriction_mul_of_mem_center
    {R : Type u} {G : Type v}
    [CommRing R] [CharP R 2] [Group G] [Finite G]
    (z : G) (hz : z * z = 1)
    (a b : MonoidAlgebra R G)
    (ha : a ∈ Set.center (MonoidAlgebra R G))
    (hb : b ∈ Set.center (MonoidAlgebra R G)) :
    centralizerRestriction R z (a * b) =
      centralizerRestriction R z a * centralizerRestriction R z b := by
  classical
  letI : Fintype (Subgroup.centralizer ({z} : Set G)) :=
    Fintype.ofFinite _
  ext h
  rw [centralizerRestriction_apply,
    monoidAlgebra_mul_apply_eq_sum]
  rw [monoidAlgebra_mul_apply_eq_sum]
  simp only [centralizerRestriction_apply, Subgroup.coe_inv,
    Subgroup.coe_mul]
  let F : G → R := fun g => a g * b (g⁻¹ * (h : G))
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hh : (h : G) * z = z * (h : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp h.2
  have hF : ∀ g : G, F (z * g * z⁻¹) = F g := by
    intro g
    have haCoeff :=
      CentralIdempotentSupport.coeff_conj_eq_of_mem_center a ha z g
    have harg :
        (z * g * z⁻¹)⁻¹ * (h : G) =
          z * (g⁻¹ * (h : G)) * z⁻¹ := by
      rw [hzinv]
      simp only [mul_inv_rev, mul_assoc]
      rw [hzinv, ← hh]
    have hbCoeff :=
      CentralIdempotentSupport.coeff_conj_eq_of_mem_center
        b hb z (g⁻¹ * (h : G))
    dsimp [F]
    rw [haCoeff, harg, hbCoeff]
  have hsum :
      (∑ g : G, F g) =
        ∑ k : Subgroup.centralizer ({z} : Set G), F (k : G) := by
    calc
      ∑ g : G, F g =
          ∑ g ∈ (Finset.univ : Finset G) with
            g ∈ Subgroup.centralizer ({z} : Set G), F g :=
        sum_eq_sum_centralizer_of_conj_invariant z hz F hF
      _ = ∑ k : Subgroup.centralizer ({z} : Set G), F (k : G) := by
        rw [← Finset.sum_subtype_eq_sum_filter]
        apply Finset.sum_congr
        · ext k
          simp
        · intro k _hk
          rfl
  simpa only [F] using hsum

/-- The order-two Brauer restriction sends central idempotents of the ambient
group algebra to idempotents of the centralizer group algebra. -/
theorem centralizerRestriction_isIdempotent_of_mem_center
    {R : Type u} {G : Type v}
    [CommRing R] [CharP R 2] [Group G] [Finite G]
    (z : G) (hz : z * z = 1)
    (e : MonoidAlgebra R G)
    (hecenter : e ∈ Set.center (MonoidAlgebra R G))
    (heidem : IsIdempotentElem e) :
    IsIdempotentElem (centralizerRestriction R z e) := by
  calc
    centralizerRestriction R z e * centralizerRestriction R z e =
        centralizerRestriction R z (e * e) :=
      (centralizerRestriction_mul_of_mem_center
        z hz e e hecenter hecenter).symm
    _ = centralizerRestriction R z e := congrArg _ heidem

/-- Orthogonal central elements remain orthogonal after order-two Brauer
restriction.  Applied to block idempotents, this shows that their nonzero
local images are pairwise orthogonal idempotents. -/
theorem centralizerRestriction_mul_eq_zero_of_mem_center
    {R : Type u} {G : Type v}
    [CommRing R] [CharP R 2] [Group G] [Finite G]
    (z : G) (hz : z * z = 1)
    (a b : MonoidAlgebra R G)
    (ha : a ∈ Set.center (MonoidAlgebra R G))
    (hb : b ∈ Set.center (MonoidAlgebra R G))
    (hab : a * b = 0) :
    centralizerRestriction R z a * centralizerRestriction R z b = 0 := by
  rw [← centralizerRestriction_mul_of_mem_center z hz a b ha hb, hab]
  exact map_zero (centralizerRestriction R z)

/-- The characteristic-two Brauer map for an involution, bundled as a ring
homomorphism on the center of the ambient group algebra. -/
noncomputable def centralizerRestrictionOnCenter
    (R : Type u) {G : Type v}
    [CommRing R] [CharP R 2] [Group G] [Finite G]
    (z : G) (hz : z * z = 1) :
    Subring.center (MonoidAlgebra R G) →+*
      MonoidAlgebra R (Subgroup.centralizer ({z} : Set G)) where
  toFun e := centralizerRestriction R z (e : MonoidAlgebra R G)
  map_one' := centralizerRestriction_one z
  map_mul' := by
    intro a b
    change centralizerRestriction R z
        ((a : MonoidAlgebra R G) * (b : MonoidAlgebra R G)) =
      centralizerRestriction R z (a : MonoidAlgebra R G) *
        centralizerRestriction R z (b : MonoidAlgebra R G)
    exact centralizerRestriction_mul_of_mem_center
      z hz (a : MonoidAlgebra R G) (b : MonoidAlgebra R G) a.2 b.2
  map_zero' := by
    change centralizerRestriction R z (0 : MonoidAlgebra R G) = 0
    exact map_zero (centralizerRestriction R z)
  map_add' := by
    intro a b
    change centralizerRestriction R z
        ((a : MonoidAlgebra R G) + (b : MonoidAlgebra R G)) =
      centralizerRestriction R z (a : MonoidAlgebra R G) +
        centralizerRestriction R z (b : MonoidAlgebra R G)
    exact map_add (centralizerRestriction R z)
      (a : MonoidAlgebra R G) (b : MonoidAlgebra R G)

@[simp] theorem centralizerRestrictionOnCenter_apply
    {R : Type u} {G : Type v}
    [CommRing R] [CharP R 2] [Group G] [Finite G]
    (z : G) (hz : z * z = 1)
    (e : Subring.center (MonoidAlgebra R G)) :
    centralizerRestrictionOnCenter R z hz e =
      centralizerRestriction R z (e : MonoidAlgebra R G) := rfl

/-- The same map with codomain restricted to the center of the centralizer
group algebra.  This is the usual center-to-center form of the Brauer map. -/
noncomputable def centralizerRestrictionCenterHom
    (R : Type u) {G : Type v}
    [CommRing R] [CharP R 2] [Group G] [Finite G]
    (z : G) (hz : z * z = 1) :
    Subring.center (MonoidAlgebra R G) →+*
      Subring.center
        (MonoidAlgebra R (Subgroup.centralizer ({z} : Set G))) where
  toFun e := ⟨centralizerRestriction R z (e : MonoidAlgebra R G),
    centralizerRestriction_mem_center z (e : MonoidAlgebra R G) e.2⟩
  map_one' := by
    apply Subtype.ext
    exact centralizerRestriction_one z
  map_mul' := by
    intro a b
    apply Subtype.ext
    exact centralizerRestriction_mul_of_mem_center
      z hz (a : MonoidAlgebra R G) (b : MonoidAlgebra R G) a.2 b.2
  map_zero' := by
    apply Subtype.ext
    exact map_zero (centralizerRestriction R z)
  map_add' := by
    intro a b
    apply Subtype.ext
    exact map_add (centralizerRestriction R z)
      (a : MonoidAlgebra R G) (b : MonoidAlgebra R G)

@[simp] theorem centralizerRestrictionCenterHom_apply
    {R : Type u} {G : Type v}
    [CommRing R] [CharP R 2] [Group G] [Finite G]
    (z : G) (hz : z * z = 1)
    (e : Subring.center (MonoidAlgebra R G)) :
    (centralizerRestrictionCenterHom R z hz e :
      MonoidAlgebra R (Subgroup.centralizer ({z} : Set G))) =
      centralizerRestriction R z (e : MonoidAlgebra R G) := rfl

end BrauerMapScratch

end Submission.ZStar
