module

public import Mathlib.Algebra.DirectSum.Internal
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Strong internal `ZMod 2` gradings

For a commutative ring with an internal `ZMod 2` grading, a finite family of
degree-one elements `x i`, `y i` with `sum i, x i * y i = 1` is a homogeneous
dual basis.  Projection to degree zero and the maps
`a |-> (p0 a, fun i => p0 (y i * p1 a))` give a retract of the finite free
module `A 0 × (ι → A 0)`.  The identity decomposition `a = p0 a + p1 a`
then proves flatness without any assumption on the characteristic.  Finally,
the degree-zero projection is surjective, so the criterion
`I • top = top -> I = top` proves faithful flatness and exports the same result
for the canonical grade-zero algebra-map (equivalently, subtype) inclusion.
-/

open DirectSum

@[expose] public section

namespace StrongZModTwoGrading

variable {A σ ι : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable [Fintype ι]
variable (𝒜 : ZMod 2 → σ) [GradedRing 𝒜]
variable (x y : ι → A)
variable (hx : ∀ i, x i ∈ 𝒜 1) (hy : ∀ i, y i ∈ 𝒜 1)
variable (hxy : ∑ i, x i * y i = 1)

local notation "B" => 𝒜 0

noncomputable section
local instance : DecidableEq ι := Classical.decEq ι

/-- The degree-zero projection, viewed as a `B`-linear map into the degree-zero part. -/
def p0 : A →ₗ[B] (𝒜 0) where
  toFun a := ⟨GradedRing.proj 𝒜 0 a, by
    change (decompose 𝒜 a 0 : A) ∈ 𝒜 0
    exact (decompose 𝒜 a 0).property⟩
  map_add' x y := by
    apply Subtype.ext
    simp [GradedRing.proj_apply]
  map_smul' b a := by
    apply Subtype.ext
    change (decompose 𝒜 ((b : A) * a) 0 : A) = _
    rw [DirectSum.decompose_mul, DirectSum.decompose_coe]
    rw [DirectSum.coe_of_mul_apply_of_mem_zero]
    rfl

lemma zmod2_cases (z : ZMod 2) : z = 0 ∨ z = 1 := by
  have hzcast : (z.val : ZMod 2) = z := by
    simpa only [ZMod.cast_id] using (ZMod.natCast_val (R := ZMod 2) z)
  rw [← hzcast]
  have hv := ZMod.val_lt z
  have hz : z.val = 0 ∨ z.val = 1 := by omega
  rcases hz with hz | hz
  · left
    simp [hz]
  · right
    simp [hz]

lemma decomp_eq (a : A) :
    (decompose 𝒜 a 0 : A) + (decompose 𝒜 a 1 : A) = a := by
  classical
  have hs : (decompose 𝒜 a).support ⊆ ({0, 1} : Finset (ZMod 2)) := by
    intro z hz
    rcases zmod2_cases z with rfl | rfl <;> simp
  have hzero : ∀ z ∈ ({0, 1} : Finset (ZMod 2)), z ∉ (decompose 𝒜 a).support →
      (decompose 𝒜 a z : A) = 0 := by
    intro z hz hzs
    have hz0 : decompose 𝒜 a z = (0 : 𝒜 z) :=
      DFinsupp.notMem_support_iff.mp hzs
    exact congrArg (fun q : 𝒜 z => (q : A)) hz0
  have hsum : (∑ z ∈ (decompose 𝒜 a).support, (decompose 𝒜 a z : A)) =
      (∑ z ∈ ({0, 1} : Finset (ZMod 2)), (decompose 𝒜 a z : A)) :=
    Finset.sum_subset hs hzero
  have hsum01 :
      (∑ z ∈ ({0, 1} : Finset (ZMod 2)), (decompose 𝒜 a z : A)) =
        (decompose 𝒜 a 0 : A) + (decompose 𝒜 a 1 : A) := by
    norm_num
  calc
    (decompose 𝒜 a 0 : A) + (decompose 𝒜 a 1 : A) =
        ∑ z ∈ ({0, 1} : Finset (ZMod 2)), (decompose 𝒜 a z : A) := by
          rw [hsum01]
    _ = ∑ z ∈ (decompose 𝒜 a).support, (decompose 𝒜 a z : A) := hsum.symm
    _ = a := DirectSum.sum_support_decompose 𝒜 a

lemma p0_mem_zero {a : A} (ha : a ∈ 𝒜 0) : ((p0 𝒜 a : B) : A) = a := by
  exact DirectSum.decompose_of_mem_same 𝒜 ha

lemma p0_mem_one {a : A} (ha : a ∈ 𝒜 1) : ((p0 𝒜 a : B) : A) = 0 := by
  have h10 : (1 : ZMod 2) ≠ 0 := by norm_num
  exact DirectSum.decompose_of_mem_ne 𝒜 ha h10

lemma p0_mul_zero (b : B) (a : A) :
    ((p0 𝒜 ((b : A) * a) : B) : A) = (b : A) * (p0 𝒜 a : A) := by
  change (decompose 𝒜 ((b : A) * a) 0 : A) = _
  rw [DirectSum.decompose_mul, DirectSum.decompose_coe]
  rw [DirectSum.coe_of_mul_apply_of_mem_zero]
  rfl

/-- The degree-one projection, retained in `A` so it can be paired with `oddInclusion`. -/
def p1 : A →ₗ[B] A where
  toFun a := GradedRing.proj 𝒜 1 a
  map_add' x y := by simp [GradedRing.proj_apply]
  map_smul' b a := by
    change (decompose 𝒜 ((b : A) * a) 1 : A) = _
    rw [DirectSum.decompose_mul, DirectSum.decompose_coe]
    rw [DirectSum.coe_of_mul_apply_of_mem_zero]
    rfl

lemma p1_mem (a : A) : p1 𝒜 a ∈ 𝒜 1 := by
  exact (decompose 𝒜 a 1).property

lemma p0_product_one_zero {a : A} (ha : a ∈ 𝒜 1) (b : B) :
    ((p0 𝒜 (a * (b : A)) : B) : A) = 0 := by
  apply p0_mem_one
  simpa using SetLike.mul_mem_graded ha b.property

/-- Inclusion of a finite family of degree-one coordinates into the ambient ring. -/
def oddInclusion : (ι → B) →ₗ[B] A where
  toFun c := ∑ i, x i * (c i : A)
  map_add' c d := by
    simp only [Pi.add_apply, AddMemClass.coe_add, mul_add, Finset.sum_add_distrib]
  map_smul' b c := by
    change (∑ i, x i * ((b : A) * (c i : A))) =
      (b : A) * ∑ i, x i * (c i : A)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring

/-- The dual coordinate map obtained by multiplying by the `y i` and projecting to degree zero. -/
def oddProjection : A →ₗ[B] (ι → B) where
  toFun a i := p0 𝒜 (y i * p1 𝒜 a)
  map_add' a b := by
    funext i
    simp [mul_add, map_add]
  map_smul' b a := by
    funext i
    apply Subtype.ext
    simp only [Algebra.smul_def, Pi.smul_apply]
    rw [← Algebra.smul_def, map_smul]
    change (p0 𝒜 (y i * ((b : A) * p1 𝒜 a)) : A) =
      (b : A) * p0 𝒜 (y i * p1 𝒜 a)
    rw [show y i * ((b : A) * p1 𝒜 a) =
      (b : A) * (y i * p1 𝒜 a) by ring]
    exact p0_mul_zero 𝒜 b (y i * p1 𝒜 a)

/-- The finite-free source of the retract. -/
def freeInjection : (B × (ι → B)) →ₗ[B] A :=
  (Algebra.linearMap B A).comp (LinearMap.fst B B (ι → B)) +
    (oddInclusion 𝒜 x).comp (LinearMap.snd B B (ι → B))

def freeProjection : A →ₗ[B] (B × (ι → B)) :=
  (p0 𝒜).prod (oddProjection 𝒜 y)

theorem freeSource_free : Module.Free B (B × (ι → B)) := by infer_instance

theorem freeSource_finite : Module.Finite B (B × (ι → B)) := by infer_instance

include hx hy hxy
lemma oddInclusion_projection (z : 𝒜 1) :
    oddInclusion 𝒜 x (fun i => p0 𝒜 (y i * (z : A))) = (z : A) := by
  classical
  calc
    oddInclusion 𝒜 x (fun i => p0 𝒜 (y i * (z : A))) =
        ∑ i, x i * (p0 𝒜 (y i * (z : A)) : A) := rfl
    _ = ∑ i, x i * (y i * (z : A)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply congrArg (fun q : A => x i * q)
      apply p0_mem_zero 𝒜
      have htwo : (1 : ZMod 2) + 1 = 0 := by decide
      simpa only [htwo] using SetLike.mul_mem_graded (hy i) z.property
    _ = ∑ i, (p1 𝒜 (x i)) * (y i * (z : A)) := by
      apply Finset.sum_congr rfl
      intro i hi
      change x i * (y i * (z : A)) =
        (decompose 𝒜 (x i) 1 : A) * (y i * (z : A))
      rw [DirectSum.decompose_of_mem_same 𝒜 (hx i)]
    _ = (∑ i, x i * y i) * (z : A) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      change (decompose 𝒜 (x i) 1 : A) * (y i * (z : A)) =
        x i * y i * (z : A)
      rw [DirectSum.decompose_of_mem_same 𝒜 (hx i)]
      ring
    _ = (z : A) := by rw [hxy]; simp

include hx
lemma oddInclusion_projection_part (a : A) :
    oddInclusion 𝒜 x (fun i => p0 𝒜 (y i * p1 𝒜 a)) = p1 𝒜 a := by
  exact oddInclusion_projection 𝒜 x y hx hy hxy ⟨p1 𝒜 a, p1_mem 𝒜 a⟩

lemma freeInjection_projection :
    (freeInjection 𝒜 x).comp (freeProjection 𝒜 y) = LinearMap.id := by
  ext a
  change (p0 𝒜 a : A) +
      oddInclusion 𝒜 x (fun i => p0 𝒜 (y i * p1 𝒜 a)) = a
  rw [oddInclusion_projection_part 𝒜 x y hx hy hxy]
  exact decomp_eq 𝒜 a

theorem flat : Module.Flat B A := by
  apply Module.Flat.of_retract (freeProjection 𝒜 y) (freeInjection 𝒜 x)
  exact freeInjection_projection 𝒜 x y hx hy hxy

theorem projective : Module.Projective B A := by
  apply Module.Projective.of_split (freeProjection 𝒜 y) (freeInjection 𝒜 x)
  exact freeInjection_projection 𝒜 x y hx hy hxy

omit [Fintype ι] x y hx hy hxy in
lemma p0_surjective : Function.Surjective (p0 𝒜) := by
  intro b
  refine ⟨(b : A), ?_⟩
  apply Subtype.ext
  exact p0_mem_zero 𝒜 b.property

theorem faithfullyFlat : Module.FaithfullyFlat B A := by
  rw [Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top]
  refine ⟨flat 𝒜 x y hx hy hxy, ?_⟩
  intro I hI
  apply I.eq_top_iff_one.mpr
  have hmem : (1 : A) ∈ I • (⊤ : Submodule B A) := by
    rw [hI]
    exact Submodule.mem_top
  have hmap : p0 𝒜 (1 : A) ∈ Submodule.map (p0 𝒜) (I • (⊤ : Submodule B A)) :=
    Submodule.mem_map_of_mem hmem
  have htop : Submodule.map (p0 𝒜) (⊤ : Submodule B A) = (⊤ : Submodule B B) := by
    rw [Submodule.map_top, LinearMap.range_eq_top.mpr (p0_surjective 𝒜)]
  rw [Submodule.map_smul'', htop] at hmap
  have hpone : p0 𝒜 (1 : A) = (1 : B) := by
    apply Subtype.ext
    exact p0_mem_zero 𝒜 (SetLike.one_mem_graded 𝒜)
  simpa [hpone, Ideal.smul_top_eq_map] using hmap

/-- Faithful flatness of the canonical inclusion of the degree-zero subring. -/
theorem gradeZero_algebraMap_faithfullyFlat :
    (algebraMap (𝒜 0) A).FaithfullyFlat :=
  (RingHom.faithfullyFlat_algebraMap_iff).2 (faithfullyFlat 𝒜 x y hx hy hxy)

/-- The same inclusion written as the subtype map of `SetLike.GradeZero.subring`. -/
theorem gradeZeroSubtype_faithfullyFlat :
    (SetLike.GradeZero.subring 𝒜).subtype.FaithfullyFlat := by
  change (algebraMap (𝒜 0) A).FaithfullyFlat
  exact gradeZero_algebraMap_faithfullyFlat 𝒜 x y hx hy hxy

end

end StrongZModTwoGrading

end
