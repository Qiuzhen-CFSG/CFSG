module

public import Theory.Representation.FirstCohomologyG2Natural.OctonionCocycle
public import Theory.Representation.FirstCohomologyG2Natural.NonbinaryCoordinates

/-!
# The nonbinary natural G₂ cocycle bound

A cocycle is determined by its six-dimensional value at a regular split-torus
element and one coordinate of its value on the short root C(1). To prove this,
consider a cocycle in the kernel of that evaluation map. Commutativity makes
it vanish on the whole torus; torus normalization then makes it vanish on the
Weyl maps. The torus centralizing the long root A has no fixed vectors, so the
cocycle vanishes on A. The torus centralizing C leaves two possible coordinates;
the involution relation C(1)² = 1 eliminates the second. The remaining first
coordinate is zero by assumption. Torus scaling and Weyl conjugation give
vanishing on all six root families, and the proved generation theorem finishes.

Thus the cocycle space injects into the direct sum of the natural module and
one copy of the field, of dimension seven. Perfectness for fields of size
greater than two transfers the bound to the actual commutator subgroup.
No cohomology dimension or spanning hypothesis enters the calculation.

Reference: Aschbacher--Smith, *The Classification of Quasithin Groups*,
I.1.6(5), printed p.408 / PDF p.419, citing Jones--Parshall (1976).
The root, torus, Weyl and generation interfaces are the attributed ATLAS ports
imported by `G2Natural`; this argument does not use B.4.6.
-/

open Atlas.SplitOctonion Representation.OneCohomology
namespace Atlas.G2.Natural
open Explicit
variable (K : Type*) [Field K] [CharP K 2]
namespace Nonbinary

private theorem cocycle_mul (f : cocycles (action K)) (g h : Model K) :
    f.val (g*h) = action K g (f.val h) + f.val g := f.property g h

private theorem cocycle_one (f : cocycles (action K)) : f.val 1 = 0 := by
  have h := f.property 1 1
  simpa using h.symm

private theorem cocycle_conjugate_of_zero (f : cocycles (action K)) (g h : Model K)
    (hg : f.val g = 0) : f.val (g * h * g⁻¹) = action K g (f.val h) := by
  have hi : f.val g⁻¹ = 0 := by
    have hh := f.property g⁻¹ g
    simpa [hg, cocycle_one] using hh.symm
  simp only [cocycle_mul, hg, hi, map_zero, add_zero, zero_add]

private theorem cocycle_fixed_of_commute (f : cocycles (action K)) (g h : Model K)
    (hg : f.val g = 0) (hcomm : g * h = h * g) :
    action K g (f.val h) = f.val h := by
  have hh := congrArg f.val hcomm
  simpa only [cocycle_mul, hg, map_zero, add_zero, zero_add] using hh

private theorem torus_cocycle_zero (f : cocycles (action K))
    (l m : Kˣ) (hl : l ≠ 1) (hm : m ≠ 1) (hlm : l ≠ m)
    (hf : f.val (torus l m) = 0) (a b : Kˣ) : f.val (torus a b) = 0 := by
  apply torus_fixed_eq_zero K l m hl hm hlm
  apply cocycle_fixed_of_commute K f _ _ hf
  rw [torus_product, torus_product, mul_comm l a, mul_comm m b]

omit [CharP K 2] in
private theorem weylR_torus (l m : Kˣ) :
    torus l m * weylR = weylR * torus l (l / m) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  fin_cases i <;>
    simp [torus, torusEquiv, torusLinear, torusWeights,
      weylR, weylREquiv, weylRLinear, weylRApply] <;> field_simp <;> simp

omit [CharP K 2] in
private theorem weylS_torus (l m : Kˣ) :
    torus l m * weylS = weylS * torus m l := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  fin_cases i <;>
    simp [torus, torusEquiv, torusLinear, torusWeights,
      weylS, weylSEquiv, weylSLinear, weylSApply] <;> field_simp <;> simp

private theorem weyl_cocycle_zero [Finite K] (hq : 2 < Nat.card K)
    (f : cocycles (action K)) (hf : ∀ l m, f.val (torus l m) = 0) :
    f.val weylR = 0 ∧ f.val weylS = 0 := by
  obtain ⟨l,m,hl,hm,hlm⟩ := exists_regular_torus K hq
  constructor
  · apply torus_fixed_eq_zero K l m hl hm hlm
    have h := congrArg f.val (weylR_torus K l m)
    simpa only [cocycle_mul, hf, map_zero, add_zero, zero_add] using h
  · apply torus_fixed_eq_zero K l m hl hm hlm
    have h := congrArg f.val (weylS_torus K l m)
    simpa only [cocycle_mul, hf, map_zero, add_zero, zero_add] using h

private theorem unit_ne_inverse (t : Kˣ) (ht : t ≠ 1) : t ≠ t⁻¹ := by
  intro h
  have hs : (t : K)^2 = 1 := by
    calc
      (t : K)^2 = (t : K) * (t : K) := pow_two _
      _ = (t : K) * (t⁻¹ : Kˣ) := congrArg (fun u : Kˣ => (t : K) * u) h
      _ = 1 := Units.mul_inv t
  rcases sq_eq_one_iff.mp hs with hs | hs
  · exact ht (Units.ext hs)
  · exact ht (Units.ext (hs.trans (CharTwo.neg_eq _)))

private theorem rootA_cocycle_zero [Finite K] (hq : 2 < Nat.card K)
    (f : cocycles (action K)) (hf : ∀ l m, f.val (torus l m) = 0) (a : K) :
    f.val (rootA a) = 0 := by
  obtain ⟨l,m,hl,_,_⟩ := exists_regular_torus K hq
  apply torus_fixed_eq_zero K l l⁻¹ hl (inv_ne_one.mpr hl) (unit_ne_inverse K l hl)
  have h := cocycle_conjugate_of_zero K f (torus l l⁻¹) (rootA a) (hf _ _)
  rw [torus_rootA] at h
  simpa using h.symm

private theorem coordinates_rootC_first (a : K) (v : Space K) :
    coordinates K (action K (rootC a) v) 0 =
      coordinates K v 0 + a^2 * coordinates K v 5 := by
  obtain ⟨x,rfl⟩ := mk_surjective K v
  have ht : x.val 3 = x.val 4 := by
    have hh := x.property
    change x.val 3 + x.val 4 = 0 at hh
    exact (eq_neg_of_add_eq_zero_left hh).trans (CharTwo.neg_eq _)
  simp [action_mk, coordinates_mk, traceZeroAction_val, rootC, rootCEquiv,
    rootCLinear, rootCApply, nonbinaryIndex, ht]

private theorem rootC_one_cocycle_zero [Finite K] (hq : 2 < Nat.card K)
    (f : cocycles (action K)) (hf : ∀ l m, f.val (torus l m) = 0)
    (h0 : coordinates K (f.val (rootC 1)) 0 = 0) : f.val (rootC 1) = 0 := by
  obtain ⟨t,m,ht,_,_⟩ := exists_regular_torus K hq
  have ht' : (t : K) ≠ 1 := by intro h; exact ht (Units.ext h)
  have hfix : action K (torus 1 t) (f.val (rootC 1)) = f.val (rootC 1) := by
    have h := cocycle_conjugate_of_zero K f (torus 1 t) (rootC 1) (hf _ _)
    rw [torus_rootC] at h
    simpa using h.symm
  have h5 : coordinates K (f.val (rootC 1)) 5 = 0 := by
    have h := congrArg (fun v => coordinates K v 0) (cocycle_mul K f (rootC 1) (rootC 1))
    rw [rootC_add, CharTwo.add_self_eq_zero, rootC_zero, cocycle_one] at h
    simp only [map_zero, map_add, Pi.add_apply, Pi.zero_apply,
      coordinates_rootC_first, one_pow, one_mul, h0, zero_add, add_zero] at h
    exact h.symm
  apply coordinates_injective K
  ext i
  change coordinates K (f.val (rootC 1)) i = 0
  fin_cases i
  · exact h0
  · apply torus_fixed_coordinate K 1 t _ hfix 1
    simpa [torusWeights, nonbinaryIndex] using ht'
  · apply torus_fixed_coordinate K 1 t _ hfix 2
    simpa [torusWeights, nonbinaryIndex] using ht'
  · apply torus_fixed_coordinate K 1 t _ hfix 3
    simpa [torusWeights, nonbinaryIndex] using ht'
  · apply torus_fixed_coordinate K 1 t _ hfix 4
    simpa [torusWeights, nonbinaryIndex] using ht'
  · exact h5

private theorem rootC_cocycle_zero (f : cocycles (action K))
    (hf : ∀ l m, f.val (torus l m) = 0) (h1 : f.val (rootC 1) = 0) (a : K) :
    f.val (rootC a) = 0 := by
  by_cases ha : a = 0
  · simp [ha, cocycle_one]
  · have h := cocycle_conjugate_of_zero K f (torus (Units.mk0 a ha) 1)
      (rootC 1) (hf _ _)
    simpa [torus_rootC, h1] using h

omit [CharP K 2] in
private theorem weylS_rootC (a : K) : weylS * rootC a * weylS⁻¹ = rootD a := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  fin_cases i <;> simp [weylS, weylSEquiv, weylSLinear, weylSApply,
    rootC, rootCEquiv, rootCLinear, rootCApply, rootD, rootDEquiv, rootDLinear,
    rootDApply] <;> ring

/-- The zero set of a cocycle is a subgroup. -/
private def zeroSubgroup (f : cocycles (action K)) : Subgroup (Model K) where
  carrier := {g | f.val g = 0}
  one_mem' := cocycle_one K f
  mul_mem' := by
    intro g h hg hh
    change f.val (g*h) = 0
    rw [cocycle_mul, hg, hh, map_zero, add_zero]
  inv_mem' := by
    intro g hg
    change f.val g = 0 at hg
    have h := cocycle_mul K f g⁻¹ g
    simpa [hg, cocycle_one] using h.symm

/-- A torus-zero cocycle is detected by one coordinate on the short root C. -/
private theorem eq_zero_of_torus_of_rootC [Finite K] (hq : 2 < Nat.card K)
    (f : cocycles (action K)) (hf : ∀ l m, f.val (torus l m) = 0)
    (h0 : coordinates K (f.val (rootC 1)) 0 = 0) : f = 0 := by
  obtain ⟨hR,hS⟩ := weyl_cocycle_zero K hq f hf
  have hA := rootA_cocycle_zero K hq f hf
  have hC := rootC_cocycle_zero K f hf (rootC_one_cocycle_zero K hq f hf h0)
  have hB (a : K) : f.val (rootB a) = 0 := by
    rw [← weylR_rootA, cocycle_conjugate_of_zero K f _ _ hR, hA, map_zero]
  have hE (a : K) : f.val (rootE a) = 0 := by
    rw [← weylS_rootB, cocycle_conjugate_of_zero K f _ _ hS, hB, map_zero]
  have hD (a : K) : f.val (rootD a) = 0 := by
    rw [← weylS_rootC K, cocycle_conjugate_of_zero K f _ _ hS, hC, map_zero]
  have hF (a : K) : f.val (rootF a) = 0 := by
    rw [← weylR_rootD, cocycle_conjugate_of_zero K f _ _ hR, hD, map_zero]
  have hU : unipotent ≤ zeroSubgroup K f := by
    rw [unipotent, Subgroup.closure_le]
    simp only [Set.union_subset_iff, Set.range_subset_iff]
    exact ⟨⟨⟨⟨⟨hA,hB⟩,hC⟩,hD⟩,hE⟩,hF⟩
  have hW : rootWeylSubgroup ≤ zeroSubgroup K f := by
    rw [rootWeylSubgroup, Subgroup.closure_le]
    intro g hg
    rcases hg with hg | hg
    · exact hU hg
    · change f.val g = 0
      rcases hg with rfl | rfl
      · exact hR
      · exact hS
  have hT : splitTorus ≤ zeroSubgroup K f := by
    rintro g ⟨⟨l,m⟩,rfl⟩
    exact hf l m
  have hG : generated ≤ zeroSubgroup K f := sup_le hW hT
  rw [generated_eq_top] at hG
  apply Subtype.ext
  funext g
  exact hG (Subgroup.mem_top g)

/-- Six values at a regular torus element and one short-root coordinate suffice. -/
private def evaluationMap (l m : Kˣ) : cocycles (action K) →ₗ[K] (Space K × K) :=
  (evaluation (action K) (torus l m)).prod
    ((LinearMap.proj 0).comp ((coordinates K).comp (evaluation (action K) (rootC 1))))

private theorem evaluationMap_injective [Finite K] (hq : 2 < Nat.card K)
    (l m : Kˣ) (hl : l ≠ 1) (hm : m ≠ 1) (hlm : l ≠ m) :
    Function.Injective (evaluationMap K l m) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro f hf
  have ht : f.val (torus l m) = 0 := congrArg Prod.fst hf
  have hc : coordinates K (f.val (rootC 1)) 0 = 0 := congrArg Prod.snd hf
  exact eq_zero_of_torus_of_rootC K hq f
    (torus_cocycle_zero K f l m hl hm hlm ht) hc

private theorem finrank_full_cocycles_le_seven [Finite K] (hq : 2 < Nat.card K) :
    Module.finrank K (cocycles (action K)) ≤ 7 := by
  obtain ⟨l,m,hl,hm,hlm⟩ := exists_regular_torus K hq
  have h := LinearMap.finrank_le_finrank_of_injective
    (evaluationMap_injective K hq l m hl hm hlm)
  simpa using h

end Nonbinary
/-- Upper bound for the genuine natural representation of the actual derived group. -/
public theorem finrank_cocycles_le_seven_nonbinary [Finite K] (hq : 2 < Nat.card K) :
    Module.finrank K (cocycles (derivedAction K)) ≤ 7 := by
  have hperfect := (isPerfect (F := K) hq).commutator_eq_top
  let toDerived (g : Model K) : commutator (Model K) :=
    ⟨g, by rw [hperfect]; trivial⟩
  let lift : cocycles (derivedAction K) →ₗ[K] cocycles (action K) :=
    { toFun := fun f => ⟨fun g => f.val (toDerived g), by
        intro g h
        exact f.property (toDerived g) (toDerived h)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective lift := by
    intro f g h
    apply Subtype.ext
    funext x
    exact congrArg (fun f : cocycles (action K) => f.val x.val) h
  exact (LinearMap.finrank_le_finrank_of_injective hinj).trans
    (Nonbinary.finrank_full_cocycles_le_seven K hq)

end Atlas.G2.Natural
