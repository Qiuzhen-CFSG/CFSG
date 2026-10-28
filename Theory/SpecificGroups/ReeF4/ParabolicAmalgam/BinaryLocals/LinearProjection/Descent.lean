module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.LinearProjection.Levi
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.Radicals
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.LinearQuotient
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore

/-!
# Descent of the binary linear Levi projection

A twist-equivariant split retraction restricts to fixed points. Its canonical
Levi section supplies a fixed lift of each fixed Levi element, proving
surjectivity without assuming exactness of fixed points. The kernel remains
the specified root radical. An identification of the split end-node Levi with
SL₂ × SL₂ that carries the twist to factor exchange identifies its fixed
subgroup with the diagonal SL₂, hence with the actual PSL₂ in characteristic
two.

The split retraction and the compatible matrix identification are explicit
inputs below. They must be constructed before asserting the unconditional
binary projection. Source: Aschbacher–Smith F.1.12(I)(5), printed pp.263–264
of `refs/quasithin.pdf`.
-/

@[expose] public section
noncomputable section

namespace ReeF4.Parabolics.BinaryLinear

open LargeLocalSeeds Subgroup

/-- The fixed seed as a subgroup of the split seed, preserving its matrices. -/
def toSplitSeed (m : ℕ) : seed m .linear →* splitSeed m .linear where
  toFun x := ⟨toSplitGroup m x.val, x.property⟩
  map_one' := Subtype.ext (map_one (toSplitGroup m))
  map_mul' x y := Subtype.ext (map_mul (toSplitGroup m) x.val y.val)

@[simp] theorem seedTwist_toSplitSeed (m : ℕ) (x : seed m .linear) :
    seedTwist m (toSplitSeed m x) = toSplitSeed m x := by
  apply Subtype.ext
  rw [seedTwist_coe]
  exact reeTwist_toSplitGroup m x.val

/-- A fixed Levi element is an element of the actual fixed seed. -/
def fixedLeviInclusion (m : ℕ) : fixedLevi m →* seed m .linear where
  toFun x := ⟨⟨x.val.val, (ReeF4.mem_fixedSubgroup m _).mpr (by
    have h := congrArg Subtype.val ((mem_fixedLevi m x.val).mp x.property)
    simpa only [leviTwist_coe] using h)⟩,
      by
        change toSplitGroup m _ ∈ splitSeed m .linear
        rw [toSplitGroup_apply]
        exact splitLevi_le_seed m x.val.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem toSplitSeed_fixedLeviInclusion (m : ℕ) (x : fixedLevi m) :
    toSplitSeed m (fixedLeviInclusion m x) = leviInclusion m x.val := by
  apply Subtype.ext
  exact toSplitGroup_apply m _

/-- Restriction of a twist-equivariant split map to the actual fixed groups. -/
def fixedProjection (m : ℕ) (q : splitSeed m .linear →* splitLevi m)
    (hq : ∀ x, q (seedTwist m x) = leviTwist m (q x)) :
    seed m .linear →* fixedLevi m where
  toFun x := ⟨q (toSplitSeed m x), (mem_fixedLevi m _).mpr (by
    rw [← hq, seedTwist_toSplitSeed])⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)

/-- The fixed Levi section proves fixed-point surjectivity directly. -/
theorem fixedProjection_surjective (m : ℕ)
    (q : splitSeed m .linear →* splitLevi m)
    (hq : ∀ x, q (seedTwist m x) = leviTwist m (q x))
    (hs : ∀ l, q (leviInclusion m l) = l) :
    Function.Surjective (fixedProjection m q hq) := by
  intro l
  refine ⟨fixedLeviInclusion m l, Subtype.ext ?_⟩
  change q (toSplitSeed m (fixedLeviInclusion m l)) = l.val
  rw [toSplitSeed_fixedLeviInclusion, hs]

/-- The split kernel calculation restricts to the exact specified fixed radical. -/
theorem fixedProjection_ker (m : ℕ)
    (q : splitSeed m .linear →* splitLevi m)
    (hq : ∀ x, q (seedTwist m x) = leviTwist m (q x))
    (hker : q.ker = splitRadicalInSeed m) :
    (fixedProjection m q hq).ker = radicalInSeed m .linear := by
  ext x
  change (fixedProjection m q hq x = 1) ↔ _
  rw [Subtype.ext_iff]
  change q (toSplitSeed m x) = 1 ↔ _
  change toSplitSeed m x ∈ q.ker ↔ _
  rw [hker]
  rfl

abbrev BinarySL := Matrix.SpecialLinearGroup (Fin 2) (CoefficientField 0)

/-- Factor exchange has diagonal fixed subgroup; the equivalence is on the
actual split Levi and is required to intertwine the actual Ree twist. -/
def fixedLeviEquivSLOfProduct (e : splitLevi 0 ≃* BinarySL × BinarySL)
    (he : ∀ l, e (leviTwist 0 l) = (e l).swap) :
    fixedLevi 0 ≃* BinarySL where
  toFun x := (e x.val).1
  invFun a := ⟨e.symm (a, a), (mem_fixedLevi 0 _).mpr (e.injective (by
    rw [he, e.apply_symm_apply]
    rfl))⟩
  left_inv x := by
    apply Subtype.ext
    apply e.injective
    rw [e.apply_symm_apply]
    have hx := congrArg e ((mem_fixedLevi 0 x.val).mp x.property)
    rw [he] at hx
    exact Prod.ext rfl (congrArg Prod.fst hx).symm
  right_inv a := by simp
  map_mul' x y := by simp

/-- The characteristic-two center comparison reaches the project's actual PSL₂. -/
def fixedLeviEquivPSLOfProduct (e : splitLevi 0 ≃* BinarySL × BinarySL)
    (he : ∀ l, e (leviTwist 0 l) = (e l).swap) :
    fixedLevi 0 ≃* LinearQuotient 0 :=
  (fixedLeviEquivSLOfProduct e he).trans
    (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := CoefficientField 0))

/-- Assembly from the two split-matrix calculations. This is a conditional
construction, not the unconditional binary projection. -/
def projectionOfSplitData
    (q : splitSeed 0 .linear →* splitLevi 0)
    (hq : ∀ x, q (seedTwist 0 x) = leviTwist 0 (q x))
    (e : splitLevi 0 ≃* BinarySL × BinarySL)
    (he : ∀ l, e (leviTwist 0 l) = (e l).swap) :
    seed 0 .linear →* LinearQuotient 0 :=
  (fixedLeviEquivPSLOfProduct e he).toMonoidHom.comp (fixedProjection 0 q hq)

theorem projectionOfSplitData_surjective
    (q : splitSeed 0 .linear →* splitLevi 0)
    (hq : ∀ x, q (seedTwist 0 x) = leviTwist 0 (q x))
    (hs : ∀ l, q (leviInclusion 0 l) = l)
    (e : splitLevi 0 ≃* BinarySL × BinarySL)
    (he : ∀ l, e (leviTwist 0 l) = (e l).swap) :
    Function.Surjective (projectionOfSplitData q hq e he) :=
  (fixedLeviEquivPSLOfProduct e he).surjective.comp
    (fixedProjection_surjective 0 q hq hs)

theorem projectionOfSplitData_ker
    (q : splitSeed 0 .linear →* splitLevi 0)
    (hq : ∀ x, q (seedTwist 0 x) = leviTwist 0 (q x))
    (hker : q.ker = splitRadicalInSeed 0)
    (e : splitLevi 0 ≃* BinarySL × BinarySL)
    (he : ∀ l, e (leviTwist 0 l) = (e l).swap) :
    (projectionOfSplitData q hq e he).ker = radicalInSeed 0 .linear := by
  exact (MonoidHom.ker_comp_of_injective (fixedProjection 0 q hq)
    (fixedLeviEquivPSLOfProduct e he).toMonoidHom
    (fixedLeviEquivPSLOfProduct e he).injective).trans
      (fixedProjection_ker 0 q hq hker)

end ReeF4.Parabolics.BinaryLinear
