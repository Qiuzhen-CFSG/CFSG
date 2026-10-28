module

public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.QuotientConstruction.AffineCoordinates
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.GroupTheory.PGroup

/-!
# Recovering the product quotient from compatible affine coordinates

An affine form records the actual permutation of the 24 native points:
one permutation of the three octads, one common binary special linear map,
and a translation on each octad. Uniqueness and composition of these forms
construct a homomorphism to S₃ × SL₃(2), provided every stabilizer element
has an affine form. Its kernel consists of translations; each element
squares to the identity. Explicit affine lifts then give surjectivity.

`AffineCoverage` and `AffineLifts` are independent proof obligations.
No coverage or lift is assumed as a property of the native M₂₄ carrier,
and this conditional construction alone does not establish Lemma 20.2.
It needs neither a splitting nor the exact kernel order 64.

Source context: Aschbacher, *Sporadic Groups*, Chapter 7, Lemma 20.2,
printed p.97; GLS3, Table 5.3e, E₆₄.N(3B).
-/

@[expose] public section

namespace Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction

/-- The full quotient model, retaining both source factors. -/
abbrev QuotientModel :=
  Equiv.Perm (Fin 3) × Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)

/-- The coordinate formula for an actual element of the native stabilizer.
Translations are indexed by the source octad. -/
def HasAffineForm (g : trioStabilizer standardTrio) (q : QuotientModel)
    (t : Fin 3 → Vector) : Prop :=
  ∀ i v, (g.val.val : Equiv.Perm (Fin 24)) (point (i,v)) =
    point (q.1 i, Matrix.SpecialLinearGroup.toLin' q.2 v + t i)

theorem hasAffineForm_unique {g : trioStabilizer standardTrio}
    {q r : QuotientModel} {t u : Fin 3 → Vector}
    (h : HasAffineForm g q t) (k : HasAffineForm g r u) : q = r ∧ t = u := by
  have he (i : Fin 3) (v : Vector) := point.injective ((h i v).symm.trans (k i v))
  have ht : t = u := by
    funext i
    simpa using congrArg Prod.snd (he i 0)
  refine ⟨Prod.ext ?_ ?_, ht⟩
  · exact Equiv.ext (fun i => congrArg Prod.fst (he i 0))
  · apply Matrix.SpecialLinearGroup.toLin'_injective
    ext v j
    have hv := congrArg Prod.snd (he (0 : Fin 3) v)
    rw [ht] at hv
    exact congrFun (add_right_cancel hv) j

theorem hasAffineForm_one : HasAffineForm 1 1 0 := by
  intro i v
  simp

theorem hasAffineForm_mul {g h : trioStabilizer standardTrio}
    {q r : QuotientModel} {t u : Fin 3 → Vector}
    (hg : HasAffineForm g q t) (hh : HasAffineForm h r u) :
    HasAffineForm (g * h) (q * r)
      (fun i => Matrix.SpecialLinearGroup.toLin' q.2 (u i) + t (r.1 i)) := by
  intro i v
  change g.val.val (h.val.val (point (i,v))) = _
  rw [hh, hg]
  apply congrArg point
  apply Prod.ext
  · rfl
  · change Matrix.SpecialLinearGroup.toLin' q.2
        (Matrix.SpecialLinearGroup.toLin' r.2 v + u i) + t (r.1 i) =
      Matrix.SpecialLinearGroup.toLin' (q.2 * r.2) v +
        (Matrix.SpecialLinearGroup.toLin' q.2 (u i) + t (r.1 i))
    rw [map_mul]
    simp only [LinearEquiv.mul_apply, map_add, add_assoc]

/-- Every stabilizer element has one common linear part on the three octads. -/
def AffineCoverage : Prop :=
  ∀ g : trioStabilizer standardTrio, ∃ q t, HasAffineForm g q t

/-- Every prescribed octad permutation and linear part is realized in M₂₄. -/
def AffineLifts : Prop :=
  ∀ q : QuotientModel, ∃ g t, HasAffineForm g q t

/-- Forget the translation, using uniqueness to obtain a homomorphism. -/
noncomputable def affineQuotient (h : AffineCoverage) :
    trioStabilizer standardTrio →* QuotientModel where
  toFun g := (h g).choose
  map_one' := by
    obtain ⟨t, ht⟩ := (h 1).choose_spec
    exact (hasAffineForm_unique ht hasAffineForm_one).1
  map_mul' g k := by
    obtain ⟨t, ht⟩ := (h g).choose_spec
    obtain ⟨u, hu⟩ := (h k).choose_spec
    obtain ⟨v, hv⟩ := (h (g * k)).choose_spec
    exact (hasAffineForm_unique hv (hasAffineForm_mul ht hu)).1

theorem affineQuotient_spec (h : AffineCoverage) (g : trioStabilizer standardTrio) :
    ∃ t, HasAffineForm g (affineQuotient h g) t :=
  (h g).choose_spec

theorem affineQuotient_eq (h : AffineCoverage) {g : trioStabilizer standardTrio}
    {q : QuotientModel} {t : Fin 3 → Vector} (hg : HasAffineForm g q t) :
    affineQuotient h g = q := by
  obtain ⟨u, hu⟩ := affineQuotient_spec h g
  exact (hasAffineForm_unique hu hg).1

theorem affineQuotient_surjective (h : AffineCoverage) (hl : AffineLifts) :
    Function.Surjective (affineQuotient h) := by
  intro q
  obtain ⟨g, t, hg⟩ := hl q
  exact ⟨g, affineQuotient_eq h hg⟩

/-- Trivial octad permutation and linear part leave only translations,
whose squares are the identity in characteristic two. -/
theorem affineQuotient_kernel_isPGroup (h : AffineCoverage) :
    IsPGroup 2 (affineQuotient h).ker := by
  apply isPGroup_iff_pow_pow_eq_one.mpr
  intro g
  refine ⟨1, ?_⟩
  obtain ⟨t, ht⟩ := affineQuotient_spec h g.val
  have hq : affineQuotient h g.val = 1 := g.property
  rw [hq] at ht
  have ht' (i : Fin 3) (v : Vector) :
      g.val.val.val (point (i,v)) = point (i,v + t i) := by
    simpa using ht i v
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro x
  obtain ⟨⟨i,v⟩, rfl⟩ := point.surjective x
  change g.val.val.val (g.val.val.val (point (i,v))) = point (i,v)
  rw [ht', ht']
  apply congrArg point
  apply congrArg (fun w : Vector => (i,w))
  ext j
  change (v j + t i j) + t i j = v j
  have hz : ∀ z : ZMod 2, z + z = 0 := by decide
  rw [add_assoc, hz, add_zero]

end Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction
