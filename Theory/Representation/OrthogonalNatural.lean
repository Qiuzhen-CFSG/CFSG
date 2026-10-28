module

public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Natural actions and characteristic-two projectivization of orthogonal groups

The natural representation is restriction of the actual quadratic isometries.
A scalar isometry of a form representing one has scalar square one. In
characteristic two this scalar is one, so projectivization is an isomorphism
and the natural action descends, without losing the quadratic form.

Sources: GLS3 §2.7 and Aschbacher--Smith C.1.30 (printed p.135).
-/

@[expose] public noncomputable section

namespace ClassicalOrthogonal

open Theory.AlgebraicGroup

universe u
variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
variable {Q : QuadraticForm F V} (H : Subgroup (quadraticIsometrySubgroup Q))

/-- Restriction of the defining action of the quadratic isometry group. -/
def subgroupNatural : Representation F H V where
  toFun g := g.val.val.toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The same natural action on the multiplicative version of the additive space. -/
def subgroupNaturalAction : H →* MulAut (Multiplicative V) where
  toFun g := g.val.val.toAddEquiv.toMultiplicative
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem subgroupNaturalAction_apply (g : H) (v : Multiplicative V) :
    Multiplicative.toAdd (subgroupNaturalAction H g v) =
      subgroupNatural H g (Multiplicative.toAdd v) := rfl

/-- The full quadratic form, rather than only its polarization, is preserved. -/
theorem subgroupNatural_preserves (g : H) (v : V) :
    Q (subgroupNatural H g v) = Q v :=
  (mem_quadraticIsometrySubgroup Q g.val.val).mp g.val.prop v

/-- No nonidentity isometry acts trivially on the natural space. -/
theorem subgroupNaturalAction_injective : Function.Injective (subgroupNaturalAction H) := by
  intro g h he
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  exact congrArg Multiplicative.toAdd (congrArg (fun a => a (Multiplicative.ofAdd v)) he)

/-- The cardinality condition already forces characteristic two. -/
theorem charTwo_of_card [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) : CharP F 2 := by
  let := Fintype.ofFinite F
  exact charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hF)

variable (Q) [CharP F 2]

/-- All elementary scalar isometries are trivial in characteristic two. -/
theorem elementaryScalarSubgroup_eq_bot_charTwo : elementaryScalarSubgroup Q = ⊥ := by
  apply le_antisymm _ bot_le
  rintro g ⟨c, hc, hg⟩
  have hc1 : c = 1 := CharTwo.sq_injective (by simpa using hc)
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  simpa [hc1] using hg v

/-- Omega and its projective scalar quotient agree in characteristic two. -/
def elementaryProjectiveEquiv : elementarySubgroup Q ≃* ProjectiveElementary Q :=
  MulEquiv.ofBijective (projectiveElementaryMap Q)
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by
        rw [projectiveElementaryMap_kernel, elementaryScalarSubgroup_eq_bot_charTwo]),
      projectiveElementaryMap_surjective Q⟩

@[simp] theorem elementaryProjectiveEquiv_apply (g : elementarySubgroup Q) :
    elementaryProjectiveEquiv Q g = projectiveElementaryMap Q g := rfl

/-- The descended action is obtained using the inverse of the actual quotient map. -/
def projectiveElementaryNatural : Representation F (ProjectiveElementary Q) V :=
  (subgroupNatural (elementarySubgroup Q)).comp (elementaryProjectiveEquiv Q).symm.toMonoidHom

@[simp] theorem projectiveElementaryNatural_mk (g : elementarySubgroup Q) (v : V) :
    projectiveElementaryNatural Q (projectiveElementaryMap Q g) v = g.val.val v := by
  change subgroupNatural (elementarySubgroup Q)
    ((elementaryProjectiveEquiv Q).symm (elementaryProjectiveEquiv Q g)) v = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- Projectivization retains the full quadratic form on the natural space. -/
theorem projectiveElementaryNatural_preserves (g : ProjectiveElementary Q) (v : V) :
    Q (projectiveElementaryNatural Q g v) = Q v :=
  subgroupNatural_preserves (elementarySubgroup Q) _ _

namespace Minus

/-- Scalar isometries of a form representing one vanish in characteristic two. -/
theorem scalarSubgroup_eq_bot_charTwo (hQ : ∃ v, Q v = 1) : scalarSubgroup F V Q = ⊥ := by
  apply le_antisymm _ bot_le
  rintro g ⟨c, hc⟩
  obtain ⟨v, hv⟩ := hQ
  have hg := (mem_quadraticIsometrySubgroup Q g.val.val).mp g.val.prop v
  rw [hc, Q.map_smul, hv] at hg
  have hc2 : (c : F) ^ 2 = 1 := by simpa [pow_two] using hg
  have hc1 : (c : F) = 1 := CharTwo.sq_injective (by simpa using hc2)
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro w
  simpa [hc1] using hc w

/-- The quotient map from the orthogonal commutator group is an isomorphism. -/
def omegaProjectiveEquiv (hQ : ∃ v, Q v = 1) : Omega F V Q ≃* ProjectiveOmega F V Q :=
  MulEquiv.ofBijective (QuotientGroup.mk' (scalarSubgroup F V Q))
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by
        rw [QuotientGroup.ker_mk', scalarSubgroup_eq_bot_charTwo Q hQ]),
      QuotientGroup.mk'_surjective _⟩

omit [CharP F 2] in
/-- The minus model represents one on its anisotropic plane. -/
theorem quadraticForm_represents_one [Finite F] (r : ℕ) :
    ∃ v, quadraticForm F r v = 1 := by
  refine ⟨(0, (1, 0)), ?_⟩
  simp [quadraticForm, form_apply, plane, QuadraticMap.linMulLin_apply]

/-- The concrete minus Omega carrier and its projective model are isomorphic. -/
def minusProjectiveEquiv [Finite F] (r : ℕ) :
    Omega F (Space F (r - 1)) (quadraticForm F r) ≃* ClassicalGroup.POmegaMinus r F :=
  omegaProjectiveEquiv (quadraticForm F r) (quadraticForm_represents_one r)

/-- Natural action of the projective orthogonal commutator group. -/
def projectiveOmegaNatural (hQ : ∃ v, Q v = 1) : Representation F (ProjectiveOmega F V Q) V :=
  (subgroupNatural (Omega F V Q)).comp (omegaProjectiveEquiv Q hQ).symm.toMonoidHom

@[simp] theorem projectiveOmegaNatural_mk (hQ : ∃ v, Q v = 1)
    (g : Omega F V Q) (v : V) :
    projectiveOmegaNatural Q hQ (QuotientGroup.mk' (scalarSubgroup F V Q) g) v =
      g.val.val v := by
  change subgroupNatural (Omega F V Q)
    ((omegaProjectiveEquiv Q hQ).symm (omegaProjectiveEquiv Q hQ g)) v = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- The descended minus action also preserves quadratic values. -/
theorem projectiveOmegaNatural_preserves (hQ : ∃ v, Q v = 1)
    (g : ProjectiveOmega F V Q) (v : V) :
    Q (projectiveOmegaNatural Q hQ g v) = Q v :=
  subgroupNatural_preserves (Omega F V Q) _ _

end Minus

/-- The split Omega subgroup, including the dimension-two torus. The
Siegel-generator construction in `OmegaPlus` is used in rank at least two;
in rank one Omega is the commutator subgroup of the hyperbolic plane's
orthogonal group. See GLS3 §2.7, printed pp.87–88. -/
def omegaPlusWithTorus (r : ℕ) (F : Type u) [Field F] :
    Subgroup (quadraticIsometrySubgroup (formD r F)) :=
  if r = 1 then Minus.Omega F (VectorD r F) (formD r F) else elementarySubgroup (formD r F)

omit [CharP F 2] in
@[simp] theorem omegaPlusWithTorus_one :
    omegaPlusWithTorus 1 F = Minus.Omega F (VectorD 1 F) (formD 1 F) := by
  simp [omegaPlusWithTorus]

omit [CharP F 2] in
/-- Above dimension two this is exactly the existing split Omega model. -/
theorem omegaPlusWithTorus_eq (r : ℕ) (hr : 2 ≤ r) :
    omegaPlusWithTorus r F = elementarySubgroup (formD r F) := by
  simp [omegaPlusWithTorus, show r ≠ 1 by omega]

end ClassicalOrthogonal
