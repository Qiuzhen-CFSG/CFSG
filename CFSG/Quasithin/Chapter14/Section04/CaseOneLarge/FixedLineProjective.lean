module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineCoefficient
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.Alternating.Aut
public import Theory.Mathieu.M22.ValueBoundParabolics.SmallQuotients
public import Theory.SpecificGroups.SymmetricFive.ElementaryFiveNormalizer

/-!
# The faithful five-point coefficient action of the original SL₂(4) double

A scalar isometry of the doubled natural action is trivial. The proof uses
only one SL₂ factor: its transvections annihilate same-column pairings, and
its diagonal torus, combined with a scalar, annihilates cross-column pairings
unless that scalar is one. Nondegeneracy excludes that outcome.

Normalize each GL₂(4) coefficient by its determinant. This gives the actual
projective semilinear action, identified with S₅ through SL₂(4) = A₅ and its
automorphisms. The invariant form makes this action faithful on the whole
coefficient image. The field kernel is precisely its even part, isomorphic
to the original component centralizer, and inherits trivial two-core.

The original elementary actor has a nontrivial even coefficient from its
component centralizer and an odd coefficient from its field action. Its
five-point image therefore has order four. An elementary subgroup of a
five-cycle normalizer has order at most two, excluding containment in such
a normalizer. The literal quotient, determinant coordinates and field maps
are retained throughout.

`CatalogueExclusion.source_large_projective_remainder_of_mixed_size` applies
these facts to the original flag. Recognition of the remaining coefficient
subgroups and unmarked exchanged constituents remains necessary for the
large-case assembly.

Source: Aschbacher--Smith G.11.8, printed pp.368--369, and 14.4.2,
printed pp.1006--1007 (refs/quasithin.pdf).
-/

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
public noncomputable section
open Subgroup Module Representation Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineProjective
open FixedLineSemilinear
local instance : Algebra (ZMod 2) Field := ZMod.algebra _ 2

private theorem unit_cube (c : Fieldˣ) : c ^ 3 = 1 := by
  have hc : Nat.card Fieldˣ = 3 := by
    rw [Nat.card_units,GaloisField.card 2 2 (by decide)]
    decide
  simpa only [hc] using pow_card_eq_one' (x := c)

private def normalize : LinearGroup →* SL(2,Field) where
  toFun g := ⟨(Matrix.GeneralLinearGroup.det g : Field) • g.val, by
    rw [Matrix.det_smul,Fintype.card_fin]
    have hh := congrArg Units.val (unit_cube (Matrix.GeneralLinearGroup.det g))
    change (Matrix.GeneralLinearGroup.det g : Field) ^ 3 = 1 at hh
    change (Matrix.GeneralLinearGroup.det g : Field) ^ 2 * (Matrix.GeneralLinearGroup.det g : Field) = 1
    simpa only [pow_succ] using hh⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' g h := by
    apply Subtype.ext
    change ((Matrix.GeneralLinearGroup.det (g*h) : Field) • (g*h).val) =
      ((Matrix.GeneralLinearGroup.det g : Field) • g.val) *
        ((Matrix.GeneralLinearGroup.det h : Field) • h.val)
    rw [map_mul,Units.val_mul,Units.val_mul,smul_mul_smul_comm]

private def projective : Gamma →* SL2AutomorphismNatural.Parameters (F := Field) :=
  SemidirectProduct.map normalize (MonoidHom.id _) (by
    intro σ
    apply MonoidHom.ext
    intro g
    apply Subtype.ext
    ext i j
    change ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.coefficientAction Field σ g) : Field) *
      σ (g.val i j)) = σ ((Matrix.GeneralLinearGroup.det g : Field) * g.val i j)
    rw [map_mul]
    congr 1
    exact (σ.map_det g.val).symm)

private abbrev Space := Fin 2 → Plane
private def column (i : Fin 2) (v : Plane) : Space := fun j k => if k=i then v j else 0
private def act (g : SL(2,Field)) (v : Space) : Space := fun i => g.val.mulVec (v i)

private theorem column_smul (i : Fin 2) (c : Field) (v : Plane) :
    column i (c • v) = c • column i v := by
  funext j k
  by_cases h : k=i <;> simp [column,h]

private theorem column_sum (v : Space) : v = column 0 (fun i => v i 0) + column 1 (fun i => v i 1) := by
  funext j k
  fin_cases k <;> simp [column]

private theorem invariant_column_zero
    (B : LinearMap.BilinForm (ZMod 2) Space)
    (hB : ∀ g u v, B (act g u) (act g v) = B u v)
    (v w : Plane) : B (column 0 v) (column 0 w) = 0 := by
  let g : SL(2,Field) := SpecialLinearGroup.transvection zero_ne_one 1
  have h0 (v : Plane) : act g (column 0 v) = column 0 v := by
    funext j k
    fin_cases k <;>
      simp [act,g,SpecialLinearGroup.transvection_coe,Matrix.mulVec,dotProduct,Fin.sum_univ_two,column]
  have h1 (w : Plane) : act g (column 1 w) = column 1 w + column 0 w := by
    funext j k
    fin_cases k <;>
      simp [act,g,SpecialLinearGroup.transvection_coe,Matrix.mulVec,dotProduct,Fin.sum_univ_two,column]
  have hh := hB g (column 0 v) (column 1 w)
  rw [h0,h1,map_add] at hh
  exact add_eq_left.mp hh

private theorem scalar_isometry_eq_one
    (B : LinearMap.BilinForm (ZMod 2) Space) (hnd : B.Nondegenerate)
    (hB : ∀ g u v, B (act g u) (act g v) = B u v)
    (c : Field) (hc : c ≠ 0) (hiso : ∀ u v, B (c • u) (c • v) = B u v) : c = 1 := by
  by_contra hc1
  have hc2 : c*c-1 ≠ 0 := by
    intro he
    exact hc1 (CharTwo.sq_injective (by simpa only [pow_two,one_mul] using sub_eq_zero.mp he))
  let g := SpecialLinearGroup.diag2 c hc
  have he0 (v : Plane) : c • act g (column 0 v) = column 0 ((c*c) • v) := by
    funext j k
    fin_cases k <;>
      simp [act,g,SpecialLinearGroup.diag2_coe',Matrix.mulVec,dotProduct,Fin.sum_univ_two,column,mul_assoc]
  have he1 (v : Plane) : c • act g (column 1 v) = column 1 v := by
    funext j k
    fin_cases k <;>
      simp [act,g,SpecialLinearGroup.diag2_coe',Matrix.mulVec,dotProduct,Fin.sum_univ_two,column,hc,mul_assoc]
  have hz (v w : Plane) : B (column 0 v) (column 1 w) = 0 := by
    let z : Plane := (c*c-1)⁻¹ • v
    have hh := (hiso (act g (column 0 z)) (act g (column 1 w))).trans
      (hB g (column 0 z) (column 1 w))
    rw [he0,he1] at hh
    have hdiff : column 0 ((c*c) • z) - column 0 z = column 0 v := by
      rw [column_smul]
      calc
        (c*c) • column 0 z - column 0 z = (c*c-1) • column 0 z := by rw [sub_smul,one_smul]
        _ = column 0 v := by rw [show column 0 z = (c*c-1)⁻¹ • column 0 v from column_smul 0 _ v,
        smul_smul,mul_inv_cancel₀ hc2,one_smul]
    have hz' : B (column 0 ((c*c) • z) - column 0 z) (column 1 w) = 0 := by
      rw [map_sub,LinearMap.sub_apply,hh,sub_self]
    rwa [hdiff] at hz'
  have he : column 0 (fun _ => (1 : Field)) = 0 := hnd.1 _ (by
    intro y
    rw [column_sum y,map_add,invariant_column_zero B hB,hz,zero_add])
  have hh := congrArg (fun x : Space => x 0 0) he
  simpa [column] using hh

private theorem projective_kernel (g : Gamma) (hg : projective g = 1) :
    g.right = 1 ∧ ∃ c : Field, c ≠ 0 ∧ g.left.val = c • (1 : Matrix (Fin 2) (Fin 2) Field) := by
  have hr : g.right = 1 := congrArg SemidirectProduct.right hg
  have hl : (normalize g.left).val = 1 := congrArg (fun z : SL2AutomorphismNatural.Parameters (F := Field) => z.left.val) hg
  let c : Field := (Matrix.GeneralLinearGroup.det g.left : Field)
  have hc : c ≠ 0 := (Matrix.GeneralLinearGroup.det g.left).ne_zero
  refine ⟨hr,c⁻¹,inv_ne_zero hc,?_⟩
  change c • g.left.val = 1 at hl
  calc
    g.left.val = c⁻¹ • (c • g.left.val) := by rw [smul_smul,inv_mul_cancel₀ hc,one_smul]
    _ = c⁻¹ • 1 := by rw [hl]

variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) D W} {H : Subgroup D}

private theorem component_action (a : Coordinates ρ H) (h : H) (w : W) :
    a.space (ρ h w) = act (a.component h) (a.space w) := by
  have hc : a.coefficient h = 1 := MonoidHom.mem_ker.mp (a.coefficient_kernel.symm ▸ h.property)
  funext i
  rw [a.equivariant,hc,a.component_marking]
  change (∑ j : Fin 2, (1 : Matrix (Fin 2) (Fin 2) Field) i j •
    SL2AutomorphismNatural.action (MulAut.conj (a.component h)) (a.space w j)) = _
  simp only [SL2AutomorphismNatural.action_conj]
  fin_cases i <;> simp [act,Matrix.one_apply]

private theorem scalar_coefficient_eq_one (a : Coordinates ρ H)
    (B : LinearMap.BilinForm (ZMod 2) W) (hnd : B.Nondegenerate)
    (hB : ∀ g u v, B (ρ g u) (ρ g v) = B u v)
    (g : centralizer (H : Set D)) (c : Field) (hc : c ≠ 0)
    (hscalar : (a.centralizerLinear g).val = c • (1 : Matrix (Fin 2) (Fin 2) Field)) : c = 1 := by
  let B' := B.comp a.space.symm.toLinearMap a.space.symm.toLinearMap
  have hnd' : B'.Nondegenerate := by
    constructor
    · intro u hu
      apply a.space.symm.injective
      have he : a.space.symm u = 0 := hnd.1 _ (by
        intro w
        have hh := hu (a.space w)
        change B (a.space.symm u) (a.space.symm (a.space w)) = 0 at hh
        simpa only [a.space.symm_apply_apply] using hh)
      simpa using he
    · intro u hu
      apply a.space.symm.injective
      have he : a.space.symm u = 0 := hnd.2 _ (by
        intro w
        have hh := hu (a.space w)
        change B (a.space.symm (a.space w)) (a.space.symm u) = 0 at hh
        simpa only [a.space.symm_apply_apply] using hh)
      simpa using he
  have hact (k : SL(2,Field)) (z : Space) :
      a.space.symm (act k z) = ρ (a.component.symm k : H) (a.space.symm z) := by
    apply a.space.injective
    rw [a.space.apply_symm_apply,component_action,a.space.apply_symm_apply,a.component.apply_symm_apply]
  have hB' (k : SL(2,Field)) (u v : Space) : B' (act k u) (act k v) = B' u v := by
    change B (a.space.symm (act k u)) (a.space.symm (act k v)) = _
    rw [hact,hact]
    exact hB _ _ _
  have hsc (z : Space) : a.space.symm (c • z) = ρ (g:D) (a.space.symm z) := by
    apply a.space.injective
    rw [a.space.apply_symm_apply]
    funext i
    rw [a.centralizer_action,a.space.apply_symm_apply,hscalar]
    fin_cases i <;> simp
  exact scalar_isometry_eq_one B' hnd' hB' c hc (fun u v => by
    change B (a.space.symm (c • u)) (a.space.symm (c • v)) = _
    rw [hsc,hsc]
    exact hB _ _ _)

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineProjective

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineSemilinear.Coordinates
open FixedLineProjective
variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) D W} {H : Subgroup D} (a : Coordinates ρ H)

/-- The projective coefficient action, retaining the original field automorphism. -/
def projectiveCoefficient : a.coefficient.range →* SL2AutomorphismNatural.Parameters (F := Field) :=
  projective.comp a.coefficient.range.subtype

/-- The projective coefficient's field map is exactly the original one. -/
theorem projectiveCoefficient_field (b : a.coefficient.range) :
    (a.projectiveCoefficient b).right = a.coefficientField b := (a.coefficientField_apply b).symm

/-- The linear projective coordinate is determinant normalization of the original coefficient matrix. -/
theorem projectiveCoefficient_linear (b : a.coefficient.range) :
    (a.projectiveCoefficient b).left.val =
      (Matrix.GeneralLinearGroup.det (b : Gamma).left : Field) • (b : Gamma).left.val := by rfl

/-- The original invariant nondegenerate form excludes scalar coefficients.
Thus projectivizing the literal coefficient image loses no element. -/
theorem projectiveCoefficient_injective
    (B : LinearMap.BilinForm (ZMod 2) W) (hnd : B.Nondegenerate)
    (hB : ∀ g u v, B (ρ g u) (ρ g v) = B u v) :
    Function.Injective a.projectiveCoefficient := by
  apply (injective_iff_map_eq_one _).mpr
  intro b hb
  obtain ⟨hf,c,hc,hscalar⟩ := projective_kernel b.val hb
  have hbfield : a.coefficientField b = 1 := (a.coefficientField_apply b).trans hf
  let g : centralizer (H : Set D) := ⟨a.coefficientLift b,a.coefficientLift_centralizer b hbfield⟩
  have hmark : a.coefficient g = b.val := congrArg Subtype.val (a.coefficientLift_marking b)
  have hlin : (a.centralizerLinear g).val = c • (1 : Matrix (Fin 2) (Fin 2) Field) := by
    rw [a.centralizerLinear_apply,hmark]
    exact hscalar
  have hc1 := scalar_coefficient_eq_one a B hnd hB g c hc hlin
  apply Subtype.ext
  apply SemidirectProduct.ext ?_ hf
  apply Units.ext
  change b.val.left.val = (1 : Matrix (Fin 2) (Fin 2) Field)
  simpa only [hc1,one_smul] using hscalar

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineSemilinear.Coordinates
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineProjective
open FixedLineSemilinear
open Representation.SL2AutomorphismNatural

private def specialAlternating : SL(2,Field) ≃* alternatingGroup (Fin 5) :=
  (Theory.PSL2.sl2QuotientEquiv Field).trans
    (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
      (GaloisField.card 2 2 (by decide))).some

private def automorphismFive : Equiv.Perm (Fin 5) ≃* MulAut (alternatingGroup (Fin 5)) :=
  MulEquiv.ofBijective MulAut.conjNormal
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by decide) (by decide))

private def fiveEquiv : Parameters (F := Field) ≃* Equiv.Perm (Fin 5) :=
  parameterEquiv.trans ((MulAut.congr specialAlternating).trans automorphismFive.symm)

private theorem fiveEquiv_inner (g : SL(2,Field)) :
    fiveEquiv (SemidirectProduct.inl g) = (specialAlternating g : Equiv.Perm (Fin 5)) := by
  apply automorphismFive.injective
  change automorphismFive (automorphismFive.symm ((MulAut.congr specialAlternating)
    (parameterEquiv (SemidirectProduct.inl g)))) = _
  rw [automorphismFive.apply_symm_apply]
  have hh : parameterEquiv (SemidirectProduct.inl g) = MulAut.conj g := by
    change parameterAut (SemidirectProduct.inl g) = MulAut.conj g
    exact SemidirectProduct.lift_inl _ _ _ _
  rw [hh]
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  change (specialAlternating (g * specialAlternating.symm x * g⁻¹) : Equiv.Perm (Fin 5)) =
    (specialAlternating g : Equiv.Perm (Fin 5)) * x * (specialAlternating g : Equiv.Perm (Fin 5))⁻¹
  simp

private theorem fiveEquiv_even_iff (g : Parameters (F := Field)) :
    fiveEquiv g ∈ alternatingGroup (Fin 5) ↔ g.right = 1 := by
  constructor
  · intro hg
    let k := specialAlternating.symm ⟨fiveEquiv g,hg⟩
    have he : g = SemidirectProduct.inl k := by
      apply fiveEquiv.injective
      rw [fiveEquiv_inner]
      exact (congrArg Subtype.val (specialAlternating.apply_symm_apply ⟨fiveEquiv g,hg⟩)).symm
    rw [he]
    rfl
  · intro hg
    have he : g = SemidirectProduct.inl g.left := SemidirectProduct.ext rfl hg
    rw [he,fiveEquiv_inner]
    exact (specialAlternating g.left).property
end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineProjective

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineSemilinear.Coordinates
open FixedLineProjective
variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) D W} {H : Subgroup D} (a : Coordinates ρ H)

/-- The coefficient action on five projective points, with its original quotient retained. -/
def coefficientFive : a.coefficient.range →* Equiv.Perm (Fin 5) :=
  fiveEquiv.toMonoidHom.comp a.projectiveCoefficient

/-- The actual form makes the five-point coefficient action faithful. -/
theorem coefficientFive_injective
    (B : LinearMap.BilinForm (ZMod 2) W) (hnd : B.Nondegenerate)
    (hB : ∀ g u v, B (ρ g u) (ρ g v) = B u v) :
    Function.Injective a.coefficientFive :=
  fiveEquiv.injective.comp (a.projectiveCoefficient_injective B hnd hB)

/-- The even coefficient permutations are exactly the original linear coefficients. -/
theorem coefficientFive_even_iff (b : a.coefficient.range) :
    a.coefficientFive b ∈ alternatingGroup (Fin 5) ↔ a.coefficientField b = 1 := by
  rw [←a.projectiveCoefficient_field]
  exact fiveEquiv_even_iff _

/-- The original component quotient is now a faithful concrete five-point subgroup. -/
def quotientFiveEquiv [H.Normal]
    (B : LinearMap.BilinForm (ZMod 2) W) (hnd : B.Nondegenerate)
    (hB : ∀ g u v, B (ρ g u) (ρ g v) = B u v) :
    D ⧸ H ≃* a.coefficientFive.range :=
  a.quotientEquiv.trans (MonoidHom.ofInjective (a.coefficientFive_injective B hnd hB))

/-- The original centralizer's linear kernel is the even part of that same image. -/
theorem coefficientFive_linear_image :
    a.coefficientField.ker.map a.coefficientFive =
      a.coefficientFive.range ⊓ alternatingGroup (Fin 5) := by
  ext x
  constructor
  · rintro ⟨b,hb,rfl⟩
    exact ⟨⟨b,rfl⟩,(a.coefficientFive_even_iff b).mpr hb⟩
  · rintro ⟨⟨b,rfl⟩,hb⟩
    exact ⟨b,(a.coefficientFive_even_iff b).mp hb,rfl⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineSemilinear.Coordinates
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineSemilinear.Coordinates
open FixedLineProjective Theory.GroupTheory
open scoped IsMulCommutative
variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) D W} {H : Subgroup D} (a : Coordinates ρ H)

/-- The whole group acts on the five coefficient points through the literal coefficient map. -/
def ambientFive : D →* Equiv.Perm (Fin 5) :=
  a.coefficientFive.comp a.coefficient.rangeRestrict

theorem ambientFive_apply (g : D) :
    a.ambientFive g = a.coefficientFive (a.coefficient.rangeRestrict g) := by rfl

theorem ambientFive_even_iff (g : D) :
    a.ambientFive g ∈ alternatingGroup (Fin 5) ↔ a.ambientField g = 1 := by
  rw [a.ambientFive_apply,a.coefficientFive_even_iff,a.coefficientField_apply,a.ambientField_apply]
  rfl

/-- The five-point action has precisely the original component as kernel. -/
theorem ambientFive_kernel
    (B : LinearMap.BilinForm (ZMod 2) W) (hnd : B.Nondegenerate)
    (hB : ∀ g u v, B (ρ g u) (ρ g v) = B u v) : a.ambientFive.ker = H := by
  apply Eq.trans _ a.coefficient_kernel
  ext g
  change a.coefficientFive (a.coefficient.rangeRestrict g) = 1 ↔ a.coefficient g = 1
  rw [←a.coefficientFive.map_one,(a.coefficientFive_injective B hnd hB).eq_iff]
  exact Subtype.ext_iff

/-- The original component centralizer is the even part of the faithful coefficient image. -/
def centralizerFiveEquiv
    (B : LinearMap.BilinForm (ZMod 2) W) (hnd : B.Nondegenerate)
    (hB : ∀ g u v, B (ρ g u) (ρ g v) = B u v) :
    centralizer (H : Set D) ≃* (a.coefficientFive.range ⊓ alternatingGroup (Fin 5) : Subgroup (Equiv.Perm (Fin 5))) :=
  a.centralizerCoefficientEquiv.trans
    ((Subgroup.equivMapOfInjective a.coefficientField.ker a.coefficientFive
      (a.coefficientFive_injective B hnd hB)).trans
      (MulEquiv.subgroupCongr a.coefficientFive_linear_image))

/-- Trivial original two-core is retained in the literal even coefficient image. -/
theorem coefficientFive_even_twoCore
    (B : LinearMap.BilinForm (ZMod 2) W) (hnd : B.Nondegenerate)
    (hB : ∀ g u v, B (ρ g u) (ρ g v) = B u v)
    (hc : pCore 2 D = ⊥) :
    pCore 2 (a.coefficientFive.range ⊓ alternatingGroup (Fin 5) : Subgroup (Equiv.Perm (Fin 5))) = ⊥ := by
  rw [←pCore_map_iso 2 (a.centralizerFiveEquiv B hnd hB),
    a.centralizer_twoCore hc,Subgroup.map_bot]

/-- The original actor has an order-four image on the coefficient points.
Its even involution comes from the component centralizer and its odd element
from the field automorphism forced by the single fixed line. -/
theorem actor_five_card [Finite D] [FiniteDimensional (ZMod 2) W]
    (B : LinearMap.BilinForm (ZMod 2) W) (hnd : B.Nondegenerate)
    (hB : ∀ g u v, B (ρ g u) (ρ g v) = B u v)
    (X : Subgroup D) [IsElementaryAbelian 2 X]
    (v : W) (hv : v ≠ 0)
    (hf : BinaryOffender.fixedSpace ρ X = Submodule.span (ZMod 2) {v})
    (hY : Nat.card ((centralizer (H : Set D)).subgroupOf X) = 2) :
    Nat.card (X.map a.ambientFive) = 4 := by
  let U := X.map a.ambientFive
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map a.ambientFive
  have hb : Nat.card U ≤ 4 := (primeRank_le_iff_elementary_card_le _).mp
    Sporadic.Mathieu.M22ValueBound.SmallQuotients.symmetricFive_primeRank_le_two U inferInstance
  let β := Equiv.Perm.sign.comp U.subtype
  have hYne : (centralizer (H : Set D)).subgroupOf X ≠ ⊥ := by
    intro he
    rw [he,Subgroup.card_bot] at hY
    omega
  have hex : ∃ y : X, y ∈ (centralizer (H : Set D)).subgroupOf X ∧ y ≠ 1 := by
    by_contra! hh
    apply hYne
    apply bot_unique
    intro y hy
    exact hh y hy
  obtain ⟨y,hy,hyn⟩ := hex
  let t : U := ⟨a.ambientFive y,Subgroup.mem_map_of_mem a.ambientFive y.property⟩
  have ht1 : t ≠ 1 := by
    intro ht
    have hc : a.coefficient.rangeRestrict y = 1 :=
      a.coefficientFive_injective B hnd hB ((congrArg Subtype.val ht).trans a.coefficientFive.map_one.symm)
    have ha : a.automorphism y = 1 := MonoidHom.mem_ker.mp (a.automorphism_kernel.symm ▸ hy)
    have he : (y:D) = 1 := a.faithful (by
      rw [MonoidHom.prod_apply,MonoidHom.prod_apply,ha,map_one,map_one]
      exact Prod.ext rfl (congrArg Subtype.val hc))
    exact hyn (Subtype.ext he)
  have hte : (t : Equiv.Perm (Fin 5)) ∈ alternatingGroup (Fin 5) := by
    apply (a.ambientFive_even_iff y).mpr
    rw [a.ambientField_apply]
    exact a.centralizer_field ⟨y,hy⟩
  have hk : β.ker ≠ ⊥ := by
    intro he
    exact ht1 (Subgroup.mem_bot.mp (he ▸ (show t ∈ β.ker from
      Equiv.Perm.mem_alternatingGroup.mp hte)))
  have hkc : 2 ≤ Nat.card β.ker := (β.ker.one_lt_card_iff_ne_bot.mpr hk)
  obtain ⟨x,hx⟩ := a.actor_field_nontrivial X v hv hf
  let s : U := ⟨a.ambientFive x,Subgroup.mem_map_of_mem a.ambientFive x.property⟩
  have hs : β s ≠ 1 := fun he => hx ((a.ambientFive_even_iff x).mp
    (Equiv.Perm.mem_alternatingGroup.mpr he))
  have hr : β.range ≠ ⊥ := by
    intro he
    exact hs (Subgroup.mem_bot.mp (he ▸ (show β s ∈ β.range from ⟨s,rfl⟩)))
  have hrc : 2 ≤ Nat.card β.range := β.range.one_lt_card_iff_ne_bot.mpr hr
  have hmul := β.ker.card_mul_index
  rw [Subgroup.index_ker] at hmul
  change Nat.card β.ker * Nat.card β.range = Nat.card U at hmul
  change Nat.card U = 4
  nlinarith

/-- The whole coefficient image cannot normalize a five-cycle subgroup.
This excludes the dihedral-ten centralizer branch of G.11.8 at its actual
coefficient action, without recognizing a group merely from its order. -/
theorem coefficientFive_not_le_fiveNormalizer [Finite D] [FiniteDimensional (ZMod 2) W]
    (B : LinearMap.BilinForm (ZMod 2) W) (hnd : B.Nondegenerate)
    (hB : ∀ g u v, B (ρ g u) (ρ g v) = B u v)
    (X : Subgroup D) [IsElementaryAbelian 2 X]
    (v : W) (hv : v ≠ 0)
    (hf : BinaryOffender.fixedSpace ρ X = Submodule.span (ZMod 2) {v})
    (hY : Nat.card ((centralizer (H : Set D)).subgroupOf X) = 2)
    (P : Sylow 5 (Equiv.Perm (Fin 5))) :
    ¬ a.coefficientFive.range ≤ normalizer ((P : Subgroup (Equiv.Perm (Fin 5))) : Set _) := by
  intro hN
  let U := X.map a.ambientFive
  let N := normalizer ((P : Subgroup (Equiv.Perm (Fin 5))) : Set (Equiv.Perm (Fin 5)))
  have hUN : U ≤ N := by
    rintro _ ⟨x,hx,rfl⟩
    exact hN ⟨a.coefficient.rangeRestrict x,rfl⟩
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map a.ambientFive
  let : IsElementaryAbelian 2 (U.subgroupOf N) :=
    IsElementaryAbelian.of_surjective (subgroupOfEquivOfLe hUN).symm.toMonoidHom
      (subgroupOfEquivOfLe hUN).symm.surjective
  have hb := Theory.SpecificGroups.SymmetricFive.FiveNormalizerOvergroups.elementary_normalizer_card_le_two
    P (U.subgroupOf N)
  rw [Nat.card_congr (subgroupOfEquivOfLe hUN).toEquiv] at hb
  have hc := a.actor_five_card B hnd hB X v hv hf hY
  change Nat.card U = 4 at hc
  omega
end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineSemilinear.Coordinates
