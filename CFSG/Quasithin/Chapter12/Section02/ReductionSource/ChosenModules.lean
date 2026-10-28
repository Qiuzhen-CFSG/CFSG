module
public import CFSG.Quasithin.Chapter12.Section02.SourceHypotheses
public import CFSG.Quasithin.Chapter6.SourceDefs
public import Theory.Representation.BinaryOffender.IrreducibleSection.DiagonalProduct

/-!
# The surviving single A₅ module in the source reduction

The original chosen Irr⁺ subspace is identified with its subgroup V by its
actual inclusion into R₂(LT). Conjugation models on V therefore transport
to exactly that section, with the original L/O₂(L) quotient map. A diagonal
double copy contradicts irreducibility modulo the fixed vectors. Hence the
one-or-two-copy outcome of the earlier rank-one reduction is a single A₅
module, of binary rank four.

This proves the representation step needed in 12.2.2(3d); it does not assert
the earlier global reduction 6.2.20 or the remaining six module alternatives.
The same generic exclusion applies to any proposed diagonal double model.
Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
Theorem 12.2.2, p.795, using Definition A.1.40 and the 6.2.20 alternative.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The literal ambient inclusion of the chosen subspace into V. -/
def spaceMap : Multiplicative D.space →* V where
  toFun v := ⟨v.toAdd.val.toMul.val, by
    exact D.image_eq.le (mem_map_of_mem _ (mem_map_of_mem _ v.toAdd.property))⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The image equality of the original choice makes that inclusion bijective. -/
theorem spaceMap_bijective : Function.Bijective D.spaceMap := by
  constructor
  · intro a b h
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun v : V => (v : G)) h
  · intro v
    have hv := D.image_eq.ge v.property
    obtain ⟨a, ⟨b, hb, rfl⟩, hv⟩ := hv
    exact ⟨Multiplicative.ofAdd ⟨Additive.ofMul b, hb⟩, Subtype.ext hv⟩

/-- Coordinates on V retain its original inclusion into the ambient group. -/
def spaceEquiv : Multiplicative D.space ≃* V :=
  MulEquiv.ofBijective D.spaceMap D.spaceMap_bijective

theorem spaceEquiv_apply (v : D.space) :
    (D.spaceEquiv (Multiplicative.ofAdd v) : G) = v.val.toMul.val := by rfl

include D

private def linearOfMultiplicative
    {S W : Type*} [AddCommGroup S] [Module (ZMod 2) S]
    [AddCommGroup W] [Module (ZMod 2) W]
    (f : Multiplicative S ≃* Multiplicative W) : S ≃ₗ[ZMod 2] W :=
  let eA : S ≃+ W := {
    toFun v := (f (Multiplicative.ofAdd v)).toAdd
    invFun w := (f.symm (Multiplicative.ofAdd w)).toAdd
    left_inv v := congrArg Multiplicative.toAdd (f.symm_apply_apply (Multiplicative.ofAdd v))
    right_inv w := congrArg Multiplicative.toAdd (f.apply_symm_apply (Multiplicative.ofAdd w))
    map_add' v w := congrArg Multiplicative.toAdd (f.map_mul
      (Multiplicative.ofAdd v) (Multiplicative.ofAdd w)) }
  eA.toLinearEquiv (ZMod.map_smul eA)

private def modelSpace {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (f : V ≃* Multiplicative W) : D.space ≃ₗ[ZMod 2] W :=
  linearOfMultiplicative (S := D.space) (W := W) (D.spaceEquiv.trans f)

private def modelActor {A : Type*} [Group A] (a : (L ⧸ pCore 2 L) ≃* A) :
    L.subgroupOf (L ⊔ (T : Subgroup G)) →* A := a.toMonoidHom.comp
    ((QuotientGroup.mk' (pCore 2 L)).comp (subgroupOfEquivOfLe le_sup_left).toMonoidHom)

private theorem modelSpace_action
    {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) A W) (a : (L ⧸ pCore 2 L) ≃* A)
    (f : V ≃* Multiplicative W)
    (hf : ∀ (l : L) (v : V),
      ((f.symm (Multiplicative.ofAdd (σ (a (QuotientGroup.mk' (pCore 2 L) l))
        (f v).toAdd))) : G) = (l : G) * (v : G) * (l : G)⁻¹)
    (g : L.subgroupOf (L ⊔ (T : Subgroup G))) (v : D.space) :
    modelSpace D f ((invariantSubspace _ _ _ D.irrPlus.isIrrPlus.choose).toRepresentation g v) =
      σ (modelActor (T := T) a g) (modelSpace D f v) := by
  have hh := hf ((subgroupOfEquivOfLe le_sup_left) g) (D.spaceEquiv (Multiplicative.ofAdd v))
  change f (D.spaceEquiv (Multiplicative.ofAdd _)) =
    Multiplicative.ofAdd (σ (modelActor (T := T) a g) (f (D.spaceEquiv (Multiplicative.ofAdd v))).toAdd)
  apply f.symm.injective
  apply Subtype.ext
  rw [MulEquiv.symm_apply_apply]
  exact hh.symm

/-- No chosen Irr⁺ section can carry a diagonal double conjugation model. -/
theorem not_double_conjugation_model
    {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) A W) :
    ¬ Chapter6.Source.IsConjugationModel L V (σ.prod σ) := by
  rintro ⟨a, f, hf⟩
  apply D.irrPlus.isIrrPlus.not_diagonal_product _ σ (modelActor (T := T) a) (modelSpace D f)
  exact modelSpace_action D (σ.prod σ) a f hf

/-- The genuine one-or-two-copy conclusion from the earlier rank-one branch
reduces to a single A₅ module on the same V and same L/O₂(L). -/
theorem one_a5_of_one_or_two
    (h : Chapter6.Source.IsOneOrTwoA5Modules L V) :
    Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module := by
  rcases h with h | h
  · exact h
  · exact (D.not_double_conjugation_model Chapter6.Source.a5Module h).elim


/-- In this branch the original chosen binary subspace has rank four. -/
theorem a5_space_finrank_of_one_or_two
    (h : Chapter6.Source.IsOneOrTwoA5Modules L V) :
    Module.finrank (ZMod 2) D.space = 4 := by
  obtain ⟨a, f, hf⟩ := D.one_a5_of_one_or_two h
  exact (modelSpace D f).finrank_eq.trans (by
    simpa using BinaryPermutation.finrank_natural_odd (Fin 5) (by decide))

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
