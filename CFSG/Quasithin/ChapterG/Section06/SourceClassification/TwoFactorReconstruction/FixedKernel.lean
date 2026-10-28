module

public import CFSG.Quasithin.ChapterG.Section06.ModelLifting
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Statement
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Actions.Displacement
public import Theory.Representation.SmallNaturalMovedDimension
public import Theory.Representation.ResidualMovedGeneration
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.BinaryPermutation.FiveLowRank

/-!
# Recovering the original moved factor from its fixed quotient

The projection is literally the restriction of V → V/C_V(D) to the specified
moved space. A dimension bound makes this surjection injective. For the binary
SL₂ and SL₃ natural rows, two or three conjugates of the marked involution
give exactly the required bound. The resulting action equivalence therefore
lives on the original moved space, and its intersection with C_V(D) is zero.

Source: Aschbacher–Smith, G.6.4 case II, printed p.346, using B.5.6(3), p.105.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterG.Section06.TwoFactorReconstruction
open ChapterB.QuasisimpleSource ChapterB.SourceInduction
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) D V}

/-- Restriction of the original global fixed-quotient map. -/
noncomputable def fixedImageProjection (U : Subrepresentation ρ) :
    U.toSubmodule →ₗ[ZMod 2] ((fixed ρ).quotientImage U).toSubmodule where
  toFun v := ⟨ρ.invariants.mkQ v, ⟨v, v.property, rfl⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [FiniteDimensional (ZMod 2) V] in
theorem fixedImageProjection_surjective (U : Subrepresentation ρ) :
    Function.Surjective (fixedImageProjection U) := by
  rintro ⟨q, v, hv, rfl⟩
  exact ⟨⟨v, hv⟩, rfl⟩

theorem fixedImageProjection_injective_of_dimension (U : Subrepresentation ρ)
    (hd : Module.finrank (ZMod 2) U.toSubmodule ≤
      Module.finrank (ZMod 2) ((fixed ρ).quotientImage U).toSubmodule) :
    Function.Injective (fixedImageProjection U) := by
  have hs := fixedImageProjection_surjective U
  have he : Module.finrank (ZMod 2) U.toSubmodule =
      Module.finrank (ZMod 2) ((fixed ρ).quotientImage U).toSubmodule :=
    le_antisymm hd (LinearMap.finrank_le_finrank_of_surjective hs)
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank he).mpr hs

theorem disjoint_fixed_of_dimension (U : Subrepresentation ρ)
    (hd : Module.finrank (ZMod 2) U.toSubmodule ≤
      Module.finrank (ZMod 2) ((fixed ρ).quotientImage U).toSubmodule) :
    Disjoint U.toSubmodule ρ.invariants := by
  apply disjoint_iff.mpr
  apply bot_unique
  rintro v ⟨hu, hv⟩
  have hz : fixedImageProjection U ⟨v, hu⟩ = 0 := by
    apply Subtype.ext
    exact (Submodule.Quotient.mk_eq_zero _).mpr hv
  exact congrArg Subtype.val
    ((fixedImageProjection_injective_of_dimension U hd) (hz.trans (map_zero _).symm))

/-- The same actor marking and quotient projection recover the whole moved action. -/
noncomputable def liftImageModel {A : Subgroup D} {U : Subrepresentation ρ}
    {B W : Type*} [Group B] [AddCommGroup W] [Module (ZMod 2) W]
    {τ : Representation (ZMod 2) B W}
    (e : ActionEquiv (((fixed ρ).quotientImage U).toRepresentation.comp A.subtype) τ)
    (hd : Module.finrank (ZMod 2) U.toSubmodule ≤
      Module.finrank (ZMod 2) ((fixed ρ).quotientImage U).toSubmodule) :
    ActionEquiv (U.toRepresentation.comp A.subtype) τ where
  groupEquiv := e.groupEquiv
  linearEquiv := (LinearEquiv.ofBijective (fixedImageProjection U)
    ⟨fixedImageProjection_injective_of_dimension U hd,
      fixedImageProjection_surjective U⟩).trans e.linearEquiv
  intertwines a v := e.intertwines a (fixedImageProjection U v)

theorem linearThree_dimension {A : Subgroup D} {U : Subrepresentation ρ}
    (hm : U.toSubmodule = moved ρ A)
    (e : ActionEquiv (((fixed ρ).quotientImage U).toRepresentation.comp A.subtype)
      (linearNatural BinaryField.two 3))
    (t : A) (hne : t ≠ 1) (ht : t * t = 1)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) ≤ 1) :
    Module.finrank (ZMod 2) U.toSubmodule ≤
      Module.finrank (ZMod 2) ((fixed ρ).quotientImage U).toSubmodule := by
  have hb := SmallNaturalMovedDimension.linearThree (ρ.comp A.subtype)
    e.groupEquiv t hne ht
  change U.toSubmodule = subspaceCommutator ρ ⊤ A at hm
  rw [← subspaceCommutator_top_eq_coinvariants, ← hm] at hb
  have he := e.linearEquiv.finrank_eq
  change Module.finrank (ZMod 2) ((fixed ρ).quotientImage U).toSubmodule =
    Module.finrank (ZMod 2) (Fin 3 → ZMod 2) at he
  rw [Module.finrank_fin_fun] at he
  change Module.finrank (ZMod 2) U.toSubmodule ≤
    3 * Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) at hb
  omega

theorem linearTwo_dimension {A : Subgroup D} {U : Subrepresentation ρ}
    (hm : U.toSubmodule = moved ρ A)
    (e : ActionEquiv (((fixed ρ).quotientImage U).toRepresentation.comp A.subtype)
      (linearNatural BinaryField.two 2))
    (t : A) (hne : t ≠ 1) (ht : t * t = 1)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) ≤ 1) :
    Module.finrank (ZMod 2) U.toSubmodule ≤
      Module.finrank (ZMod 2) ((fixed ρ).quotientImage U).toSubmodule := by
  let E := e.groupEquiv.trans ((BinaryLinear.OuterCyclic.slEquivLinear 2).trans
    BinaryLinear.SmallParabolicLevi.linearTwoEquivSymmetricThree)
  have hb := SmallNaturalMovedDimension.symmetricThree (ρ.comp A.subtype) E t hne ht
  change U.toSubmodule = subspaceCommutator ρ ⊤ A at hm
  rw [← subspaceCommutator_top_eq_coinvariants, ← hm] at hb
  have he := e.linearEquiv.finrank_eq
  change Module.finrank (ZMod 2) ((fixed ρ).quotientImage U).toSubmodule =
    Module.finrank (ZMod 2) (Fin 2 → ZMod 2) at he
  rw [Module.finrank_fin_fun] at he
  change Module.finrank (ZMod 2) U.toSubmodule ≤
    2 * Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) at hb
  omega

/-- Rank on the literal image in the fixed quotient cannot exceed ambient rank. -/
theorem fixedImage_displacement_le (U : Subrepresentation ρ) (t : D) :
    Module.finrank (ZMod 2) (LinearMap.range
      (((fixed ρ).quotientImage U).toRepresentation t - LinearMap.id)) ≤
    Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) := by
  have h₁ := fixedCodim_subrepresentation_le (fixed ρ).quotientRepresentation
    ((fixed ρ).quotientImage U) (zpowers t)
  have h₂ := fixedCodim_quotient_add_subrepresentation_le ρ (fixed ρ) (zpowers t)
  simp only [fixedCodim_zpowers_eq_displacement_rank] at h₁ h₂
  omega

theorem symmetricFive_dimension {A : Subgroup D} {U : Subrepresentation ρ}
    (hm : U.toSubmodule = moved ρ A)
    (e : ActionEquiv (((fixed ρ).quotientImage U).toRepresentation.comp A.subtype)
      (BinaryPermutation.naturalRepresentation (Fin 5)))
    (t : A) (hne : t ≠ 1)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) ≤ 1) :
    Module.finrank (ZMod 2) U.toSubmodule ≤
      Module.finrank (ZMod 2) ((fixed ρ).quotientImage U).toSubmodule := by
  let c : ActionEquiv (BinaryPermutation.coreRepresentation (Fin 5))
      (BinaryPermutation.naturalRepresentation (Fin 5)) :=
    ⟨MulEquiv.refl _, BinaryPermutation.coreEquivNatural (Fin 5) (by decide),
      BinaryPermutation.coreEquivNatural_equivariant (Fin 5) (by decide)⟩
  have hcore : Module.finrank (ZMod 2) (LinearMap.range
      (BinaryPermutation.coreRepresentation (Fin 5) (e.groupEquiv t) - LinearMap.id)) ≤ 1 := by
    rw [c.displacement_rank (e.groupEquiv t)]
    change Module.finrank (ZMod 2) (LinearMap.range
      (BinaryPermutation.naturalRepresentation (Fin 5) (e.groupEquiv t) - LinearMap.id)) ≤ 1
    rw [← e.displacement_rank t]
    exact (fixedImage_displacement_le U t).trans hr
  have hswap : (e.groupEquiv t).IsSwap := by
    rcases BinaryPermutation.FiveLowRank.low_rank (e.groupEquiv t) hcore with he | he
    · exact (hne (e.groupEquiv.injective (he.trans e.groupEquiv.map_one.symm))).elim
    · exact he
  have hb := SmallNaturalMovedDimension.symmetric (ρ.comp A.subtype) e.groupEquiv t hswap
  change U.toSubmodule = subspaceCommutator ρ ⊤ A at hm
  rw [← subspaceCommutator_top_eq_coinvariants, ← hm] at hb
  have he := e.linearEquiv.finrank_eq
  rw [BinaryPermutation.finrank_natural_odd (Fin 5) (by decide), Fintype.card_fin] at he
  change Module.finrank (ZMod 2) U.toSubmodule ≤
    4 * Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) at hb
  omega

/-- The three small quotient models allowed by G.6.4. -/
def SmallQuotientModel (A : Subgroup D) (U : Subrepresentation ρ) : Prop :=
  IsLinearNatural (((fixed ρ).quotientImage U).toRepresentation.comp A.subtype)
      BinaryField.two 2 ∨
  IsLinearNatural (((fixed ρ).quotientImage U).toRepresentation.comp A.subtype)
      BinaryField.two 3 ∨
  IsSymmetricNatural (((fixed ρ).quotientImage U).toRepresentation.comp A.subtype) 5

private noncomputable def binaryLinearModel {A : Subgroup D} {U : Subrepresentation ρ}
    {n : ℕ} (e : ActionEquiv (U.toRepresentation.comp A.subtype)
      (linearNatural BinaryField.two n)) :
    ActionEquiv (U.toRepresentation.comp A.subtype) (binaryLinearAction n) where
  groupEquiv := e.groupEquiv.trans (BinaryLinear.OuterCyclic.slEquivLinear n)
  linearEquiv := e.linearEquiv
  intertwines a v := e.intertwines a v

/-- The literal G.6 small-factor conclusion, with the fixed kernel proved zero. -/
theorem small_model_on_moved {A : Subgroup D} {U : Subrepresentation ρ}
    (hm : U.toSubmodule = moved ρ A) (he : SmallQuotientModel A U)
    (t : A) (hne : t ≠ 1) (ht : t * t = 1)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) ≤ 1) :
    Disjoint U.toSubmodule ρ.invariants ∧ SmallFactorModel ρ A (moved ρ A) := by
  simp only [SmallQuotientModel, IsLinearNatural, IsSymmetricNatural] at he
  rcases he with he | he | he
  · obtain ⟨e⟩ := he
    have hd := linearTwo_dimension hm e t hne ht hr
    refine ⟨disjoint_fixed_of_dimension U hd, ?_⟩
    rw [← hm]
    exact smallFactorModel_of_binaryLinearAction ρ A U 2 (Or.inl rfl)
      (binaryLinearModel (liftImageModel e hd))
  · obtain ⟨e⟩ := he
    have hd := linearThree_dimension hm e t hne ht hr
    refine ⟨disjoint_fixed_of_dimension U hd, ?_⟩
    rw [← hm]
    exact smallFactorModel_of_binaryLinearAction ρ A U 3 (Or.inr rfl)
      (binaryLinearModel (liftImageModel e hd))
  · obtain ⟨e⟩ := he
    have hd := symmetricFive_dimension hm e t hne hr
    refine ⟨disjoint_fixed_of_dimension U hd, ?_⟩
    rw [← hm]
    exact smallFactorModel_of_naturalFive ρ A U (liftImageModel e hd)

end CFSG.Quasithin.ChapterG.Section06.TwoFactorReconstruction
