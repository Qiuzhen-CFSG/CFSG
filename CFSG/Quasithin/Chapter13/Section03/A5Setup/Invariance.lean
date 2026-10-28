module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.ChosenModules
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Fundamental
public import Theory.Representation.BinaryOffender.Homogeneous.NaturalFive

/-!
# T-invariance of the original chosen A₅ module

The literal inclusion of the chosen Irr⁺ subspace into R₂(LT) transports
its given natural conjugation model to the exact representation used by
A.1.40. The natural-five homogeneity theorem makes that same subspace
T-invariant. Mapping its actual inclusion back into G gives T-normalization
of the original V, without a replacement module or a structural-12.2.2 input.

Source: Aschbacher–Smith 13.3.2(3), printed p.885, and its earlier chosen
module in 12.2.2, pp.794–795. The marked natural-module conclusion remains
an earlier input; this theorem proves its source invariance consequence.
-/

public section
open Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous

namespace CFSG.Quasithin.Chapter13.Section03.A5Setup
open CFSG.Quasithin Subgroup Theory.GroupTheory BinaryPermutation
open scoped IsMulCommutative
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G}

theorem chosen_natural_module_invariant
    (D : Chapter12.Section02.ChosenModule T L V)
    (hmodel : Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module) :
    (T : Subgroup G) ≤ normalizer (V : Set G) := by
  obtain ⟨e, f, hf⟩ := hmodel
  let H := L ⊔ (T : Subgroup G)
  let X := L.subgroupOf H
  let eX : X ≃* L := subgroupOfEquivOfLe le_sup_left
  let qX := QuotientGroup.congr (pCore 2 X) (pCore 2 L) eX (pCore_map_iso 2 eX)
  let fI := D.spaceEquiv.trans f
  let A : D.space ≃+ natural (Fin 5) := {
    toFun v := (fI (Multiplicative.ofAdd v)).toAdd
    invFun w := (fI.symm (Multiplicative.ofAdd w)).toAdd
    left_inv v := congrArg Multiplicative.toAdd (fI.symm_apply_apply (Multiplicative.ofAdd v))
    right_inv w := congrArg Multiplicative.toAdd (fI.apply_symm_apply (Multiplicative.ofAdd w))
    map_add' v w := congrArg Multiplicative.toAdd
      (fI.map_mul (Multiplicative.ofAdd v) (Multiplicative.ofAdd w)) }
  let F : D.space ≃ₗ[ZMod 2] natural (Fin 5) := A.toLinearEquiv (ZMod.map_smul A)
  let ρ := Chapter12.Section02.reducedRepresentation H
  have hF (x : X) (v : D.space) :
      F ((invariantSubspace ρ X D.space D.irrPlus.invariant).toRepresentation x v) =
        naturalRepresentation (Fin 5)
          ((qX.trans e) (QuotientGroup.mk' (pCore 2 X) x)).val (F v) := by
    change f (D.spaceEquiv (Multiplicative.ofAdd _)) =
      Multiplicative.ofAdd (Chapter6.Source.a5Module
        (e (QuotientGroup.mk' (pCore 2 L) (eX x)))
        (f (D.spaceEquiv (Multiplicative.ofAdd v))).toAdd)
    apply f.symm.injective
    rw [f.symm_apply_apply]
    apply Subtype.ext
    have hh := (hf (eX x) (D.spaceEquiv (Multiplicative.ofAdd v))).symm
    have hact := D.spaceEquiv_apply
      ((invariantSubspace ρ X D.space D.irrPlus.invariant).toRepresentation x v)
    rw [D.spaceEquiv_apply] at hh
    exact hact.trans hh
  have hstable := NaturalFive.homogeneous_natural_a5_invariant ρ D.irrPlus (qX.trans e) F hF
  apply le_normalizer_iff.mpr
  intro t ht v hv
  rw [← D.image_eq] at hv ⊢
  obtain ⟨w, ⟨a, ha, rfl⟩, rfl⟩ := hv
  let tH : H := ⟨t, (le_sup_right : (T : Subgroup G) ≤ H) ht⟩
  have hh := (hstable (show tH ∈ (T : Subgroup G).subgroupOf H from ht)
    (Additive.ofMul a)).mpr ha
  exact ⟨_, ⟨Chapter12.Section02.reducedConjugation H tH a, hh, rfl⟩, rfl⟩

end CFSG.Quasithin.Chapter13.Section03.A5Setup
