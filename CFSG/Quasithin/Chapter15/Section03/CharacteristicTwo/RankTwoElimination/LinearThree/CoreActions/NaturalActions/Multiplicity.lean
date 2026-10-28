module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases.Alternatives
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.FixedKernel.DoubleCopy.CoverRigidity.ModelOffenders.Normalizers.Intertwiners
public import Theory.Representation.BinaryPlaneNormalizer

/-!
# Residual fixation on one or two binary natural modules

A map commuting with SL₃(2) acts on all three coordinate columns by one
multiplicity map. This follows from the scalar endomorphism ring of the
actual natural representation. The multiplicity maps form a representation.
For two copies a common nonzero fixed vector supplies a nonzero fixed column;
two-perfectness kills the action on that binary plane. One copy has trivial
invertible scalar action. No odd-order hypothesis on the residual is used.

Source: Aschbacher–Smith, proof of 15.3.23, final paragraph on printed p.1129,
using the natural layers in C.1.34(1),(2), printed p.136.
-/

@[expose] public section

open Representation
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.NaturalActions
abbrev Space := Fin 3 → ZMod 2
abbrev Actor := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
abbrev Copies (a : ℕ) := Fin a → Space
abbrev Coefficients (a : ℕ) := Fin a → ZMod 2

private def column {a : ℕ} (r : Fin 3) : Copies a →ₗ[ZMod 2] Coefficients a where
  toFun v i := v i r
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def inflate {a : ℕ} (r : Fin 3) : Coefficients a →ₗ[ZMod 2] Copies a where
  toFun v i := Pi.single r (v i)
  map_add' v w := by ext; simp [Pi.single_add]
  map_smul' c v := by
    funext i j
    by_cases h : j = r <;> simp [h]

private def multiplicityMap {a : ℕ} (f : Module.End (ZMod 2) (Copies a)) :=
  (column 0).comp (f.comp (inflate 0))

private lemma scalar_block {a : ℕ} (f : Module.End (ZMod 2) (Copies a))
    (hf : ∀ g v, f (NaturalCopies (ZMod 2) a g v) = NaturalCopies (ZMod 2) a g (f v))
    (i j : Fin a) : ∃ c : ZMod 2, ∀ v : Space, f (Pi.single j v) i = c • v := by
  let b : (specialLinearNatural (k := ZMod 2) 3).IntertwiningMap
      (specialLinearNatural (k := ZMod 2) 3) :=
    { toLinearMap := (LinearMap.proj i).comp (f.comp (LinearMap.single (ZMod 2) (fun _ : Fin a => Space) j))
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro v
        have he : NaturalCopies (ZMod 2) a g (Pi.single j v) =
            Pi.single j (specialLinearNatural 3 g v) := by
          funext k
          by_cases hk : k = j
          · subst k; simp [moduleCopies]
          · simp [moduleCopies, Pi.single_eq_of_ne hk]
        exact congrFun (hf g (Pi.single j v) |>.symm.trans (congrArg f he) |>.symm) i }
  obtain ⟨c, hc⟩ := ChapterC.BinaryMS.AbelianCore.DoubleCopy.CoverModels.ModelOffenders.base_end_scalar b
  refine ⟨c, fun v => ?_⟩
  have h := congrArg (fun t : (specialLinearNatural (k := ZMod 2) 3).IntertwiningMap (specialLinearNatural (k := ZMod 2) 3) => t v) hc
  exact h

/-- A commuting map acts on every coordinate column by the same multiplicity map. -/
private theorem commuting_columns {a : ℕ} (f : Module.End (ZMod 2) (Copies a))
    (hf : ∀ g v, f (NaturalCopies (ZMod 2) a g v) = NaturalCopies (ZMod 2) a g (f v))
    (v : Copies a) (r : Fin 3) : column r (f v) = multiplicityMap f (column r v) := by
  classical
  choose c hc using scalar_block f hf
  have formula (v : Copies a) (i : Fin a) : f v i = ∑ j : Fin a, c i j • v j := by
    have he : v = ∑ j : Fin a, Pi.single j (v j) := by funext i; simp [Finset.sum_apply]
    conv_lhs => rw [he, map_sum]
    simpa only [Finset.sum_apply] using Finset.sum_congr rfl (fun j _ => hc i j (v j))
  ext i
  change f v i r = f (inflate 0 (column r v)) i 0
  rw [formula, formula]
  simp [Finset.sum_apply, inflate, column]

/-- Restriction to the multiplicity space is a representation, not just a family of maps. -/
private def multiplicityRepresentation {K : Type*} [Group K] {a : ℕ}
    (ρ : Representation (ZMod 2) K (Copies a))
    (hρ : ∀ k g v, ρ k (NaturalCopies (ZMod 2) a g v) = NaturalCopies (ZMod 2) a g (ρ k v)) :
    Representation (ZMod 2) K (Coefficients a) where
  toFun k := multiplicityMap (ρ k)
  map_one' := by
    apply LinearMap.ext
    intro v
    funext i
    change (ρ 1 (inflate 0 v)) i 0 = v i
    rw [map_one]
    simp [inflate]
  map_mul' k l := by
    apply LinearMap.ext
    intro v
    funext i
    change (column 0 (ρ (k * l) (inflate 0 v))) i = _
    rw [map_mul, Module.End.mul_apply, commuting_columns (ρ k) (hρ k)]
    rfl

private lemma one_dimensional_trivial {K : Type*} [Group K]
    (ρ : Representation (ZMod 2) K (Coefficients 1)) (k : K) : ρ k = 1 := by
  have binary : ∀ v : Coefficients 1, v ≠ 0 → v = ![1] := by decide +kernel
  apply LinearMap.ext
  intro v
  by_cases hv : v = 0
  · simp [hv]
  have hne : ρ k v ≠ 0 := by
    intro h
    have hh := congrArg (ρ k⁻¹) h
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply, map_zero] at hh
    exact hv hh
  exact (binary _ hne).trans (binary _ hv).symm

/-- A two-perfect actor commuting with at most two natural copies and fixing a
nonzero vector fixes every vector. In the doubled case, the fixed column makes
its multiplicity action trivial on the binary plane. -/
theorem twoPerfect_copies_fixed {K : Type*} [Group K] {a : ℕ}
    (ha : a = 1 ∨ a = 2) (ρ : Representation (ZMod 2) K (Copies a))
    (hK : IsPPerfect 2 K)
    (hρ : ∀ k g v, ρ k (NaturalCopies (ZMod 2) a g v) = NaturalCopies (ZMod 2) a g (ρ k v))
    (w : Copies a) (hw : w ≠ 0) (hfix : ∀ k, ρ k w = w) : ∀ k, ρ k = 1 := by
  let τ := multiplicityRepresentation ρ hρ
  have he (k : K) : τ k = 1 := by
    rcases ha with rfl | rfl
    · exact one_dimensional_trivial τ k
    · obtain ⟨r, hr⟩ : ∃ r : Fin 3, column r w ≠ 0 := by
        by_contra! h
        apply hw
        ext i r
        exact congrFun (h r) i
      apply BinaryPlaneNormalizer.twoPerfect_plane_fixed τ hK (by simp [Coefficients])
        (column r w) hr ?_ k
      intro k
      change multiplicityMap (ρ k) (column r w) = column r w
      rw [← commuting_columns (ρ k) (hρ k), hfix]
  intro k
  apply LinearMap.ext
  intro v
  funext i r
  have h := commuting_columns (ρ k) (hρ k) v r
  change column r (ρ k v) = τ k (column r v) at h
  rw [he] at h
  exact congrFun h i
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.NaturalActions
