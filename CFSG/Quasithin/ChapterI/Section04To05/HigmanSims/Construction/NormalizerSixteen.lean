module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.SixteenSymplecticNormalizer
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder

/-!
# The original sixteen and its full symplectic normalizer

The original HS local hypotheses construct the pure elementary sixteen.
Its full centralizer is itself, and its point-core hyperplanes give the
alternating form. The actual central-four elements generate the full
symplectic action. Thus the literal normalizer quotient has order 720,
and the full original normalizer has order 11520.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix
open scoped IsMulCommutative
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- The full original normalizer of a pure sixteen with point-core
hyperplanes has order 11520. -/
theorem TypeAt.sixteen_normalizer_card (h : TypeAt z V)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16)
    (hCA : centralizer (A : Set G) = A)
    (hpure : ∀ x ∈ A, x ≠ 1 → IsConj x z)
    (hpoints : ∀ x ∈ A, x ≠ 1 →
      Nat.card (A ⊓ (involutionCentralizer x).pCoreIn 2 : Subgroup G) = 8) :
    Nat.card (normalizer (A : Set G)) = 11520 := by
  obtain ⟨_, _, _, _, _, φ, _⟩ :=
    h.sixteen_symplectic_normalizer A hA hCA hpure hpoints
  have hq : Nat.card (normalizer (A : Set G) ⧸
      A.subgroupOf (normalizer (A : Set G))) = 720 := by
    rw [Nat.card_congr φ.toEquiv]
    change Nat.card (Theory.SpecificGroups.SymplecticFour.Sp (ZMod 2)) = 720
    rw [Theory.SpecificGroups.SymplecticFour.card_sp]
    norm_num
  have hc : Nat.card (A.subgroupOf (normalizer (A : Set G))) = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe A.le_normalizer).toEquiv).trans hA
  rw [card_eq_card_quotient_mul_card_subgroup
    (A.subgroupOf (normalizer (A : Set G))), hq, hc]

/-- Original HS local data supply a pure self-centralizing sixteen,
the full normalizer order, and the literal symplectic quotient with its
natural action and original point-core kernels. -/
theorem TypeAt.exists_sixteen_symplectic_normalizer (h : TypeAt z V) :
    ∃ (A : Subgroup G) (hAe : IsElementaryAbelian 2 A), letI := hAe
      Nat.card A = 16 ∧ centralizer (A : Set G) = A ∧
      (∀ x ∈ A, x ≠ 1 → IsConj x z) ∧
      (∀ x ∈ A, x ≠ 1 →
        Nat.card (A ⊓ (involutionCentralizer x).pCoreIn 2 : Subgroup G) = 8) ∧
      Nat.card (normalizer (A : Set G)) = 11520 ∧
      ∃ B : LinearMap.BilinForm (ZMod 2) (Additive A), B.IsAlt ∧ B.Nondegenerate ∧
        (∀ (x : A) (_hx : x ≠ 1) (y : A),
          B (Additive.ofMul x) (Additive.ofMul y) = 0 ↔
            (y : G) ∈ (involutionCentralizer (x : G)).pCoreIn 2) ∧
        ∃ e : B.IsometryEquiv (Matrix.PSp4Three.form (n := 2) (F := ZMod 2)),
          ∃ φ : (normalizer (A : Set G) ⧸ A.subgroupOf (normalizer (A : Set G))) ≃*
              Matrix.PSp4Three.Sp 2 (ZMod 2),
            ∀ (g : normalizer (A : Set G)) (x : A),
              (φ (QuotientGroup.mk g)).val *ᵥ (e (Additive.ofMul x)) =
                e (Additive.ofMul (A.normalizerMonoidHom g x)) := by
  obtain ⟨A, hAe, hA, hCA, hpure, hpoints, _⟩ := h.exists_sixteen_point_core_form
  let := hAe
  exact ⟨A, hAe, hA, hCA, hpure, hpoints,
    h.sixteen_normalizer_card A hA hCA hpure hpoints,
    h.sixteen_symplectic_normalizer A hA hCA hpure hpoints⟩

end CFSG.Quasithin.HigmanSims
