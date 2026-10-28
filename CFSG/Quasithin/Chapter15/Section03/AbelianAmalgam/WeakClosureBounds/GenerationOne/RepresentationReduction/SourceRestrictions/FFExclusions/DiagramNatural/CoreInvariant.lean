module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.ModuleIdentifications
public import Theory.GroupTheory.SylowKernelCore
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# A fixed-space invariant for genuine diagram actions

For a binary representation, the dimension fixed by the intrinsic two-core
of a parabolic is invariant under intertwiners and inner conjugacy. If the
two parabolic classes have different dimensions and an automorphism permutes
them, an extending linear equivalence would fix both classes. Dimensions add
on direct sums, so two identical summands have the same obstruction.

This is a conditional linear-algebra reduction. The concrete model modules
must prove both the dimension distinction and the permutation of the actual
parabolic classes. Source application: Aschbacher--Smith, combined manuscript
(1 March 2004), B.4.2, B.5.1(1)(ii), and 15.3.65, printed pp.86, 99--100, 1152.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.DiagramNatural
open Representation Representation.BinaryOffender Subgroup
variable {G V W : Type*} [Group G]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]

/-- Binary dimension fixed by the intrinsic two-core, embedded in the actor. -/
def coreFixedRank (ρ : Representation (ZMod 2) G V) (P : Subgroup G) : ℕ :=
  Module.finrank (ZMod 2) (fixedSpace ρ (P.pCoreIn 2))

/-- An actual intertwiner preserves the two-core fixed-space dimension. -/
theorem coreFixedRank_map_of_intertwines (ρ : Representation (ZMod 2) G V)
    (γ : MulAut G) (e : V ≃ₗ[ZMod 2] V)
    (he : ∀ g v, e (ρ g v) = ρ (γ g) (e v)) (P : Subgroup G) :
    coreFixedRank ρ (P.map γ.toMonoidHom) = coreFixedRank ρ P := by
  unfold coreFixedRank
  rw [← map_pCoreIn_of_injective 2 P γ.toMonoidHom γ.injective,
    ← fixedSpace_map_equivariant ρ ρ γ.toMonoidHom e he]
  exact e.finrank_map_eq _

/-- Inner conjugacy preserves the same invariant. -/
theorem coreFixedRank_conjugate (ρ : Representation (ZMod 2) G V)
    (P : Subgroup G) (g : G) :
    coreFixedRank ρ (P.map (MulAut.conj g).toMonoidHom) = coreFixedRank ρ P := by
  unfold coreFixedRank
  rw [← map_pCoreIn_of_injective 2 P _ (MulAut.conj g).injective]
  exact (fixedSpaceConjEquiv ρ (P.pCoreIn 2) g).finrank_eq.symm

private def fixedProdEquiv (ρ : Representation (ZMod 2) G V)
    (τ : Representation (ZMod 2) G W) (A : Subgroup G) :
    fixedSpace (ρ.prod τ) A ≃ₗ[ZMod 2] (fixedSpace ρ A × fixedSpace τ A) where
  toFun v := (⟨v.val.1, fun a => congrArg Prod.fst (v.property a)⟩,
    ⟨v.val.2, fun a => congrArg Prod.snd (v.property a)⟩)
  invFun v := ⟨(v.1.val, v.2.val), fun a => Prod.ext (v.1.property a) (v.2.property a)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The invariant adds on the literal product representation. -/
theorem coreFixedRank_prod [FiniteDimensional (ZMod 2) V] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) G V) (τ : Representation (ZMod 2) G W)
    (P : Subgroup G) :
    coreFixedRank (ρ.prod τ) P = coreFixedRank ρ P + coreFixedRank τ P := by
  unfold coreFixedRank
  rw [(fixedProdEquiv ρ τ (P.pCoreIn 2)).finrank_eq, Module.finrank_prod]

/-- An intertwiner preserves the dimension fixed by any specified subgroup. -/
theorem fixedSpace_finrank_map_of_intertwines (ρ : Representation (ZMod 2) G V)
    (γ : MulAut G) (e : V ≃ₗ[ZMod 2] V)
    (he : ∀ g v, e (ρ g v) = ρ (γ g) (e v)) (R : Subgroup G) :
    Module.finrank (ZMod 2) (fixedSpace ρ (R.map γ.toMonoidHom)) =
      Module.finrank (ZMod 2) (fixedSpace ρ R) := by
  rw [← fixedSpace_map_equivariant ρ ρ γ.toMonoidHom e he]
  exact e.finrank_map_eq _

/-- A permuted pair with unequal fixed dimensions recovers the two normalizer
classes. This also applies when the subgroups have not been identified as cores. -/
theorem not_intertwines_of_fixedSpace_normalizers
    (ρ : Representation (ZMod 2) G V) (γ : MulAut G) (R S : Subgroup G)
    (hpair : (R.map γ.toMonoidHom = R ∧ S.map γ.toMonoidHom = S) ∨
      R.map γ.toMonoidHom = S)
    (hrank : Module.finrank (ZMod 2) (fixedSpace ρ R) ≠
      Module.finrank (ZMod 2) (fixedSpace ρ S))
    (hmoves : MovesParabolicClasses γ (normalizer (R : Set G))
      (normalizer (S : Set G))) :
    ¬ ∃ e : V ≃ₗ[ZMod 2] V, ∀ g v, e (ρ g v) = ρ (γ g) (e v) := by
  rintro ⟨e, he⟩
  rcases hpair with ⟨hR, hS⟩ | hR
  · apply hmoves
    constructor
    · refine ⟨1, ?_⟩
      rw [map_equiv_normalizer_eq, hR]
      have hconj : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by ext x; simp
      rw [hconj, Subgroup.map_id]
    · refine ⟨1, ?_⟩
      rw [map_equiv_normalizer_eq, hS]
      have hconj : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by ext x; simp
      rw [hconj, Subgroup.map_id]
  · exact hrank (by
      rw [← fixedSpace_finrank_map_of_intertwines ρ γ e he R, hR])

/-- Two identical summands preserve a strict distinction of fixed dimensions. -/
theorem not_intertwines_prod_self_of_fixedSpace_normalizers
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (γ : MulAut G) (R S : Subgroup G)
    (hpair : (R.map γ.toMonoidHom = R ∧ S.map γ.toMonoidHom = S) ∨
      R.map γ.toMonoidHom = S)
    (hrank : Module.finrank (ZMod 2) (fixedSpace ρ R) ≠
      Module.finrank (ZMod 2) (fixedSpace ρ S))
    (hmoves : MovesParabolicClasses γ (normalizer (R : Set G))
      (normalizer (S : Set G))) :
    ¬ ∃ e : (V × V) ≃ₗ[ZMod 2] (V × V),
      ∀ g v, e (ρ.prod ρ g v) = ρ.prod ρ (γ g) (e v) := by
  apply not_intertwines_of_fixedSpace_normalizers (ρ.prod ρ) γ R S hpair _ hmoves
  rw [(fixedProdEquiv ρ ρ R).finrank_eq, (fixedProdEquiv ρ ρ S).finrank_eq,
    Module.finrank_prod, Module.finrank_prod]
  omega

/-- Distinct core fixed dimensions obstruct extension across a moving diagram action. -/
theorem not_intertwines_of_coreFixedRank
    (ρ : Representation (ZMod 2) G V) (γ : MulAut G) (P Q : Subgroup G)
    (hclasses : ∀ R : Subgroup G, R = P ∨ R = Q →
      ∃ S : Subgroup G, (S = P ∨ S = Q) ∧
        ∃ g : G, R.map γ.toMonoidHom = S.map (MulAut.conj g).toMonoidHom)
    (hrank : coreFixedRank ρ P ≠ coreFixedRank ρ Q)
    (hmoves : MovesParabolicClasses γ P Q) :
    ¬ ∃ e : V ≃ₗ[ZMod 2] V, ∀ g v, e (ρ g v) = ρ (γ g) (e v) := by
  rintro ⟨e, he⟩
  have hfix (R S : Subgroup G) (g : G)
      (h : R.map γ.toMonoidHom = S.map (MulAut.conj g).toMonoidHom) :
      coreFixedRank ρ R = coreFixedRank ρ S := by
    rw [← coreFixedRank_map_of_intertwines ρ γ e he R, h, coreFixedRank_conjugate]
  apply hmoves
  constructor
  · obtain ⟨S, hS, g, hg⟩ := hclasses P (Or.inl rfl)
    rcases hS with rfl | rfl
    · exact ⟨g, hg⟩
    · exact (hrank (hfix _ _ g hg)).elim
  · obtain ⟨S, hS, g, hg⟩ := hclasses Q (Or.inr rfl)
    rcases hS with rfl | rfl
    · exact (hrank (hfix _ _ g hg).symm).elim
    · exact ⟨g, hg⟩

/-- The same obstruction applies to two identical natural summands. -/
theorem not_intertwines_prod_self_of_coreFixedRank [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (γ : MulAut G) (P Q : Subgroup G)
    (hclasses : ∀ R : Subgroup G, R = P ∨ R = Q →
      ∃ S : Subgroup G, (S = P ∨ S = Q) ∧
        ∃ g : G, R.map γ.toMonoidHom = S.map (MulAut.conj g).toMonoidHom)
    (hrank : coreFixedRank ρ P ≠ coreFixedRank ρ Q)
    (hmoves : MovesParabolicClasses γ P Q) :
    ¬ ∃ e : (V × V) ≃ₗ[ZMod 2] (V × V),
      ∀ g v, e (ρ.prod ρ g v) = ρ.prod ρ (γ g) (e v) := by
  apply not_intertwines_of_coreFixedRank (ρ.prod ρ) γ P Q hclasses _ hmoves
  rw [coreFixedRank_prod, coreFixedRank_prod]
  omega

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.DiagramNatural
