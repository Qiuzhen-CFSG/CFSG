module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Equality.B1Actors
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Involutions.Native

/-!
# Strict rank for symplectic tensor actors

The genuine common-root containment bounds an all-b₁ elementary actor by
2s. Native involution dimensions on the 16s-dimensional binary module
exclude that case and give rank at least 4s. At equality the actor and a
non-b₁ involution have identical fixed spaces, placing the actor in the
literal pointwise fixer. Its rank-s bound excludes equality.

Only the earlier-source Sylow fixed-space fixer estimate remains explicit;
`Equality.Source` supplies it from the proved involution geometry.
Source: Aschbacher–Smith, K.3.4.2, printed p.457 (PDF p.468).
-/

public section
open Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour SymplecticConjugatePair
open Theory.SpecificGroups.SymplecticFour.InvolutionTypes
namespace CFSG.Quasithin.ChapterK.Symplectic
variable {G V F : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G)
  [IsIrreducible (ρ.comp L.subtype)] [Field F]
  [Algebra (SchurField (ρ.comp L.subtype)) F]

/-- A small-ratio elementary actor has rank strictly greater than 4s.
The common-root bound excludes the all-b₁ case. A non-b₁ involution gives
rank at least 4s; equality would make the whole actor fix its 8s-dimensional
fixed space pointwise, contradicting the rank-s Sylow fixer bound. -/
theorem tensor_actor_rank_gt_four_mul {s : ℕ} (hs : 0 < s)
    (h : TensorIdentification (ρ.comp L.subtype) F s)
    (hfix : ∀ (T : Sylow 2 G) (j : G) (hjL : j ∈ L), j ∈ T → orderOf j = 2 →
      ¬ IsB1 (h.groupEquiv ⟨j, hjL⟩) →
      rank (subspaceKernel ρ (fixedSpace ρ (Subgroup.zpowers j)) T) ≤ s)
    {A : Subgroup G} (hA : IsElementaryTwo A) (hAL : A ≤ L)
    (hsmall : fixedCodim ρ A ≤ 2 * rank A) : 4 * s < rank A := by
  classical
  let : IsElementaryAbelian 2 A := hA.2
  have horder (j : G) (hj : j ∈ A) (hne : j ≠ 1) : orderOf j = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian j hj) hne
  have hle (j : G) (hj : j ∈ A) :
      fixedSpace ρ A ≤ fixedSpace ρ (Subgroup.zpowers j) := by
    intro v hv
    exact (mem_fixedSpace_zpowers_iff ρ j v).mpr (hv ⟨j, hj⟩)
  have hdim := fixedCodim_add_finrank ρ A
  rw [h.binary_finrank] at hdim
  obtain ⟨j, hj, hne, hnon⟩ : ∃ (j : G) (hj : j ∈ A),
      j ≠ 1 ∧ ¬ IsB1 (h.groupEquiv ⟨j, hAL hj⟩) := by
    by_contra! hall
    have hr := tensor_b1_actor_rank_le ρ L h hAL (by
      rintro x ⟨a, ha, rfl⟩ hne
      apply hall a.val ha
      intro he
      apply hne
      have he' : a = 1 := Subtype.ext he
      simp [he'])
    obtain ⟨j, hj⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA.1
    have hj1 : j.val ≠ 1 := fun he => hj (Subtype.ext he)
    have hd := h.component_involution_fixed_finrank_le ρ L j.val (hAL j.property)
      (horder j.val j.property hj1)
    have hm := Submodule.finrank_mono (hle j.val j.property)
    omega
  have ho := horder j hj hne
  have he : fixedSpace (ρ.comp L.subtype) (Subgroup.zpowers (⟨j, hAL hj⟩ : L)) =
      fixedSpace ρ (Subgroup.zpowers j) := by
    ext v
    simp only [mem_fixedSpace_zpowers_iff, MonoidHom.comp_apply, Subgroup.coe_subtype]
  have hdimj := h.involution_fixed_finrank (ρ.comp L.subtype) ⟨j, hAL hj⟩
    ((Subgroup.orderOf_coe (⟨j, hAL hj⟩ : L)).symm.trans ho)
  rw [he, if_neg hnon] at hdimj
  have hm := Submodule.finrank_mono (hle j hj)
  have hr : 4 * s ≤ rank A := by omega
  by_contra hn
  have hrank : rank A = 4 * s := by omega
  have hspaces : fixedSpace ρ A = fixedSpace ρ (Subgroup.zpowers j) := by
    apply Submodule.eq_of_le_of_finrank_eq (hle j hj)
    omega
  obtain ⟨T, hAT⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  have hker : A ≤ subspaceKernel ρ (fixedSpace ρ (Subgroup.zpowers j)) T := by
    intro a ha
    refine ⟨hAT ha, ?_⟩
    intro v hv
    rw [← hspaces] at hv
    exact hv ⟨a, ha⟩
  have hk := Nat.log_mono_right (b := 2) (Subgroup.card_le_of_le hker)
  change rank A ≤ rank (subspaceKernel ρ (fixedSpace ρ (Subgroup.zpowers j)) T) at hk
  have hf := hfix T j (hAL hj) (hAT hj) ho hnon
  omega
end CFSG.Quasithin.ChapterK.Symplectic
