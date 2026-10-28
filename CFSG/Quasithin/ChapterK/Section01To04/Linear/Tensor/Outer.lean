module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Tensor.Marked
public import CFSG.Quasithin.ChapterH.Section01To04.HermitianTensor.ImageOuter

/-!
# Excluding outer actors on the Hermitian tensor

For an elementary actor containing an outer involution i, its inner
intersection has index at most two and the whole actor has rank at most
2n+1. If that intersection is nontrivial, faithfulness on [V,i] makes
C_V(i) ∩ C_V(g) a proper F-subspace of the six-dimensional C_V(i).
The resulting binary codimension at least 4n excludes ratio at most 5/4.
This sufficient bound avoids the stronger printed estimate 5n.

For quadratic actors the inner intersection fixes [V,i] pointwise, so
faithfulness makes it trivial. Rank at most one then contradicts the
outer involution's codimension 3n at ratio at most two. Both conclusions
use the literal image, relative index and faithful source overgroup action.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), K.3.2.4,
printed pp.455–456/PDF pp.466–467, using H.4.4(6), printed p.381.
-/

public section
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open Representation.BinaryOffender
open Theory.GroupTheory
open scoped ENNReal
noncomputable section
namespace CFSG.Quasithin.ChapterK.Linear.Tensor
namespace Outer
variable (n : ℕ) [NeZero n]
variable (M : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) (hM : SourceOvergroup n M)

include hM in
private theorem elementary_index_le_two (A : Subgroup M) (hA : IsElementaryTwo A) :
    (innerActor n M).relIndex A ≤ 2 := by
  let _ : IsElementaryAbelian 2 A := hA.2
  let _ : IsElementaryAbelian 2 (A.map M.subtype) := IsElementaryAbelian.map_subtype
  change ((binaryImage n).comap M.subtype).relIndex A ≤ 2
  rw [Subgroup.relIndex_comap]
  exact OuterRank.Coefficients.elementary_relIndex_le_two n (normalizerCoverage n)
    (A.map M.subtype) inferInstance
    ((Subgroup.map_subtype_le A).trans (sourceOvergroup_le_normalizer n M hM))

include hM in
private theorem rank_le_one_of_inf_eq_bot (A : Subgroup M) (hA : IsElementaryTwo A)
    (hbot : A ⊓ innerActor n M = ⊥) : rank A ≤ 1 := by
  have hi := elementary_index_le_two n M hM A hA
  rw [← Subgroup.inf_relIndex_left, hbot, Subgroup.relIndex_bot_left] at hi
  have hh := Nat.log_mono_right (b := 2) hi
  simpa only [rank, show Nat.log 2 2 = 1 by decide] using hh

private theorem rank_le_of_primeRank {G : Type*} [Group G] [Finite G]
    (A : Subgroup G) [IsElementaryAbelian 2 A] {r : ℕ} (hr : primeRank 2 A ≤ r) :
    rank A ≤ r := by
  have ht : IsElementaryAbelian 2 (⊤ : Subgroup A) := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x =>
      Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 A) x.val)) }
  have hc := (primeRank_le_iff_elementary_card_le A).mp hr ⊤ ht
  rw [Nat.card_congr Subgroup.topEquiv.toEquiv] at hc
  have hh := Nat.log_mono_right (b := 2) hc
  simpa only [rank, Nat.log_pow (by decide : 1 < 2)] using hh

include hM in
private theorem outer_rank_le (A : Subgroup M) (hA : IsElementaryTwo A)
    (i : M) (hiA : i ∈ A) (hi2 : orderOf i = 2) (hiL : i ∉ innerActor n M) :
    rank A ≤ 2 * n + 1 := by
  let _ : IsElementaryAbelian 2 A := hA.2
  let B := A.map M.subtype
  let _ : IsElementaryAbelian 2 B := IsElementaryAbelian.map_subtype
  have hBN : B ≤ binaryNormalizer n :=
    (Subgroup.map_subtype_le A).trans (sourceOvergroup_le_normalizer n M hM)
  obtain ⟨c,hc,hci,_,_⟩ :=
    ChapterH.Section01To04.HermitianTensor.ImageOuter.source_outer_conjugacy n M hM i hi2 hiL
  have hr := OuterRank.elementary_outer_twoRank_le n ⟨FieldSections.centralizerEquiv n⟩ B
    (OuterRank.Coefficients.elementary_relIndex_le_two n (normalizerCoverage n) B
      inferInstance hBN) i.val ⟨i,hiA,rfl⟩ c hc hci
  apply rank_le_of_primeRank A
  rw [primeRank_equiv 2 (A.equivMapOfInjective M.subtype M.subtype_injective)]
  exact hr

include hM in
private theorem three_mul_le_codim (A : Subgroup M)
    (i : M) (hiA : i ∈ A) (hi2 : orderOf i = 2) (hiL : i ∉ innerActor n M) :
    3 * n ≤ fixedCodim (overgroupAction n M) A := by
  have hle : fixedSpace (overgroupAction n M) A ≤
      LinearMap.ker (i.val.toLinearMap - LinearMap.id) := by
    intro X hX
    change i.val X - X = 0
    exact sub_eq_zero.mpr (hX ⟨i,hiA⟩)
  have hd := Submodule.finrank_mono hle
  rw [ChapterH.Section01To04.HermitianTensor.ImageOuter.source_outer_fixed_dimension
    n M hM i hi2 hiL] at hd
  have hsum := fixedCodim_add_finrank (overgroupAction n M) A
  rw [finrank_binary] at hsum
  omega

private theorem finrank_binary_restrict (W : Submodule (F n) (Space n)) :
    Module.finrank (ZMod 2) (W.restrictScalars (ZMod 2)) =
      n * Module.finrank (F n) W := by
  have hF := Module.natCard_eq_pow_finrank (K := F n) (V := W)
  rw [card_F, ← pow_mul] at hF
  have h2 := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := W.restrictScalars (ZMod 2))
  have hc : Nat.card (ZMod 2) = 2 := by simp
  have hcard : Nat.card (W.restrictScalars (ZMod 2)) = Nat.card W := rfl
  rw [hc, hcard, hF] at h2
  exact ((pow_right_inj₀ (by decide : 0 < (2 : ℕ)) (by decide : (2 : ℕ) ≠ 1)).mp h2).symm

private theorem inner_mem_centralizer (A : Subgroup M) (hA : IsElementaryTwo A)
    (i g : M) (hiA : i ∈ A) (hgA : g ∈ A) (hgL : g ∈ innerActor n M)
    (j : Space n ≃ₗ[F n] Space n) (hj : binaryEquiv n j = i.val) :
    g.val ∈ OuterInvolutions.centralizer n j := by
  let _ : IsElementaryAbelian 2 A := hA.2
  refine ⟨hgL, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  rw [hj]
  exact congrArg (fun a : A => a.val.val)
    ((IsMulCommutative.is_comm (M := A)).comm ⟨g,hgA⟩ ⟨i,hiA⟩)

include hM in
private theorem four_mul_le_codim (A : Subgroup M) (hA : IsElementaryTwo A)
    (i : M) (hiA : i ∈ A) (hi2 : orderOf i = 2) (hiL : i ∉ innerActor n M)
    (g : M) (hgA : g ∈ A) (hgL : g ∈ innerActor n M) (hg1 : g ≠ 1) :
    4 * n ≤ fixedCodim (overgroupAction n M) A := by
  obtain ⟨j,hj,hmf,hfd,_,_,_,hfaith,_,_⟩ :=
    ChapterH.Section01To04.HermitianTensor.ImageOuter.source_outer_sections n M hM i hi2 hiL
  let gC : OuterInvolutions.centralizer n j :=
    ⟨g.val, inner_mem_centralizer n M A hA i g hiA hgA hgL j hj⟩
  let W := OuterInvolutions.fixed n j ⊓
    LinearMap.ker (OuterInvolutions.action n j gC - LinearMap.id)
  have hproper : W < OuterInvolutions.fixed n j := by
    apply lt_of_le_of_ne inf_le_left
    intro he
    have hfix (X : OuterInvolutions.moved n j) : g.val X.val = X.val := by
      have hX : X.val ∈ W := by
        rw [show W = OuterInvolutions.fixed n j from he]
        exact hmf X.property
      have hk := hX.2
      change OuterInvolutions.action n j gC X.val - X.val = 0 at hk
      rw [OuterInvolutions.action_apply] at hk
      exact sub_eq_zero.mp hk
    have hgC1 : gC = 1 := hfaith (by
      rw [map_one]
      apply LinearMap.ext
      intro X
      apply Subtype.ext
      change (OuterInvolutions.movedAction n j gC X).val = X.val
      rw [OuterInvolutions.movedAction_apply]
      exact hfix X)
    have hv : g.val = 1 :=
      congrArg (fun z : OuterInvolutions.centralizer n j => z.val) hgC1
    exact hg1 (Subtype.ext hv)
  have hdim := Submodule.finrank_lt_finrank_of_lt hproper
  rw [hfd] at hdim
  have hW : Module.finrank (F n) W ≤ 5 := by omega
  have hle : fixedSpace (overgroupAction n M) A ≤ W.restrictScalars (ZMod 2) := by
    intro X hX
    change X ∈ W
    constructor
    · apply (OuterInvolutions.mem_fixed n j X).mpr
      change binaryEquiv n j X = X
      rw [hj]
      exact hX ⟨i,hiA⟩
    · change OuterInvolutions.action n j gC X - X = 0
      rw [OuterInvolutions.action_apply]
      exact sub_eq_zero.mpr (hX ⟨g,hgA⟩)
  have hb := Submodule.finrank_mono hle
  rw [finrank_binary_restrict] at hb
  have hwb := Nat.mul_le_mul_left n hW
  have hsum := fixedCodim_add_finrank (overgroupAction n M) A
  rw [finrank_binary] at hsum
  omega

include hM in
private theorem quadratic_inf_eq_bot (A : Subgroup M) (hA : IsElementaryTwo A)
    (hq : IsQuadratic (overgroupAction n M) A)
    (i : M) (hiA : i ∈ A) (hi2 : orderOf i = 2) (hiL : i ∉ innerActor n M) :
    A ⊓ innerActor n M = ⊥ := by
  obtain ⟨j,hj,_,_,_,_,_,hfaith,_,_⟩ :=
    ChapterH.Section01To04.HermitianTensor.ImageOuter.source_outer_sections n M hM i hi2 hiL
  apply bot_unique
  intro g hg
  apply Subgroup.mem_bot.mpr
  let gC : OuterInvolutions.centralizer n j :=
    ⟨g.val, inner_mem_centralizer n M A hA i g hiA hg.1 hg.2 j hj⟩
  have hgC1 : gC = 1 := hfaith (by
    rw [map_one]
    apply LinearMap.ext
    intro X
    apply Subtype.ext
    change (OuterInvolutions.movedAction n j gC X).val = X.val
    rw [OuterInvolutions.movedAction_apply]
    obtain ⟨Y,hY⟩ := X.property
    change j Y - Y = X.val at hY
    rw [← hY]
    change g.val (binaryEquiv n j Y - Y) = binaryEquiv n j Y - Y
    rw [hj]
    exact hq g hg.1 i hiA Y)
  have hv : g.val = 1 :=
    congrArg (fun z : OuterInvolutions.centralizer n j => z.val) hgC1
  exact Subtype.ext hv

end Outer

variable (n : ℕ) [NeZero n]
variable (M : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) (hM : SourceOvergroup n M)

include hM in
/-- An elementary actor of ratio at most 5/4 lies in the literal inner image. -/
theorem small_actor_le_inner (A : Subgroup M) (hA : IsElementaryTwo A)
    (hr : actionRatio (overgroupAction n M) A ≤ 5 / 4) : A ≤ innerActor n M := by
  by_contra hAI
  obtain ⟨i,hiA,hiL⟩ := SetLike.not_le_iff_exists.mp hAI
  let _ : IsElementaryAbelian 2 A := hA.2
  have hi2 : orderOf i = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian i hiA)
    (fun h => hiL (h ▸ (innerActor n M).one_mem))
  have hn := Nat.pos_of_ne_zero (NeZero.ne n)
  have hratio : 4 * fixedCodim (overgroupAction n M) A ≤ 5 * rank A := by
    have hrank : (rank A : ℝ≥0∞) ≠ 0 := by exact_mod_cast hA.rank_pos.ne'
    rw [actionRatio, ENNReal.div_le_iff hrank (by simp)] at hr
    have he : (5 / 4 : ℝ≥0∞) * rank A = (5 * rank A) / 4 := by
      simp only [div_eq_mul_inv]
      ac_rfl
    rw [he, ENNReal.le_div_iff_mul_le (Or.inl (by norm_num))
      (Or.inl (by norm_num))] at hr
    norm_cast at hr
    omega
  by_cases hbot : A ⊓ innerActor n M = ⊥
  · have hb := Outer.rank_le_one_of_inf_eq_bot n M hM A hA hbot
    have hd := Outer.three_mul_le_codim n M hM A i hiA hi2 hiL
    omega
  · obtain ⟨g,hg,hg1⟩ := (A ⊓ innerActor n M).bot_or_exists_ne_one.resolve_left hbot
    have hd := Outer.four_mul_le_codim n M hM A hA i hiA hi2 hiL g hg.1 hg.2 hg1
    have hb := Outer.outer_rank_le n M hM A hA i hiA hi2 hiL
    omega

include hM in
/-- A quadratic elementary actor of ratio at most two lies in the literal inner image. -/
theorem quadratic_actor_le_inner (A : Subgroup M) (hA : IsElementaryTwo A)
    (hq : IsQuadratic (overgroupAction n M) A)
    (hr : actionRatio (overgroupAction n M) A ≤ 2) : A ≤ innerActor n M := by
  by_contra hAI
  obtain ⟨i,hiA,hiL⟩ := SetLike.not_le_iff_exists.mp hAI
  let _ : IsElementaryAbelian 2 A := hA.2
  have hi2 : orderOf i = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian i hiA)
    (fun h => hiL (h ▸ (innerActor n M).one_mem))
  have hbot := Outer.quadratic_inf_eq_bot n M hM A hA hq i hiA hi2 hiL
  have hb := Outer.rank_le_one_of_inf_eq_bot n M hM A hA hbot
  have hd := Outer.three_mul_le_codim n M hM A i hiA hi2 hiL
  have hc := (actionRatio_le_nat_iff (overgroupAction n M) hA 2).mp hr
  have hn := Nat.pos_of_ne_zero (NeZero.ne n)
  omega

end CFSG.Quasithin.ChapterK.Linear.Tensor
