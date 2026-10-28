module

public import Theory.Representation.OrthogonalFourPlusMatrix.RankTwoFactorSwap
public import Theory.Representation.OrthogonalFourPlusMatrix.NearOffenderSwap
public import Theory.Representation.OrthogonalFourPlusMatrix.InvolutionDisplacement
public import Theory.Representation.BinaryOffender.SmallRank

/-!
# Small common-center actors on the determinant module

Every low-displacement involution exchanges the two simple factors. If all
members have displacement at most three, the factor-permutation map is
injective, so an elementary actor has order at most two.

For a quadratic rank-three actor, an actual inner involution has fixed space
equal to its displacement space. Quadraticity identifies this with the whole
actor's fixed space. On an invariant subspace with a common displacement line,
the image therefore has rank at most one. If that subspace has codimension at
most three, its pointwise kernel also has rank at most one, a contradiction.

Source: Aschbacher–Smith, proof of 14.7.32, printed p.1057. The chapter
application supplies the literal reciprocal subspace of the full U/V₁.
-/

public noncomputable section
open Module Subgroup Representation Representation.BinaryOffender
open Representation.BinaryOffender.NaturalTensor
namespace ClassicalOrthogonal.FourPlusMatrix.Binary
open Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms
local instance : Finite (Module.End (ZMod 2) V) :=
  Finite.of_injective DFunLike.coe DFunLike.coe_injective

local instance : Finite (V ≃ₗ[ZMod 2] V) :=
  Finite.of_injective DFunLike.coe DFunLike.coe_injective

private theorem preserves_left_of_wreath_right_eq_one (t : linearNormalizer action)
    (hr : (wreathEquiv.symm (alternatingConjugation t)).right = 1) :
    LinearMap.GeneralLinearGroup.toLinearEquiv t.val ∈
      normalizer (InvolutionResidual.leftFactor : Set (V ≃ₗ[ZMod 2] V)) := by
  let w := wreathEquiv.symm (alternatingConjugation t)
  have hw : wreathMap w = alternatingConjugation t := by
    change wreathHom w = _
    rw [←wreathEquiv_apply]
    exact wreathEquiv.apply_symm_apply _
  have hf (g : Matrix.SpecialLinearGroup (Fin 2) F) :
      (normalizerConjugation t (g,1)).2 = 1 := by
    have hh := MulEquiv.congr_fun hw (alternatingPairEquiv (g,1))
    simp only [alternatingConjugation, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at hh
    rw [wreathMap_apply,if_pos hr] at hh
    have hp : alternatingPairEquiv (g,1) =
        (Representation.SL2FourNatural.alternatingFiveEquiv g,1) :=
      Prod.ext rfl Representation.SL2FourNatural.alternatingFiveEquiv.map_one
    rw [hp] at hh
    have hzero := (congrArg Prod.snd hh).symm
    simp only [map_one] at hzero
    change Representation.SL2FourNatural.alternatingFiveEquiv
      (normalizerConjugation t (g,1)).2 = 1 at hzero
    exact Representation.SL2FourNatural.alternatingFiveEquiv.injective
      (hzero.trans Representation.SL2FourNatural.alternatingFiveEquiv.map_one.symm)
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv t.val
  have hconj (g : G) : e * linearAction g * e⁻¹ = linearAction (normalizerConjugation t g) := by
    apply LinearEquiv.ext
    intro v
    have hh := normalizerConjugation_action t g (e.symm v)
    change action (normalizerConjugation t g) (e (e.symm v)) = e (action g (e.symm v)) at hh
    rw [e.apply_symm_apply] at hh
    simp only [LinearEquiv.mul_apply,LinearEquiv.coe_inv,linearAction_apply]
    exact hh.symm
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨_,⟨g,rfl⟩,rfl⟩
    refine ⟨(normalizerConjugation t (g,1)).1,?_⟩
    change linearAction ((normalizerConjugation t (g,1)).1,1) =
      e * linearAction (g,1) * e⁻¹
    rw [hconj]
    exact congrArg linearAction (Prod.ext rfl (hf g).symm)
  · rw [card_map_of_injective (MulAut.conj e).injective]

/-- If every actor moves at most three binary dimensions, the elementary
group has order at most two: every nonidentity member swaps the two factors. -/
theorem rank_le_one_of_all_displacements_le_three
    (A : Subgroup (linearNormalizer action)) (hA : IsElementaryTwo A)
    (hsmall : ∀ t ∈ A, operatorFixedCodim t.val.val ≤ 3) : rank A ≤ 1 := by
  let := hA.2
  let f : A →* Theory.GroupTheory.WreathTwoElementaryRank.C2 :=
    RegularWreathProduct.rightHom.comp
      (wreathEquiv.symm.toMonoidHom.comp (alternatingConjugation.comp A.subtype))
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_one f).mpr
    intro t ht
    by_contra hne
    have hn : (t : linearNormalizer action) ≠ 1 := fun hh => hne (Subtype.ext hh)
    let e := LinearMap.GeneralLinearGroup.toLinearEquiv t.val.val
    have he : e ≠ 1 := by
      intro hh
      exact hn (Subtype.ext (Units.ext (congrArg LinearEquiv.toLinearMap hh)))
    have hr := rank_le_two_of_rank_le_three e (normalizer_linearEquiv_mem t.val)
      (hsmall t t.property)
    obtain ⟨_,_,_,hrank⟩ := low_rank_nonidentity e (normalizer_linearEquiv_mem t.val) hr he
    have ht2 : e ^ 2 = 1 := by
      have hh := elemPow_eq_one_of_isElementaryAbelian (p := 2) t.val t.property
      exact congrArg (fun x : linearNormalizer action =>
        LinearMap.GeneralLinearGroup.toLinearEquiv x.val) hh
    exact rank_two_involution_not_normalize_leftFactor e (normalizer_linearEquiv_mem t.val)
      ht2 hrank (preserves_left_of_wreath_right_eq_one t ht)
  have hc : Nat.card A ≤ 2 := by
    simpa [Nat.card_eq_fintype_card] using Nat.card_le_card_of_injective f hf
  have hh := Nat.log_mono_right (b := 2) hc
  exact hh

/-- A quadratic rank-three actor cannot move an invariant subspace of
codimension at most three into one binary line. -/
theorem rank_ne_three_of_common_line
    (A : Subgroup (linearNormalizer action)) (hA : IsElementaryTwo A)
    (hq : IsQuadratic (normalizerRepresentation action) A)
    (D Z : Submodule (ZMod 2) V)
    (hD : A ≤ subspaceStabilizer (normalizerRepresentation action) D)
    (hcod : finrank (ZMod 2) (V ⧸ D) ≤ 3)
    (hZ : finrank (ZMod 2) Z ≤ 1)
    (hd : ∀ a ∈ A, ∀ v ∈ D, normalizerRepresentation action a v - v ∈ Z) :
    rank A ≠ 3 := by
  intro hr
  let := hA.2
  let ρ := normalizerRepresentation action
  obtain ⟨t,ht,ht1,r,hr1,hr2,htr⟩ :=
    exists_inner_involution_of_rank_ge_three A hA hr.ge
  have hker : LinearMap.ker (ρ t - LinearMap.id) = fixedSpace ρ A := by
    apply le_antisymm
    · intro v hv a
      have hv' : v ∈ LinearMap.ker (action r - LinearMap.id) := by
        change t.val.val v - v = 0 at hv
        change action r v - v = 0
        simpa only [htr] using hv
      obtain ⟨w,hw⟩ := (InvolutionDisplacement.displacement_range_eq_ker r hr1
        (by simpa only [pow_two] using hr2)).symm ▸ hv'
      have hh := hq a a.property t ht w
      change ρ a (ρ t w - w) = ρ t w - w at hh
      have hw' : ρ t w - w = v := by
        change t.val.val w - w = v
        change action r w - w = v at hw
        simpa only [htr] using hw
      rw [hw'] at hh
      exact hh
    · intro v hv
      exact sub_eq_zero.mpr (hv ⟨t,ht⟩)
  let δ := (ρ t - LinearMap.id).domRestrict D
  have hrange : δ.range ≤ Z := by
    rintro _ ⟨v,rfl⟩
    exact hd t ht v v.property
  have hk : δ.ker = (fixedSpace ρ A).comap D.subtype := by
    rw [←hker]
    rfl
  have hqdim : finrank (ZMod 2) (D ⧸ (fixedSpace ρ A).comap D.subtype) ≤ 1 := by
    have he := δ.quotKerEquivRange.finrank_eq
    rw [hk] at he
    exact he.trans_le ((Submodule.finrank_mono hrange).trans hZ)
  let Z' := Z.comap D.subtype
  have hZ' : finrank (ZMod 2) Z' ≤ 1 := by
    have he : finrank (ZMod 2) Z' = finrank (ZMod 2) (D ⊓ Z : Submodule (ZMod 2) V) := by
      rw [←Submodule.finrank_map_subtype_eq,Submodule.map_comap_subtype]
    exact he.le.trans ((Submodule.finrank_mono inf_le_right).trans hZ)
  have himg := rank_le_fixed_codim_mul_displacement_dim
    (subspaceImageRepresentation ρ D) (subspaceImageRepresentation_injective ρ D)
    (restrictedSubgroup ρ D A) ((fixedSpace ρ A).comap D.subtype) Z'
    ((fixedSpace_restrictedSubgroup ρ D A hD).symm.le) (by
      rintro _ ⟨a,ha,rfl⟩ v
      exact hd a ha v v.property)
  have himg' : rank (restrictedSubgroup ρ D A) ≤ 1 :=
    himg.trans ((Nat.mul_le_mul hqdim hZ').trans_eq (by decide))
  let B := subspaceKernel ρ D A
  have hB : rank B ≤ 1 := by
    by_cases hb : B = ⊥
    · simp [hb,rank]
    have hBA : B ≤ A := subspaceKernel_le ρ D A
    have hBe : IsElementaryTwo B := hA.of_le hBA hb
    have hfix := le_fixedSpace_subspaceKernel ρ D A
    have hcf : fixedCodim ρ B ≤ 3 := by
      have hdim := Submodule.finrank_mono hfix
      change finrank (ZMod 2) D ≤ finrank (ZMod 2) (fixedSpace ρ B) at hdim
      have hdimD := D.finrank_quotient_add_finrank
      have hdimB := fixedCodim_add_finrank ρ B
      omega
    exact rank_le_one_of_fixedCodim_le_three B hBe hcf
  have he := rank_subspaceKernel_add_image ρ D A hD (IsElementaryAbelian.isPGroup 2 A)
  change rank B + _ = _ at he
  omega
end ClassicalOrthogonal.FourPlusMatrix.Binary
