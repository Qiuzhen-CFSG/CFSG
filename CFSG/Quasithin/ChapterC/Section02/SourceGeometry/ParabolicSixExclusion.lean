module
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.ChiSixExclusion
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoImages
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.PerfectSubgroups
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.PerfectSpecialLinear
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.SubspaceTransport
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order

/-!
# The symplectic-four and linear-three parabolic exclusions

The perfect A₆ residual keeps its three-rank through the solvable star
kernel. Every perfect subgroup of either Sp₄(4) parabolic or a nontrivial
proper SL₃(2ⁿ) subspace stabilizer has three-rank at most one. The binary
SL₃ case is excluded by the factor five in the residual order.

All maps use the literal star intersection and its subgroup in the star
image of the containing component. Source: Aschbacher–Smith C.2.7(3)(e,g),
printed pp.145–147, used in 3.3.22, p.597.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {H K R M B : Subgroup G}

/-- The literal intersection star image contains a perfect subgroup of three-rank two. -/
theorem starM_perfect_three_rank_two_of_six
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hB : B ≤ M ⊓ K) [Group.IsPerfect B]
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)) :
    ∃ A : Subgroup (starM K R M), Group.IsPerfect A ∧ 2 ≤ primeRank 3 A := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (B ⧸ pCore 2 B) := e.isSimpleGroup
  let q := QuotientGroup.mk' (starKernel K R)
  let f : B →* starM K R M :=
    (q.comp (inclusion (hB.trans inf_le_right |>.trans le_sup_left))).codRestrict _
      (fun b => mem_map_of_mem q (show (b : G) ∈ M ⊓ K from hB b.property))
  let j : f.ker →* (toStarImage K R).ker :=
    { toFun := fun b => ⟨inclusion (hB.trans inf_le_right) b.val, by
        apply Subtype.ext
        exact congrArg (fun a : starM K R M => (a : StarQuotient K R))
          (show f b.val = 1 from b.property)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y hh
    exact Subtype.ext (Subtype.ext (congrArg (fun a => (a.val : G)) hh))
  let : Group.IsSolvable (toStarImage K R).ker := toStarImage_ker_solvable_from_source h
  let : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective hj
  have he : f.rangeRestrict.ker = f.ker := by
    ext x
    exact Subtype.ext_iff
  let : Group.IsSolvable f.rangeRestrict.ker := he.symm ▸ inferInstanceAs (Group.IsSolvable f.ker)
  refine ⟨f.range,Group.IsPerfect.range f,?_⟩
  have hr := PerfectCoreTwoExtension.odd_rank_le_of_solvable_kernel (by decide : Odd 3) f.rangeRestrict
  have hB3 : primeRank 3 B = 2 := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 B) pCore_isPGroup,
      primeRank_equiv 3 e,
      GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 6 3 (by decide) (by decide)]
  rwa [hB3] at hr

private theorem no_sp4_parabolic_perfect_three_rank_two
    {D : Type*} [Group D] [Finite D] (P : Subgroup D)
    (hA : ∃ A : Subgroup P, Group.IsPerfect A ∧ 2 ≤ primeRank 3 A)
    (hp : IsSp4FourMaximalParabolic P) : False := by
  obtain ⟨F,_,_,hF,e,hp⟩ := hp
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
    (by simpa only [Nat.card_eq_fintype_card, show (2 : ℕ)^2 = 4 from rfl] using hF)
  obtain ⟨A,hAp,hAr⟩ := hA
  let := hAp
  let f := e.toMonoidHom.comp (P.subtype.comp A.subtype)
  have hf : Function.Injective f := e.injective.comp (P.subtype_injective.comp A.subtype_injective)
  have hr : f.range ≤ P.map e.toMonoidHom := by
    rintro _ ⟨a,rfl⟩
    exact mem_map_of_mem _ a.val.property
  exact Theory.SpecificGroups.SymplecticFour.no_perfect_odd_rank_two_in_parabolic
    (by decide : Odd 3) hAr f hf (by
      rcases hp with hh | hh
      · exact Or.inl (hh ▸ hr)
      · exact Or.inr (hh ▸ hr))

/-- C.2.7's actual Sp4(4) parabolic cannot contain the A6 residual image. -/
theorem no_sp4_parabolic_of_six
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hB : B ≤ M ⊓ K) [Group.IsPerfect B]
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))
    (hp : IsSp4FourMaximalParabolic ((starM K R M).subgroupOf (starImage K R K))) : False := by
  obtain ⟨A,hAp,hAr⟩ := starM_perfect_three_rank_two_of_six h hB e
  let t := (subgroupOfEquivOfLe (starM_le K R M)).symm
  apply no_sp4_parabolic_perfect_three_rank_two _ _ hp
  let := hAp
  refine ⟨A.map t.toMonoidHom,Group.IsPerfect.map _,?_⟩
  rwa [primeRank_equiv 3 (t.subgroupMap A)] at hAr

private theorem linearStabilizer_eq_parabolicSL {F : Type*} [Field F] {n : ℕ}
    (W : Submodule F (Fin n → F)) : linearStabilizer W = Matrix.HigherLinear.parabolicSL W := by
  ext g
  rw [linearStabilizer, Subgroup.mem_comap, Submodule.stabilizer_coe,
    MulAction.mem_stabilizer_set]
  rfl

private theorem perfect_parabolic_subspace_rank
    {A : Type*} [Group A] [Finite A] [Group.IsPerfect A]
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F)
    (W : Submodule F (Fin 3 → F)) (hW : W ≠ ⊥) (hWt : W ≠ ⊤)
    (f : A →* linearStabilizer W) (hf : Function.Injective f) : primeRank 3 A ≤ 1 := by
  let e := MulEquiv.subgroupCongr (linearStabilizer_eq_parabolicSL W)
  rcases Matrix.PSL3.LinearThree.SubspaceTransport.exists_parabolic_equiv W hW hWt with ha | ha
  · obtain ⟨a⟩ := ha
    let j := (Matrix.PSL3.LinearThree.pointParabolicSL F).subtype.comp
      ((e.trans a).toMonoidHom.comp f)
    exact Matrix.PSL3.LinearThree.PerfectSubgroups.perfect_parabolicSL_rank
      (by decide : Odd 3) hF j
      ((Matrix.PSL3.LinearThree.pointParabolicSL F).subtype_injective.comp
        ((e.trans a).injective.comp hf))
      (Or.inl (by rintro _ ⟨x,rfl⟩; exact (e.trans a (f x)).property))
  · obtain ⟨a⟩ := ha
    let j := (Matrix.PSL3.LinearThree.lineParabolicSL F).subtype.comp
      ((e.trans a).toMonoidHom.comp f)
    exact Matrix.PSL3.LinearThree.PerfectSubgroups.perfect_parabolicSL_rank
      (by decide : Odd 3) hF j
      ((Matrix.PSL3.LinearThree.lineParabolicSL F).subtype_injective.comp
        ((e.trans a).injective.comp hf))
      (Or.inr (by rintro _ ⟨x,rfl⟩; exact (e.trans a (f x)).property))

/-- The literal special-linear three-space parabolic excludes an A6 residual. -/
theorem no_linearThree_parabolic_of_six
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hB : B ≤ M ⊓ K) [Group.IsPerfect B]
    (e6 : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))
    (F : Type) [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2^n)
    (hp : IsLinearMaximalParabolic ((starM K R M).subgroupOf (starImage K R K)) 3 F) : False := by
  obtain ⟨e,W,hW,hWt,hP⟩ := hp
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  by_cases hn1 : n = 1
  · have hf2 : Nat.card F = 2 := by simpa [hn1] using hF
    have hc : Nat.card SL(3,F) = 168 := by
      have hs := (center SL(3,F)).card_mul_index
      rw [index_eq_card,Atlas.ExceptionalSupport.card_sl_center,Fintype.card_fin,hf2,
        Matrix.PSL3.LinearThree.card_projective,hf2] at hs
      norm_num at hs
      exact hs.symm
    have hd := (starM_five_dvd_of_six h hB e6).trans (card_dvd_of_le (starM_le K R M))
    rw [Nat.card_congr e.toEquiv,hc] at hd
    norm_num at hd
  · have hF4 : 4 ≤ Nat.card F := by
      rw [hF]
      exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ n)
    obtain ⟨A,hAp,hAr⟩ := starM_perfect_three_rank_two_of_six h hB e6
    let := hAp
    let t := (subgroupOfEquivOfLe (starM_le K R M)).symm
    let j := t.trans ((e.subgroupMap _).trans (MulEquiv.subgroupCongr hP))
    have hr := perfect_parabolic_subspace_rank hF4 W hW hWt
      (j.toMonoidHom.comp A.subtype) (j.injective.comp A.subtype_injective)
    omega
end CFSG.Quasithin.ChapterC.C27Source
