module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianConstituents
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedKernelHigher.OrthogonalSourceGeometry
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedNormalModels
public import Theory.Representation.BinaryOffender.IrreducibleSubspaceExistence
public import Theory.Representation.BinaryOffender.Homogeneous.Dimension
public import Theory.Representation.BinaryAlternatingSixModels.Schur
public import Theory.Representation.BinaryPermutation.FiveRankOneActors
public import Theory.Representation.BinaryPermutation.SevenCommutant
public import Theory.Representation.BinaryPermutation.EightCommutant
public import Theory.Representation.AlternatingSevenConjugatePair.ElementaryGeometry
public import Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.TreeWreathModel
public import Theory.GroupTheory.WreathTwoElementaryRank

/-!
# Multiplicity of the original marked constituent

The actual homogeneous component orbit has exactly two copies of its proper
marked constituent. At higher multiplicity, the proved orthogonal-constituent
construction supplies a second constituent stabilized by a noncentral actor.
G.6.4 recognizes its rank-one displacement as a natural alternating action.
Its scalar commutant and automorphism rank contradict higher multiplicity.
The original fixed-line action then determines the constituent degree.

The orthogonal construction and natural-model recognition are imported from
independent representation modules in the Chapter 14 development. The Schur
comparison adapts CaseOneLarge/HigherMultiplicity, without its ambient source
hypotheses. Source: Aschbacher--Smith G.11.6--9, printed pp.365--369, and
12.9.4, printed pp.859--860.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MonoidAlgebra
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
namespace FixedLineConstituent
open Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.MarkedHigherOrthogonal
private theorem end_finrank_le_one_of_trivial_commutant
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (ρ : Representation (ZMod 2) D W)
    [IsIrreducible ρ]
    (hc : ∀ f : W ≃ₗ[ZMod 2] W, (∀ a w, f (ρ a w) = ρ a (f w)) →
      f = LinearEquiv.refl _ _) :
    finrank (ZMod 2) (IntertwiningMap ρ ρ) ≤ 1 := by
  apply finrank_le_one_iff.mpr
  refine ⟨IntertwiningMap.id ρ,fun f => ?_⟩
  rcases IsIrreducible.bijective_or_eq_zero f with hf | rfl
  · have he := hc (f.ofBijective hf).toLinearEquiv f.isIntertwining
    refine ⟨1,?_⟩
    rw [one_smul]
    ext w
    exact (congrArg (fun a : W ≃ₗ[ZMod 2] W => a w) he).symm
  · exact ⟨0,zero_smul _ _⟩

private theorem natural_schur_bound (n : ℕ) (hn5 : 5 ≤ n) (hn8 : n ≤ 8) :
    finrank (ZMod 2) (IntertwiningMap (BinaryPermutation.alternatingNaturalRepresentation (Fin n))
      (BinaryPermutation.alternatingNaturalRepresentation (Fin n))) ≤ 1 := by
  let := BinaryPermutation.alternatingNatural_isIrreducible (Ω := Fin n) (by simpa using hn5)
  interval_cases n
  · apply end_finrank_le_one_of_trivial_commutant
    intro f hf
    exact Representation.FivePointActors.natural_commuting_eq_refl _ (MulEquiv.refl _)
      (LinearEquiv.refl _ _) (fun _ _ => rfl) f hf
  · exact BinaryAlternatingSix.Schur.natural_end_finrank_one.le
  · apply end_finrank_le_one_of_trivial_commutant
    intro f hf
    apply LinearEquiv.toLinearMap_injective
    exact BinaryPermutation.SevenCommutant.commuting_eq_id f.toLinearMap f.injective hf
  · exact end_finrank_le_one_of_trivial_commutant _ BinaryPermutation.EightCommutant.commuting_eq_refl

private theorem natural_automorphism_rank (n : ℕ) (hn5 : 5 ≤ n) (hn8 : n ≤ 8) :
    primeRank 2 (MulAut (alternatingGroup (Fin n))) ≤ n - 3 := by
  interval_cases n
  · exact Theory.SpecificGroups.Alternating.FiveExtensionAction.automorphism_primeRank_two_le
  · exact ChapterG.Section09.DefiningCharacteristic.AlternatingSixCover.alternating_six_automorphism_two_rank
  · let e : Equiv.Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
      MulEquiv.ofBijective _ (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
        7 (by decide) (by decide))
    rw [← primeRank_equiv 2 e]
    have he := Representation.AlternatingSevenConjugatePair.ElementaryGeometry.primeRank_symmetric
    change primeRank 2 (Equiv.Perm (Fin 7)) = 3 at he
    omega
  · let e : Equiv.Perm (Fin 8) ≃* MulAut (alternatingGroup (Fin 8)) :=
      MulEquiv.ofBijective _ (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
        8 (by decide) (by decide))
    rw [← primeRank_equiv 2 e]
    let S := Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.treeSylow
    rw [S.primeRank_eq]
    have hb : primeRank 2 Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.treeGroup ≤ 4 := by
      rw [primeRank_equiv 2 Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.treeWreathEquiv]
      apply WreathTwoElementaryRank.rank_bound (r := 2) _ (by decide)
      apply primeRank_le_of_noncommutative_card_prime_pow (n := 2)
      · norm_num [DihedralGroup.nat_card,DihedralGroup.card]
      · exact DihedralGroup.not_commutative (by decide) (by decide)
    exact hb.trans (by decide)

private theorem natural_schur_rank_gap
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (ρ : Representation (ZMod 2) D W)
    (n : ℕ) (hn5 : 5 ≤ n) (hn8 : n ≤ 8)
    (hm : ChapterG.Section09.Quasiequivalent ρ (BinaryPermutation.alternatingNaturalRepresentation (Fin n))) :
    2 * (finrank (ZMod 2) (IntertwiningMap ρ ρ) + primeRank 2 (MulAut D) + 1) <
      3 * finrank (ZMod 2) W := by
  obtain ⟨e,c,hc⟩ := hm
  let f : ρ.Equiv ((BinaryPermutation.alternatingNaturalRepresentation (Fin n)).comp e.toMonoidHom) :=
    .mk c (fun a => LinearMap.ext (hc a))
  have hs := ((BinaryAlternatingSix.Schur.endEquiv f).trans
    (BinaryAlternatingSix.Schur.endCompEquiv _ e)).finrank_eq
  have hb := natural_schur_bound n hn5 hn8
  have hr := natural_automorphism_rank n hn5 hn8
  rw [← hs] at hb
  rw [← primeRank_equiv 2 (MulAut.congr e)] at hr
  have hd := c.finrank_eq
  interval_cases n
  · rw [BinaryPermutation.finrank_natural_odd (Fin 5) (by decide),Fintype.card_fin] at hd
    omega
  · rw [BinaryPermutation.finrank_natural_even (Fin 6) (by decide),Fintype.card_fin] at hd
    omega
  · rw [BinaryPermutation.finrank_natural_odd (Fin 7) (by decide),Fintype.card_fin] at hd
    omega
  · rw [BinaryPermutation.finrank_natural_even (Fin 8) (by decide),Fintype.card_fin] at hd
    omega

private theorem orthogonal_rank_one
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] {ρ : Representation (ZMod 2) D W}
    {B : LinearMap.BilinForm (ZMod 2) W} {v : W} {E I J : Submodule (ZMod 2) W}
    {X : Subgroup D} [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
    (hyp : ChapterG.Section10.Hypothesis ρ B v E X X₀) (hi : IsIrreducible ρ)
    (H : Subgroup D) [H.Normal] (hJ : IsIrrPlus ρ H J)
    (hv : v ∈ I) (hvJ : v ∉ J) (hperp : J ≤ B.orthogonal I)
    (hf : Function.Injective (invariantSubspace ρ H J hJ.choose).toRepresentation)
    (a : X) (ha : (a : D) ∈ subspaceStabilizer ρ J)
    (hc : (a : D) ∉ centralizer (H : Set D)) :
    finrank (ZMod 2) (LinearMap.range ((ρ a - 1).comp J.subtype)) = 1 := by
  have hle : LinearMap.range ((ρ a - 1).comp J.subtype) ≤ J ⊓ E := by
    rintro w ⟨u,rfl⟩
    exact ⟨J.sub_mem ((ha u).mpr u.property) u.property,
      hyp.displacement a u (hperp u.property v hv)⟩
  have hb := (Submodule.finrank_mono hle).trans
    (hyp.constituent_inter_W_finrank_le_one hi H hJ hvJ)
  have hp : finrank (ZMod 2) (LinearMap.range ((ρ a - 1).comp J.subtype)) ≠ 0 := by
    intro hz
    apply hc
    apply centralizes_of_fixes_faithful_section ρ H J hJ.choose
    · intro b hb hbfix
      have he : (invariantSubspace ρ H J hJ.choose).toRepresentation ⟨b,hb⟩ =
          (invariantSubspace ρ H J hJ.choose).toRepresentation 1 := by
        rw [map_one]
        apply LinearMap.ext
        intro w
        apply Subtype.ext
        exact hbfix w w.property
      exact congrArg Subtype.val (hf he)
    · exact le_normalizer_of_normal (mem_top _)
    · intro w hw
      have he : ρ a w - w ∈ LinearMap.range ((ρ a - 1).comp J.subtype) := ⟨⟨w,hw⟩,rfl⟩
      rw [Submodule.finrank_eq_zero.mp hz] at he
      exact sub_eq_zero.mp he
  omega

variable {D A : Type*} [Group D] [Finite D] [AddCommGroup A]
  [Module (ZMod 2) A] [FiniteDimensional (ZMod 2) A]
  {ρ : Representation (ZMod 2) D A} {B : LinearMap.BilinForm (ZMod 2) A}
  {v : A} {W : Submodule (ZMod 2) A} {X : Subgroup D}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
  (h : ChapterG.Section10.Hypothesis ρ B v W X X₀)
  (hns : ¬ Group.IsSolvable D)
  (cover : ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple D)
  (S : Sylow 2 D) (hnX : (S : Subgroup D) ≤ normalizer (X : Set D))
  {C : Subgroup D} (hC : IsComponent D C) (hm : ⁅C,X⁆ ≠ ⊥)
  {I : Submodule (ZMod 2) A} (hI : IsIrrPlus ρ (componentOrbit C ⊤) I)
  (hv : v ∈ I) (hp : I ≠ ⊤)
include h hns cover hnX hC hm hI hv hp

private theorem homogeneous_data :
    let R := invariantSubspace ρ (componentOrbit C ⊤) I hI.choose
    Homogeneous.homogeneousPart R ⊤ = ⊤ ∧ Function.Injective R.toRepresentation ∧
      (∀ J : Subrepresentation (ρ.comp (componentOrbit C ⊤).subtype),
        IsIrreducible J.toRepresentation → Homogeneous.SameModule R J) ∧
      (∀ u ∈ I, ∀ w ∈ I, B u w = 0) := by
  have hind := cover.component_normalizer_index_le_two hC
  obtain ⟨hh,hf,_,hiso | ⟨ht,_⟩⟩ :=
    h.constituent_homogeneous_faithful_selfDual_of_point_mem hns hC hm S hnX hind hI hv
  · exact ⟨hh,hf,h.constituent_sameModule_of_point_mem hns hC hm S hnX hind hI hv,hiso⟩
  · exact (hp ht).elim

/-- Higher multiplicity supplies an actual stable constituent in the marked
constituent's perpendicular, disjoint from its original marked point. -/
theorem stable_orthogonal_of_higher
    (hd : 2 * finrank (ZMod 2) I < finrank (ZMod 2) A) (x : X) :
    ∃ J : Submodule (ZMod 2) A, IsIrrPlus ρ (componentOrbit C ⊤) J ∧
      v ∉ J ∧ J ≤ B.orthogonal I ∧ (x : D) ∈ subspaceStabilizer ρ J := by
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  let : Group.IsPerfect H := hC.orbit_isPerfect ⊤
  let : Nontrivial H := H.nontrivial_iff_ne_bot.mpr hC.componentOrbit_top_ne_bot
  have hi := h.irreducible_of_not_solvable hns
  let R := invariantSubspace ρ H I hI.choose
  let : IsIrreducible R.toRepresentation := hI.irreducible_of_normal_restriction ρ hi H
  let : IsSemisimpleModule (ZMod 2)[H] (Representation.asModule (ρ.comp H.subtype)) :=
    NormalConstituentDisplacement.restriction_semisimple ρ hi H
  obtain ⟨_,_,hsame,hiso⟩ := homogeneous_data h hns cover S hnX hC hm hI hv hp
  have hxx : (x : D) * x = 1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) (x : D) x.property
  obtain ⟨J,hJ,hdis,hperp,hxJ⟩ := exists_stable_orthogonal_simple
    ρ H R hsame B h.preserves h.alternating h.nondegenerate hiso x hxx
    (h.stabilizes_constituent_of_point_mem hi H hI hv x.property) hd
  have hJs : H ≤ subspaceStabilizer ρ J.toSubmodule := by
    apply le_subspaceStabilizer
    exact fun a ha w hw => J.apply_mem_toSubmodule ⟨a,ha⟩ hw
  have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ
    h.faithful hi H hC.componentOrbit_top_ne_bot
  have hnfix : ¬ J.toSubmodule ≤ fixedSpace ρ H := by
    intro he
    apply ((Subrepresentation.irreducible_iff_isAtom J).mp hJ).ne_bot
    apply Subrepresentation.toSubmodule_injective
    exact le_bot_iff.mp (he.trans_eq hfix)
  obtain ⟨K,hKJ,hK⟩ := exists_isIrrPlus_le_of_not_fixed ρ H J.toSubmodule hJs hnfix
  let R' : Subrepresentation (ρ.comp H.subtype) :=
    ⟨K,fun a w hw => (hK.choose a.property w).mpr hw⟩
  have hRJ : R' = J := ((Subrepresentation.irreducible_iff_isAtom J).mp hJ).le_iff_eq
    (fun hb => hK.ne_bot ρ (congrArg Subrepresentation.toSubmodule hb)) |>.mp hKJ
  have hJI : IsIrrPlus ρ H J.toSubmodule := (congrArg Subrepresentation.toSubmodule hRJ) ▸ hK
  exact ⟨J.toSubmodule,hJI,(fun hvJ => h.point_ne_zero
    ((Submodule.disjoint_def.mp hdis) v hv hvJ)),hperp,hxJ⟩

/-- A higher-multiplicity marked constituent has the literal natural
alternating action, obtained from a constructed orthogonal constituent. -/
theorem natural_model_of_higher
    (hd : 2 * finrank (ZMod 2) I < finrank (ZMod 2) A) :
    ∃ n, 5 ≤ n ∧ n ≤ 8 ∧
      ChapterG.Section09.Quasiequivalent
        (invariantSubspace ρ (componentOrbit C ⊤) I hI.choose).toRepresentation
        (BinaryPermutation.alternatingNaturalRepresentation (Fin n)) := by
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  let : Group.IsPerfect H := hC.orbit_isPerfect ⊤
  let : Nontrivial H := H.nontrivial_iff_ne_bot.mpr hC.componentOrbit_top_ne_bot
  have hi := h.irreducible_of_not_solvable hns
  obtain ⟨_,hfaith,hsame,_⟩ := homogeneous_data h hns cover S hnX hC hm hI hv hp
  have hnon : ¬ X ≤ centralizer (H : Set D) := by
    intro he
    apply hm
    rw [commutator_comm,commutator_eq_bot_iff_le_centralizer]
    exact (centralizer_le (le_componentOrbit C ⊤)).trans' he
  obtain ⟨x,hx,hxc⟩ := SetLike.not_le_iff_exists.mp hnon
  let a : X := ⟨x,hx⟩
  obtain ⟨J,hJ,hvJ,hperp,hxJ⟩ := stable_orthogonal_of_higher h hns cover S hnX hC hm hI hv hp hd a
  let Q := invariantSubspace ρ H J hJ.choose
  have hiQ : IsIrreducible Q.toRepresentation := hJ.irreducible_of_normal_restriction ρ hi H
  obtain ⟨f,hf⟩ := hsame Q hiQ
  have hfQ : Function.Injective Q.toRepresentation := by
    intro b c he
    apply hfaith
    apply LinearMap.ext
    intro w
    apply f.injective
    exact (hf b w).trans ((LinearMap.congr_fun he (f w)).trans (hf c w).symm)
  have hr := orthogonal_rank_one h hi H hJ hv hvJ hperp hfQ a hxJ hxc
  have hdual := constituent_selfDual_of_sameModule ρ H hi B h.preserves
    h.nondegenerate hJ (fun K hK => (hsame Q hiQ).symm.trans (hsame K hK))
  obtain ⟨n,hn5,hn8,_,e,c,hc⟩ := ChapterG.Section11.normal_constituent_natural_model
    ρ H (zpowers x) J hJ.choose (zpowers_le.mpr hxJ)
    hiQ hfQ (hJ.finrank_gt_two ρ H) hdual ⟨cover⟩ ⟨x,mem_zpowers _⟩
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx) hr
  exact ⟨n,hn5,hn8,e,f.trans c,fun b w => by change c (f (_)) = _; rw [hf,hc]; rfl⟩

/-- Every proper marked constituent occurs exactly twice. This uses the
actual G.10 geometry and SQTK cover, without a low-rank witness. -/
theorem double_of_proper :
    let R := invariantSubspace ρ (componentOrbit C ⊤) I hI.choose
    finrank (ZMod 2) A = 2 * finrank (ZMod 2) I ∧
      Nonempty (Representation.Equiv (ρ.comp (componentOrbit C ⊤).subtype)
        (R.toRepresentation.prod R.toRepresentation)) := by
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  let : Group.IsPerfect H := hC.orbit_isPerfect ⊤
  let R := invariantSubspace ρ H I hI.choose
  have hi := h.irreducible_of_not_solvable hns
  have hiR := hI.irreducible_of_normal_restriction ρ hi H
  obtain ⟨hh,_,_,hiso⟩ := homogeneous_data h hns cover S hnX hC hm hI hv hp
  have hl := B.twice_finrank_le_of_isotropic h.nondegenerate I hiso
  have hu : finrank (ZMod 2) A ≤ 2 * finrank (ZMod 2) I := by
    by_contra hu
    obtain ⟨n,hn5,hn8,hmodel⟩ := natural_model_of_higher h hns cover S hnX hC hm hI hv hp (by omega)
    have hg := natural_schur_rank_gap R.toRepresentation n hn5 hn8 hmodel
    have hdis := h.centralizer_displacement_range_and_ker hi H hC.componentOrbit_top_ne_bot
      R hiR hh hv (hI.finrank_gt_two ρ H)
    have hr := finrank_le_schur_add_automorphism_rank ρ h.faithful H X R (B.orthogonal I) hdis
    have hq := (Group.rank_le_of_surjective (QuotientGroup.mk' X₀)
      (QuotientGroup.mk'_surjective _)).trans (IsElementaryAbelian.rank_le_finrank (p := 2) X)
    have hd := h.dimension_bound.1
    have hlt : finrank (ZMod 2) A < 3 * finrank (ZMod 2) I := by
      change 2 * (finrank (ZMod 2) (IntertwiningMap R.toRepresentation R.toRepresentation) +
        primeRank 2 (MulAut H) + 1) < 3 * finrank (ZMod 2) I at hg
      omega
    exact hu (Homogeneous.degree_le_double_of_lt_triple R hiR hh hp hlt)
  exact ⟨by omega,Homogeneous.double_coordinates_of_degree_le R hiR hh hp hu⟩

end FixedLineConstituent
/-- If the original actor is faithful on its marked transvection space,
common fixed spaces for the component centralizer bound that kernel by two.
This does not assume a multiplicity or a low-rank witness. -/
private theorem centralizer_card_le_two
    {D A : Type*} [Group D] [Finite D] [AddCommGroup A]
    [Module (ZMod 2) A] [FiniteDimensional (ZMod 2) A]
    {ρ : Representation (ZMod 2) D A} {B : LinearMap.BilinForm (ZMod 2) A}
    {v : A} {W : Submodule (ZMod 2) A} {X : Subgroup D}
    [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
    (h : ChapterG.Section10.Hypothesis ρ B v W X X₀)
    (hfaith : ∀ x y : X, (∀ w : W, ρ x w = ρ y w) → x = y)
    (H : Subgroup D) (K : Submodule (ZMod 2) A)
    (hker : ∀ c : X, (c : D) ∈ centralizer (H : Set D) → c ≠ 1 →
      LinearMap.ker (ρ c - LinearMap.id) = K) :
    Nat.card ((centralizer (H : Set D)).subgroupOf X) ≤ 2 := by
  classical
  let Y := (centralizer (H : Set D)).subgroupOf X
  change Nat.card Y ≤ 2
  by_cases hy : Y = ⊥
  · rw [hy,Subgroup.card_bot]; decide
  have hWK : ¬ W ≤ K := by
    intro hle
    obtain ⟨c,hc⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hy
    have hcX : (c : X) ≠ 1 := fun he => hc (Subtype.ext he)
    apply hcX
    apply hfaith
    intro w
    rw [Subgroup.coe_one,map_one,Module.End.one_apply]
    apply sub_eq_zero.mp
    change w.val ∈ LinearMap.ker (ρ (c : X) - LinearMap.id)
    rw [hker (c : X) c.property hcX]
    exact hle w.property
  obtain ⟨w,hw,hwK⟩ := SetLike.not_le_iff_exists.mp hWK
  have hfree (y : Y) (hy : ρ (y : X) w = w) : y = 1 := by
    by_contra hy1
    apply hwK
    rw [← hker (y : X) y.property (fun he => hy1 (Subtype.ext he))]
    exact sub_eq_zero.mpr hy
  have hinj : Function.Injective (fun y : Y => ρ (y : X) w) := by
    intro a b hab
    dsimp only at hab
    have he : a⁻¹ * b = 1 := by
      apply hfree
      change ρ ((a : D)⁻¹ * b) w = w
      rw [map_mul,Module.End.mul_apply,← hab,← Module.End.mul_apply,← map_mul,
        inv_mul_cancel,map_one,Module.End.one_apply]
    exact inv_mul_eq_one.mp he
  let c (y : Y) : ZMod 2 := (h.transvections (y : X)).choose ⟨w,hw⟩
  have hc (y : Y) : ρ (y : X) w = w + c y • v :=
    (h.transvections (y : X)).choose_spec.2 ⟨w,hw⟩
  have hci : Function.Injective c := by
    intro a b he
    apply hinj
    change ρ (a : X) w = ρ (b : X) w
    rw [hc a,hc b,he]
  simpa only [Nat.card_zmod] using Nat.card_le_card_of_injective c hci

private theorem elementary_quotient_rank
    {X : Type*} [Group X] [Finite X] [IsElementaryAbelian 2 X]
    (Y : Subgroup X) (hcard : Nat.card Y ≤ 2) :
    (Nat.card Y = 1 ∧ finrank (ZMod 2) (Additive X) = finrank (ZMod 2) (Additive (X ⧸ Y))) ∨
    (Nat.card Y = 2 ∧ finrank (ZMod 2) (Additive X) = finrank (ZMod 2) (Additive (X ⧸ Y)) + 1) := by
  have hcX : Nat.card X = 2 ^ finrank (ZMod 2) (Additive X) := by
    rw [Nat.card_congr Additive.ofMul,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  have hcQ : Nat.card (X ⧸ Y) = 2 ^ finrank (ZMod 2) (Additive (X ⧸ Y)) := by
    rw [Nat.card_congr Additive.ofMul,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  have he := Y.index_mul_card
  rw [Subgroup.index_eq_card,hcX,hcQ] at he
  have hp : 0 < Nat.card Y := Nat.card_pos
  rcases (show Nat.card Y = 1 ∨ Nat.card Y = 2 by omega) with h1 | h2
  · rw [h1,mul_one] at he
    exact Or.inl ⟨h1,((Nat.pow_right_injective (by decide : 2 ≤ 2)) he).symm⟩
  · rw [h2,← pow_succ] at he
    exact Or.inr ⟨h2,((Nat.pow_right_injective (by decide : 2 ≤ 2)) he).symm⟩

open Section02 Section08 Section08.InvariantFlag Section08.InvariantFlag.Symplectic
open ChapterG.Section11
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V : Subgroup G} {n : ℕ}

/-- Exact two-copy data on the original marked constituent, with the literal
centralizer quotient. A nontrivial actor kernel has order two and loses one
binary dimension. The original module, orbit and action are retained. -/
@[expose] def FixedLineConstituent.DoubleData
    (F : InvariantFlag T V n) [IsElementaryAbelian 2 F.Uhat]
    (g : G) [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (J : Subgroup F.TerminalHdot) (I : Submodule (ZMod 2) (Additive F.Uhat))
    (hI : IsIrrPlus F.terminalRepresentation (componentOrbit J ⊤) I) : Prop :=
  let R := invariantSubspace F.terminalRepresentation (componentOrbit J ⊤) I hI.choose
  let X := F.terminalDot (F.X g)
  let Y := (centralizer (componentOrbit J ⊤ : Set F.TerminalHdot)).subgroupOf X
  finrank (ZMod 2) (Additive F.Uhat) = 2 * finrank (ZMod 2) I ∧
    Nonempty (Representation.Equiv (F.terminalRepresentation.comp (componentOrbit J ⊤).subtype)
      (R.toRepresentation.prod R.toRepresentation)) ∧
    finrank (ZMod 2) I = finrank (ZMod 2) (Additive X) + 1 ∧
    ((Nat.card Y = 1 ∧ finrank (ZMod 2) I = finrank (ZMod 2) (Additive (X ⧸ Y)) + 1) ∨
     (Nat.card Y = 2 ∧ finrank (ZMod 2) I = finrank (ZMod 2) (Additive (X ⧸ Y)) + 2))

/-- Construct the two-copy multiplicity and exact kernel on the selected
original marked constituent. All source premises remain on the same flag. -/
theorem nonabelian_marked_constituent_double
    (modules : Theorem1222ModulesOfMany.{u} KnownSimple.IsKnownSimple)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (preferred : PreferredDimension KnownSimple.IsKnownSimple T n)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (four : NaturalReduction KnownSimple.IsKnownSimple.{u} 4)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hg10 : ChapterG.Section10.Hypothesis F.terminalRepresentation B v (hatSpace F (F.E g))
      (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hS : NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)))
    {J : Subgroup F.TerminalHdot} (hJ : IsComponent F.TerminalHdot J)
    (hm : ⁅J,F.terminalDot (F.X g)⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation (componentOrbit J ⊤)
      (F.terminalDot (F.X g)) I)
    (hdata : FixedLineConstituent.MarkedData F.terminalRepresentation B v
      (F.terminalDot (F.X g)) J I hI) :
    FixedLineConstituent.DoubleData F g J I hI.isIrrPlus := by
  obtain ⟨hv,hp,_,_,_,_,_,_,_,_,hdis,_⟩ := hdata
  obtain ⟨S,_,hXS,hnS⟩ := hS
  have hnX := (normal_subgroupOf_iff_le_normalizer hXS).mp hnS
  obtain ⟨hd,he⟩ := FixedLineConstituent.double_of_proper hg10
    (nonabelian_hat_not_solvable h hn F hne) (nonabelian_sqtkCover h F)
    S hnX hJ hm hI.isIrrPlus hv hp
  obtain ⟨_,_,_,_,_,hfaith,_,_,hr,_⟩ := nonabelian_fixed_line_lagrangian
    modules h hn preferred earlier four F hne g hgP hgH
  have hdI : finrank (ZMod 2) I = finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) + 1 := by omega
  have hb := centralizer_card_le_two hg10 hfaith (componentOrbit J ⊤) (B.orthogonal I)
    (fun c hc hc1 => (hdis c hc hc1).2)
  refine ⟨hd,he,hdI,?_⟩
  rcases elementary_quotient_rank _ hb with ⟨hcard,hq⟩ | ⟨hcard,hq⟩
  · exact Or.inl ⟨hcard,by omega⟩
  · exact Or.inr ⟨hcard,by omega⟩

/-- Apply the new multiplicity theorem to the constituent actually selected
from the original source flag. The exchanged branch is kept explicitly;
no constituent selection, kernel size or multiplicity is assumed. -/
theorem nonabelian_fixed_line_constituents_double
    (modules : Theorem1222ModulesOfMany.{u} KnownSimple.IsKnownSimple)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (preferred : PreferredDimension KnownSimple.IsKnownSimple T n)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (four : NaturalReduction KnownSimple.IsKnownSimple.{u} 4)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ hX : IsElementaryAbelian 2 (F.terminalDot (F.X g)),
      let := hX
      ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat),
        ChapterG.Section10.Hypothesis F.terminalRepresentation B v (hatSpace F (F.E g))
          (F.terminalDot (F.X g))
          ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
        hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v} ∧
        NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
        ∃ J : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot J ∧
          ⁅J,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧
          ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B J ∧
          ∃ I : Submodule (ZMod 2) (Additive F.Uhat),
          ∃ hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation (componentOrbit J ⊤)
            (F.terminalDot (F.X g)) I,
          (FixedLineConstituent.MarkedData F.terminalRepresentation B v
              (F.terminalDot (F.X g)) J I hI ∧
            FixedLineConstituent.DoubleData F g J I hI.isIrrPlus ∧
            (Function.Injective (fun x : F.terminalDot (F.X g) =>
              (F.terminalRepresentation (x : F.TerminalHdot)).comp I.subtype) →
              ¬ Nonempty (componentOrbit J ⊤ ≃* alternatingGroup (Fin 6)))) ∨
          (v ∉ I ∧ ChapterG.Section10.ExchangedConstituentGeometry
            F.terminalRepresentation B v (hatSpace F (F.E g)) (F.terminalDot (F.X g)) I) := by
  obtain ⟨hX,B,v,hg10,hline,hS,J,hJ,hm,ho,I,hI,hmarked | hex⟩ :=
    nonabelian_fixed_line_constituents modules h hn preferred earlier four F hne g hgP hgH
  · let := hX
    exact ⟨hX,B,v,hg10,hline,hS,J,hJ,hm,ho,I,hI,Or.inl ⟨hmarked.1,
      nonabelian_marked_constituent_double modules h hn preferred earlier four F hne g hgP hgH
        hg10 hS hJ hm hI hmarked.1,hmarked.2⟩⟩
  · exact ⟨hX,B,v,hg10,hline,hS,J,hJ,hm,ho,I,hI,Or.inr hex⟩

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
