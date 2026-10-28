module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.MarkedMultiplicity
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedKernelHigher.OrthogonalSourceGeometry
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedNormalModels
public import Theory.Representation.BinaryOffender.IrreducibleSubspaceExistence
public import Theory.Representation.BinaryOffender.Homogeneous.Dimension
public import Theory.Representation.BinaryAlternatingSixModels.Schur
public import Theory.Representation.BinaryPermutation.FiveRankOneActors
public import Theory.Representation.BinaryPermutation.SevenCommutant
public import Theory.Representation.BinaryPermutation.EightCommutant

/-!
# Exactly two copies of the original marked constituent

Suppose the component orbit has more than two copies of its constituent
through the marked point. The original form makes that constituent isotropic.
The homogeneous multiplicity-space argument then supplies, for any actor,
a disjoint stable constituent in its perpendicular. A noncentral actor has
rank-one displacement on this second constituent. Its faithful self-dual
action therefore identifies the actual orbit and constituent with the natural
A₅, A₆, A₇ or A₈ module.

These natural modules have scalar endomorphisms. The existing centralizer
displacement bound, combined with the actual automorphism two-rank, places
the whole degree below three constituent degrees. Homogeneity forces exactly
two copies, contrary to the initial assumption. The final application removes
the multiplicity premise from the literal actor-centralizer quotient bound.

All statements retain the original flag, action, and marked point. Neither
fixed-point clause is discarded. Recognition of the remaining two-copy
models and conversion to the marked 14.4.2 catalogue remain separate assembly
obligations; these results do not establish source 14.4.14.

The stable orthogonal constituent is the proved G.11.9(1) construction from
the rank-two source family, applied here to the original rank-three flag.
Source: Aschbacher--Smith G.10.12--16, G.11.7--9 and 14.4.2,
printed pp.360--369,1006--1007; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MonoidAlgebra
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter14.Section03.NonabelianSource.Recognition
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension LargerDimension.LocalAction.Components
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

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
  (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
  (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
  (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
  (classification : EarlierFaithfulClassification G (T : Subgroup G))
  (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
  (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
  (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
  [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
    (hatSpace F (F.E g)) (F.terminalDot (F.X g))
    ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
  {C : Subgroup F.TerminalHdot} (hC : IsComponent F.TerminalHdot C)
  (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
  {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (hI : IsIrrPlus F.terminalRepresentation (componentOrbit C ⊤) I) (hv : v ∈ I)

include d earlier hq chosen structural alternatives hne hZ hlarge hgP hgH hyp hC hm hI hv

private theorem higher_homogeneous_data :
    let R := invariantSubspace F.terminalRepresentation (componentOrbit C ⊤) I hI.choose
    Homogeneous.homogeneousPart R ⊤ = ⊤ ∧ Function.Injective R.toRepresentation ∧
      (∀ J : Subrepresentation (F.terminalRepresentation.comp (componentOrbit C ⊤).subtype),
        IsIrreducible J.toRepresentation → Homogeneous.SameModule R J) := by
  let := chosen.elementary
  let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
  obtain ⟨hXP,hN⟩ := source_terminal_actor_normal_in_sylow d earlier hq chosen
    structural alternatives F hne g hgP hgH
  have hn := source_large_terminal_not_solvable d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hind := terminal_component_normalizer_index_le_two d.qtke F (by decide) C hC
  have ha := hyp.constituent_homogeneous_faithful_selfDual_of_point_mem hn hC hm P
    ((normal_subgroupOf_iff_le_normalizer hXP).mp hN) hind hI hv
  exact ⟨ha.1,ha.2.1,hyp.constituent_sameModule_of_point_mem hn hC hm P
    ((normal_subgroupOf_iff_le_normalizer hXP).mp hN) hind hI hv⟩

include classification

private theorem higher_stable_orthogonal
    (hd : 2 * finrank (ZMod 2) I < finrank (ZMod 2) (Additive F.Uhat))
    (x : F.terminalDot (F.X g)) :
    ∃ J : Submodule (ZMod 2) (Additive F.Uhat),
      IsIrrPlus F.terminalRepresentation (componentOrbit C ⊤) J ∧
      v ∉ J ∧ J ≤ B.orthogonal I ∧
      (x : F.TerminalHdot) ∈ subspaceStabilizer F.terminalRepresentation J := by
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  let : Group.IsPerfect H := hC.orbit_isPerfect ⊤
  let : Nontrivial H := H.nontrivial_iff_ne_bot.mpr hC.componentOrbit_top_ne_bot
  have hn := source_large_terminal_not_solvable d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hi := hyp.irreducible_of_not_solvable hn
  let R := invariantSubspace F.terminalRepresentation H I hI.choose
  let : IsIrreducible R.toRepresentation := hI.irreducible_of_normal_restriction _ hi H
  let : IsSemisimpleModule (ZMod 2)[H]
      (Representation.asModule (F.terminalRepresentation.comp H.subtype)) :=
    NormalConstituentDisplacement.restriction_semisimple F.terminalRepresentation hi H
  obtain ⟨hh,hfaith,hsame⟩ := higher_homogeneous_data d earlier hq chosen structural alternatives
    F hne hZ hlarge g hgP hgH hyp hC hm hI hv
  have hxx : (x : F.TerminalHdot) * x = 1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) (x : F.TerminalHdot) x.property
  obtain ⟨J,hJ,hdis,hperp,hxJ⟩ := exists_stable_orthogonal_simple
    F.terminalRepresentation H R hsame B hyp.preserves hyp.alternating hyp.nondegenerate
    (source_large_point_constituent_isotropic d earlier hq chosen structural alternatives
      classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv) x hxx
    (hyp.stabilizes_constituent_of_point_mem hi H hI hv x.property) hd
  have hJs : H ≤ subspaceStabilizer F.terminalRepresentation J.toSubmodule := by
    apply le_subspaceStabilizer
    exact fun h hh w hw => J.apply_mem_toSubmodule ⟨h,hh⟩ hw
  have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible F.terminalRepresentation
    hyp.faithful hi H hC.componentOrbit_top_ne_bot
  have hnfix : ¬ J.toSubmodule ≤ fixedSpace F.terminalRepresentation H := by
    intro he
    apply ((Subrepresentation.irreducible_iff_isAtom J).mp hJ).ne_bot
    apply Subrepresentation.toSubmodule_injective
    exact le_bot_iff.mp (he.trans_eq hfix)
  obtain ⟨K,hKJ,hK⟩ := exists_isIrrPlus_le_of_not_fixed F.terminalRepresentation H
    J.toSubmodule hJs hnfix
  let S : Subrepresentation (F.terminalRepresentation.comp H.subtype) :=
    ⟨K,fun h w hw => (hK.choose h.property w).mpr hw⟩
  have hSJ : S = J := ((Subrepresentation.irreducible_iff_isAtom J).mp hJ).le_iff_eq
    (fun hb => hK.ne_bot F.terminalRepresentation (congrArg Subrepresentation.toSubmodule hb)) |>.mp hKJ
  have hJI : IsIrrPlus F.terminalRepresentation H J.toSubmodule :=
    (congrArg Subrepresentation.toSubmodule hSJ) ▸ hK
  have hvJ : v ∉ J.toSubmodule := fun hvJ => hyp.point_ne_zero
    ((Submodule.disjoint_def.mp hdis) v hv hvJ)
  exact ⟨J.toSubmodule,hJI,hvJ,hperp,hxJ⟩

/-- Higher multiplicity forces the original marked constituent to be a
natural alternating module, with the component orbit and action identified. -/
private theorem source_large_marked_higher_natural_model
    (hd : 2 * finrank (ZMod 2) I < finrank (ZMod 2) (Additive F.Uhat)) :
    ∃ n, 5 ≤ n ∧ n ≤ 8 ∧
      ChapterG.Section09.Quasiequivalent
        (invariantSubspace F.terminalRepresentation (componentOrbit C ⊤) I hI.choose).toRepresentation
        (BinaryPermutation.alternatingNaturalRepresentation (Fin n)) := by
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  let : Group.IsPerfect H := hC.orbit_isPerfect ⊤
  let : Nontrivial H := H.nontrivial_iff_ne_bot.mpr hC.componentOrbit_top_ne_bot
  have hn := source_large_terminal_not_solvable d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hi := hyp.irreducible_of_not_solvable hn
  obtain ⟨_,hfaith,hsame⟩ := higher_homogeneous_data d earlier hq chosen structural alternatives
    F hne hZ hlarge g hgP hgH hyp hC hm hI hv
  have hnon : ¬ F.terminalDot (F.X g) ≤ centralizer (H : Set F.TerminalHdot) := by
    intro he
    apply hm
    rw [commutator_comm,commutator_eq_bot_iff_le_centralizer]
    exact (centralizer_le (le_componentOrbit C ⊤)).trans' he
  obtain ⟨x,hx,hxc⟩ := SetLike.not_le_iff_exists.mp hnon
  let a : F.terminalDot (F.X g) := ⟨x,hx⟩
  obtain ⟨J,hJ,hvJ,hperp,hxJ⟩ := higher_stable_orthogonal d earlier hq chosen structural alternatives
    classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv hd a
  let Q := invariantSubspace F.terminalRepresentation H J hJ.choose
  have hiQ : IsIrreducible Q.toRepresentation := hJ.irreducible_of_normal_restriction _ hi H
  obtain ⟨f,hf⟩ := hsame Q hiQ
  have hfQ : Function.Injective Q.toRepresentation := by
    intro b c he
    apply hfaith
    apply LinearMap.ext
    intro w
    apply f.injective
    exact (hf b w).trans ((LinearMap.congr_fun he (f w)).trans (hf c w).symm)
  have hr := orthogonal_rank_one hyp hi H hJ hv hvJ hperp hfQ a hxJ hxc
  have hdual := constituent_selfDual_of_sameModule F.terminalRepresentation H hi B hyp.preserves
    hyp.nondegenerate hJ (fun K hK => (hsame Q hiQ).symm.trans (hsame K hK))
  obtain ⟨n,hn5,hn8,_,e,c,hc⟩ := ChapterG.Section11.normal_constituent_natural_model
    F.terminalRepresentation H (zpowers x) J hJ.choose (zpowers_le.mpr hxJ)
    hiQ hfQ (by have he := hJ.finrank_gt_two F.terminalRepresentation H; omega)
    hdual (source_terminal_cover F d chosen) ⟨x,mem_zpowers _⟩
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx) hr
  exact ⟨n,hn5,hn8,e,f.trans c,fun b w => by change c (f (_)) = _; rw [hf,hc]; rfl⟩

/-- Every original marked constituent occurs exactly twice. Higher
multiplicity contradicts the scalar Schur and automorphism-rank bounds of
its forced natural alternating model. This holds under both G.11 clauses. -/
theorem source_large_marked_double :
    let R := invariantSubspace F.terminalRepresentation (componentOrbit C ⊤) I hI.choose
    finrank (ZMod 2) (Additive F.Uhat) = 2 * finrank (ZMod 2) I ∧
      Nonempty (Representation.Equiv (F.terminalRepresentation.comp (componentOrbit C ⊤).subtype)
        (R.toRepresentation.prod R.toRepresentation)) := by
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  let R := invariantSubspace F.terminalRepresentation H I hI.choose
  have hn := source_large_terminal_not_solvable d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hi := hyp.irreducible_of_not_solvable hn
  have hiR := hI.irreducible_of_normal_restriction _ hi H
  have hh := (higher_homogeneous_data d earlier hq chosen structural alternatives
    F hne hZ hlarge g hgP hgH hyp hC hm hI hv).1
  have hiso := source_large_point_constituent_isotropic d earlier hq chosen structural alternatives
    classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv
  have hl := B.twice_finrank_le_of_isotropic hyp.nondegenerate I hiso
  have hp : I ≠ ⊤ := by
    intro he
    exact hyp.point_ne_zero (hyp.nondegenerate.1 v
      (fun w => hiso v hv w (he.symm ▸ Submodule.mem_top)))
  have hu : finrank (ZMod 2) (Additive F.Uhat) ≤ 2 * finrank (ZMod 2) I := by
    by_contra hu
    obtain ⟨n,hn5,hn8,hmodel⟩ := source_large_marked_higher_natural_model d earlier hq chosen
      structural alternatives classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv (by omega)
    have hg := natural_schur_rank_gap R.toRepresentation n hn5 hn8 hmodel
    have hr := source_large_marked_actor_schur_bound d earlier hq chosen structural alternatives
      F hne hZ hlarge g hgP hgH hyp hC hm hI hv
    have hq := (Group.rank_le_of_surjective
      (QuotientGroup.mk' ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
      (QuotientGroup.mk'_surjective _)).trans
        (IsElementaryAbelian.rank_le_finrank (p := 2) (F.terminalDot (F.X g)))
    have hd := hyp.dimension_bound.1
    have hlt : finrank (ZMod 2) (Additive F.Uhat) < 3 * finrank (ZMod 2) I := by
      change 2 * (finrank (ZMod 2) (IntertwiningMap R.toRepresentation R.toRepresentation) +
        primeRank 2 (MulAut H) + 1) < 3 * finrank (ZMod 2) I at hg
      change finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ≤
        finrank (ZMod 2) (IntertwiningMap R.toRepresentation R.toRepresentation) +
        primeRank 2 (MulAut H) at hr
      omega
    exact hu (Homogeneous.degree_le_double_of_lt_triple R hiR hh hp hlt)
  exact ⟨by omega,Homogeneous.double_coordinates_of_degree_le R hiR hh hp hu⟩

/-- In the original fixed-line branch, a nontrivial actor centralizer has
order two, and its literal quotient has degree one less than the actor.
The multiplicity premise of the preceding kernel theorem is discharged. -/
theorem source_large_marked_nontrivial_kernel
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)))
    (hk : (centralizer (componentOrbit C ⊤ : Set F.TerminalHdot)).subgroupOf
      (F.terminalDot (F.X g)) ≠ ⊥) :
    let Y := (centralizer (componentOrbit C ⊤ : Set F.TerminalHdot)).subgroupOf
      (F.terminalDot (F.X g))
    Nat.card Y = 2 ∧
      finrank (ZMod 2) I = finrank (ZMod 2) (Additive ((F.terminalDot (F.X g)) ⧸ Y)) + 2 := by
  exact source_large_marked_double_kernel d earlier hq chosen structural alternatives classification
    F hne hZ hlarge g hgP hgH hyp hC hm hI hv hline hn
    (source_large_marked_double d earlier hq chosen structural alternatives classification
      F hne hZ hlarge g hgP hgH hyp hC hm hI hv).1 hk

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
