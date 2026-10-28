module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Decomposable.ResidualGeometry
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Exchange
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.DecomposableTwoRank

/-!
# Sylow geometry of the original cubic decomposable marking

In the prime-three branch, the literal support action has order not divisible
by four. The binary symmetric-three normalizer alternatives prove this from
the original local hypotheses: the support has trivial two-core, and a
symmetric-three pair on one support contradicts the independent other factor.

Consequently the Sylow support action has order two. Its Thompson subgroup
already acts nontrivially, since its fixed four-group is smaller than the
sixteen-element support. Thus the support stabilizer centralizes the marking.
This identifies the literal C_T(Z₁), proves its normality and both required
indices, and supplies the exchanged-plane geometry on the original full
centralizer residual. All quotient and restriction maps are the actual ones.

The parent Decomposable module applies the result to the original
eight-dimensional action and retains the same prime-five alternative.
Residual order, marker generation, and the prime-five source argument remain
necessary for pre-exclusion component selection.

Source: Aschbacher--Smith 15.1.16(a), 15.1.18(3), and 15.1.25,
printed pp.1092--1093 and 1102.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.DecomposableMarker
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition
open Stellmacher Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

private theorem not_symmetricThree_times_two_of_twoCore {D : Type*} [Group D] [Finite D]
    (hcore : pCore 2 D = ⊥)
    (e : D ≃* (Equiv.Perm (Fin 3) × Multiplicative (ZMod 2))) : False := by
  have he : pCore 2 (Equiv.Perm (Fin 3) × Multiplicative (ZMod 2)) = ⊥ := by
    rw [←pCore_map_iso 2 e,hcore,Subgroup.map_bot]
  have htwo : IsPGroup 2 (Multiplicative (ZMod 2)) := IsPGroup.of_card (n := 1) (by simp)
  have hx : (1,Multiplicative.ofAdd (1 : ZMod 2)) ∈
      pCore 2 (Equiv.Perm (Fin 3) × Multiplicative (ZMod 2)) := by
    rw [pCore_prod]
    exact ⟨one_mem _, (le_sSup ⟨inferInstance, htwo.of_equiv (Subgroup.topEquiv).symm⟩ :
      (⊤ : Subgroup (Multiplicative (ZMod 2))) ≤ pCore 2 _) (mem_top _)⟩
  rw [he] at hx
  have hh := congrArg (fun a : Equiv.Perm (Fin 3) × Multiplicative (ZMod 2) => a.2.toAdd)
    (mem_bot.mp hx)
  norm_num at hh

/-- The actual prime-three support has Sylow subgroups of order two.
The two-core and factor-count exclusions come from the source local action. -/
theorem ThompsonPair.support_four_not_dvd_of_prime_three
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V : Subgroup G} [IsElementaryAbelian 2 V] (hM : IsOrderingMaximal T M)
    (hfull : V = localModule T M) (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (hd : d.FittingFull)
    (s : ThompsonPair (T := T) hn c d)
    (π : internalActionImage M V hn →* Equiv.Perm d.Index)
    (hp : ∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g k)).actor)
    (hs : ∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V hn g) =
      (c.ambientFactor d (π g k)).space)
    (hthree : s.prime = 3) (i : d.Index) :
    ¬ 4 ∣ Nat.card (subspaceActionImage (imageRepresentation M V hn)
      (c.ambientFactor d i).space) := by
  subst V
  let ρ := imageRepresentation M (localModule T M) hn
  have he : ∀ k : d.Index, Nonempty ((d.factor k).Carrier ≃* Equiv.Perm (Fin 3)) := by
    intro k
    have hm := (s.dihedral k).dihedral
    rw [hthree] at hm
    exact ⟨hm.some.trans nonempty_dihedralThreeEquivPerm.some⟩
  let F := c.ambientFactor d i
  obtain ⟨k,J,hk,_,_,hnk,hfull⟩ := F.faithful_normal_support_image_data
    (c.support_stabilizer_normalizes_actor d π hp hs i)
  let : k.range.Normal := hnk
  let : FiniteDimensional (ZMod 2) F.space := Module.Finite.of_surjective J.toLinearMap J.surjective
  let σ := subspaceImageRepresentation ρ F.space
  let e := (MonoidHom.ofInjective hk).symm.trans (he i).some
  have hmove : subspaceCommutator (σ.comp k.range.subtype) ⊤ ⊤ = ⊤ := by
    rw [subspaceCommutator_comp_map,←MonoidHom.range_eq_map,k.range.range_subtype]
    exact hfull
  let τ := σ.comp (k.range.subtype.comp e.symm.toMonoidHom)
  have hτ : subspaceCommutator τ ⊤ ⊤ = ⊤ := by
    change subspaceCommutator ((σ.comp k.range.subtype).comp e.symm.toMonoidHom) ⊤ ⊤ = ⊤
    rw [subspaceCommutator_comp_map,map_top_of_surjective _ e.symm.surjective]
    exact hmove
  intro hfour
  rcases Representation.BinarySymmetricThreeNormalizer.normal_symmetricThree_cases σ
      (subspaceImageRepresentation_injective ρ F.space)
      (J.finrank_eq.symm.trans (s.dihedral i).dimension)
      k.range e (Representation.BinarySymmetricThreeNormalizer.fixedFree_of_full τ hτ) hfour
    with ⟨esmall⟩ | ⟨epair⟩
  · exact not_symmetricThree_times_two_of_twoCore
      (source_localAction_symmetricThree_support_twoCore hG T hM U c d hd π hp hs he i) esmall.some
  · have hsingle := source_localAction_symmetricThree_pair_image_singleton
      hG T hM U c d π hp hs he i epair.some
    exact s.distinct ((hsingle s.first).trans (hsingle s.second).symm)

/-- A support action with no factor of four identifies the actual marked
Sylow centralizer and proves normality, both indices, and exchange. -/
theorem ThompsonPair.sylow_geometry_of_support_four_not_dvd
    {T : Sylow 2 G} {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T := T) hn c d)
    (hfour : ¬ 4 ∣ Nat.card (subspaceActionImage (imageRepresentation M V hn)
      (c.ambientFactor d s.first).space)) :
    let A := plane V (c.ambientFactor d s.first).space
    let B := plane V (c.ambientFactor d s.second).space
    let Z := thompsonPlane T V (c.ambientFactor d s.first).space
    let S := (T : Subgroup G) ⊓ centralizer (Z : Set G)
    S = (T : Subgroup G) ⊓ normalizer (A : Set G) ∧
      S.relIndex (T : Subgroup G) = 2 ∧
      (S.subgroupOf (T : Subgroup G)).Normal ∧
      S ≤ normalizer (A : Set G) ∧ S ≤ normalizer (B : Set G) ∧
      (centralizer (A : Set G)).relIndex S = 2 ∧
      ∀ t ∈ (T : Subgroup G), t ∉ S →
        A.map (MulAut.conj t).toMonoidHom = B ∧
        B.map (MulAut.conj t).toMonoidHom = A := by
  let ρ := imageRepresentation M V hn
  let W := (c.ambientFactor d s.first).space
  let A := plane V W
  let Z := thompsonPlane T V W
  let N := (T : Subgroup G) ⊓ normalizer (A : Set G)
  let J := ChapterB.thompsonJ (T : Subgroup G) 1
  let f := (actionHom M V hn).rangeRestrict
  have hNM : N ≤ M := inf_le_left.trans hTM
  have hJN : J ≤ N := by
    intro j hj
    have hjT : j ∈ (T : Subgroup G) := ChapterB.thompsonJ_le _ _ hj
    have hjZ : j ∈ centralizer (Z : Set G) := fun z hz => (hz.2.2 j hj).symm
    exact ⟨hjT,s.centralizer_le_stabilizer ⟨hjT,hjZ⟩⟩
  have hstab (n : N) : f ⟨n,hNM n.property⟩ ∈ subspaceStabilizer ρ W := by
    apply (subspace_map_eq_iff ρ W _).mp
    apply (plane_injective V)
    exact (plane_conjugate hn W ⟨n,hNM n.property⟩).symm.trans
      (mem_normalizer_iff_map_conj_eq.mp n.property.2)
  let a : N →* subspaceStabilizer ρ W :=
    (f.comp (inclusion hNM)).codRestrict (subspaceStabilizer ρ W) hstab
  let g := (subspaceActionHom ρ W).comp a
  have hg (n : N) : g n = 1 ↔ (n : G) ∈ centralizer (A : Set G) := by
    refine Iff.trans ?_ (ExtraspecialMarker.image_mem_kernel_iff M V hn W ⟨n,hNM n.property⟩)
    constructor
    · intro he
      refine ⟨mem_top _,fun w hw => ?_⟩
      exact congrArg (fun b => (subspaceImageRepresentation ρ W b ⟨w,hw⟩ : Additive V)) he
    · intro he
      apply subspaceImageRepresentation_injective ρ W
      apply LinearMap.ext
      intro w
      apply Subtype.ext
      exact he.2 w w.property
  have hgp : IsPGroup 2 g.range :=
    (T.isPGroup'.to_le (show N ≤ (T : Subgroup G) from inf_le_left)).of_surjective
      g.rangeRestrict g.rangeRestrict_surjective
  have hgc : Nat.card g.range ≤ 2 := by
    obtain ⟨k,hk⟩ := hgp.exists_card_eq
    have hk2 : k < 2 := by
      by_contra! hh
      apply hfour
      exact (show 4 ∣ Nat.card g.range from hk ▸ Nat.pow_dvd_pow 2 hh).trans
        (card_subgroup_dvd_card _)
    interval_cases k <;> simp_all
  let H := (J.subgroupOf N).map g
  have hH : H ≤ g.range := map_le_range _ _
  have hHne : H ≠ ⊥ := by
    intro hb
    have hAJ : A ≤ thompsonFixed T V := by
      intro w hw
      refine ⟨plane_le W hw,?_⟩
      intro j hj
      have hjH : g ⟨j,hJN hj⟩ ∈ H := mem_map_of_mem g hj
      rw [hb,mem_bot] at hjH
      exact ((hg ⟨j,hJN hj⟩).mp hjH w hw).symm
    have hZA : Z = A := inf_eq_left.mpr hAJ
    have hz := s.thompson_card s.first
    have ha := s.support_card s.first
    change Nat.card Z = 4 at hz
    change Nat.card A = 16 at ha
    rw [hZA,ha] at hz
    omega
  have hHc : 2 ≤ Nat.card H := H.one_lt_card_iff_ne_bot.mpr hHne
  have hHeq : H = g.range := eq_of_le_of_card_ge hH (hgc.trans hHc)
  have hgc2 : Nat.card g.range = 2 := by
    have hb := card_le_of_le hH
    omega
  have hNZ : N ≤ centralizer (Z : Set G) := by
    intro n hnN z hz
    have hnH : g ⟨n,hnN⟩ ∈ H := hHeq.symm ▸ (show g ⟨n,hnN⟩ ∈ g.range from ⟨⟨n,hnN⟩,rfl⟩)
    obtain ⟨j,hj,he⟩ := hnH
    obtain ⟨w,hw,hwz⟩ := hz.1
    have hew := congrArg (fun b =>
      (subspaceImageRepresentation ρ W b ⟨Additive.ofMul w,hw⟩ : Additive V)) he
    have heG := congrArg (fun v : Additive V => (v.toMul : G)) hew
    change (j : G) * (w : G) * (j : G)⁻¹ = n * (w : G) * n⁻¹ at heG
    have hjz : (j : G) * z = z * j := hz.2.2 j hj
    change (w : G) = z at hwz
    rw [hwz] at heG
    rw [hjz,mul_inv_cancel_right] at heG
    exact (mul_inv_eq_iff_eq_mul.mp heG.symm).symm
  have he : (T : Subgroup G) ⊓ centralizer (Z : Set G) = N :=
    le_antisymm (le_inf inf_le_left s.centralizer_le_stabilizer)
      (le_inf inf_le_left hNZ)
  have hi : (centralizer (A : Set G)).relIndex N = 2 := by
    have hker : g.ker = (centralizer (A : Set G)).subgroupOf N := by
      ext n
      exact hg n
    change ((centralizer (A : Set G)).subgroupOf N).index = 2
    rw [←hker,index_ker,hgc2]
  dsimp only
  change _ = N ∧ _
  refine ⟨he,?_,?_,?_,?_,?_,?_⟩
  · rw [he]
    exact s.stabilizer_index
  · rw [he]
    exact s.stabilizer_normal
  · rw [he]
    exact inf_le_right
  · rw [he]
    exact s.stabilizes_second
  · rw [he]
    exact hi
  · intro t ht htn
    apply s.exchanges t ht
    intro htA
    exact htn (he.symm ▸ (show t ∈ N from ⟨ht,htA⟩))

/-- Apply the Sylow calculation to the same marked component and its literal
full residual, yielding every clause of the exchanged-plane geometry. -/
theorem ThompsonPair.exchangedPlaneGeometry_of_support_four_not_dvd
    {T : Sylow 2 G} {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T := T) hn c d)
    (π : internalActionImage M V hn →* Equiv.Perm d.Index)
    (hp : ∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g k)).actor)
    (hs : ∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V hn g) =
      (c.ambientFactor d (π g k)).space)
    (hJ : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict =
      ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict ⊓
        Jhat (imageRepresentation M V hn))
    (hfour : ¬ 4 ∣ Nat.card (subspaceActionImage (imageRepresentation M V hn)
      (c.ambientFactor d s.first).space))
    (e : CaseIComponentData T M Mc V)
    (hZ : e.Z1 = thompsonPlane T V (c.ambientFactor d s.first).space)
    (hrow : e.row = .six) : e.ExchangedPlaneGeometry := by
  obtain ⟨hf,hm,hcf,hcm⟩ := s.full_residual_geometry hTM hn c d π hp hs hJ
  have hF : e.nineFixedPlane = plane V (c.ambientFactor d s.first).space :=
    (congrArg (fun Z : Subgroup G => V ⊓ centralizer
      ((pResidual 2 (M ⊓ centralizer (Z : Set G) : Subgroup G)).map
        (M ⊓ centralizer (Z : Set G)).subtype : Set G)) hZ).trans hf
  have hB : e.nineMovingPlane = plane V (c.ambientFactor d s.second).space :=
    (congrArg (fun Z : Subgroup G => ⁅V,
      (pResidual 2 (M ⊓ centralizer (Z : Set G) : Subgroup G)).map
        (M ⊓ centralizer (Z : Set G)).subtype⁆) hZ).trans hm
  have hS : e.S = (T : Subgroup G) ⊓ centralizer
      (thompsonPlane T V (c.ambientFactor d s.first).space : Set G) :=
    congrArg (fun Z : Subgroup G => (T : Subgroup G) ⊓ centralizer (Z : Set G)) hZ
  obtain ⟨_,hi,_,hnA,hnB,hci,hex⟩ :=
    s.sylow_geometry_of_support_four_not_dvd hTM hn c d hfour
  refine {
    sizes := Or.inr ⟨hrow,?_,?_,?_⟩
    planes_sup := ?_
    planes_inf := ?_
    marked_le_fixed := ?_
    index := ?_
    fixes_planes := ?_
    fixed_centralizer_index := ?_
    exchanges := ?_ }
  · rw [hZ]
    exact s.thompson_card s.first
  · rw [hF]
    exact s.support_card s.first
  · rw [hB]
    exact s.support_card s.second
  · rw [hF,hB]
    exact s.complement
  · rw [hF,hB]
    exact s.disjoint
  · rw [hZ,hF]
    exact inf_le_left
  · rw [hS]
    exact hi
  · rw [hS,hF,hB]
    exact ⟨hnA,hnB⟩
  · rw [hS,hF]
    exact hci
  · rw [hS,hF,hB]
    exact hex

end CFSG.Quasithin.Chapter15.Section01.DecomposableMarker
