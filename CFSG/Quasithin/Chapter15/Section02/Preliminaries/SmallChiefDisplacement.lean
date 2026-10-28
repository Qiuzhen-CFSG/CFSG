module
public import Theory.GroupAction.NormalPChiefSeries.CommutatorBound
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2CoverBounds
public import CFSG.Quasithin.ChapterC.Section01.LocalCoreDisplacement
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.MarkedFiveWreathExclusion.ComponentActions
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.TwoChiefQuotientExclusions.FiveResidual

/-!
# The actual small-parabolic commutator layers are not natural blocks

Both original noncentral chief factors contribute a natural A₅ four-space
to [U_H,K]. Their distinct intervals in the same filtration give order
at least 256 for this commutator. Subnormal two-perfect action places it
inside the literal [O₂(K),K], so that layer also has order at least 256.

This excludes both natural four-dimensional block types: the L₂(4) block
has commutator layer of order at most 64, retaining its possible central
covering kernel, and the A₅ block has commutator layer of order 16.
The two applications use the embedded O²(H) in the single-S₅ branch and
the original C-component K in the wreath-five branch. The F.1.1 consumer
keeps Y₁Rc, the full second parabolic H, and the original Sylow T.

These are exclusions of specific source alternatives, not recognition of
the whole pair. The remaining mixed-pair, centered quintic and quotient
exclusions remain with qt-e-152-small-parabolic. No survival of either
chief factor through W/O₂(W) is asserted.

Source: Aschbacher--Smith 15.1.12, 15.2.4 and 15.2.8, printed pp.1090,
1105--1110; F.1.12(I)(1),(2),(6), pp.262--263; C.1.7 and C.1.12,
pp.123--124; I.1.6, p.408, for the natural L₂ central-cover bound.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
open NoncentralChiefRefinement ChapterB.QuasisimpleSource ChapterC

private theorem irreducible_moved_top
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (hi : IsIrreducible ρ)
    (hm : ∃ g v, ρ g v ≠ v) : subspaceCommutator ρ ⊤ ⊤ = ⊤ := by
  let A := subspaceCommutator ρ ⊤ ⊤
  have hs : (⊤ : Subgroup D) ≤ subspaceStabilizer ρ A :=
    subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by intros; trivial))
      (by rw [normalizer_eq_top])
  let J : Subrepresentation ρ := ⟨A, fun g v hv => (hs (mem_top g) v).2 hv⟩
  rcases hi.eq_bot_or_eq_top J with hb | ht
  · have hz : A = ⊥ := congrArg Subrepresentation.toSubmodule hb
    obtain ⟨g,v,hv⟩ := hm
    have hd : ρ g v - v ∈ A := Submodule.subset_span ⟨g,mem_top _,v,Submodule.mem_top,rfl⟩
    rw [hz,Submodule.mem_bot] at hd
    exact (hv (sub_eq_zero.mp hd)).elim
  · exact congrArg Subrepresentation.toSubmodule ht

private theorem perfect_twoPerfect {D : Type*} [Group D] [Finite D]
    [Group.IsPerfect D] : IsPPerfect 2 D := by
  intro N hN hp
  let := hN
  have hs : Subsingleton (D ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (D ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

private theorem blockU_card_congr {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) : Nat.card (blockU A) = Nat.card (blockU B) := by
  have hm : (blockU A).map e.toMonoidHom = blockU B := by
    rw [blockU,map_commutator,pCore_map_iso,map_top_of_surjective _ e.surjective,blockU]
  rw [←hm,card_map_of_injective e.injective]

private theorem no_small_natural_blocks {D : Type*} [Group D]
    (hc : 256 ≤ Nat.card (blockU D)) :
    ¬ IsL2EvenBlock D 2 ∧ ¬ IsAlternatingBlock D 5 := by
  constructor
  · intro h
    have hfixed := h.fixed_card_le
    have hcard := (blockFixed D).card_eq_card_quotient_mul_card_subgroup
    have hmodule := h.module_card
    change Nat.card (blockU D ⧸ blockFixed D) = 2 ^ (2 * 2) at hmodule
    rw [hmodule] at hcard
    norm_num at hfixed hcard
    omega
  · intro h
    have hh := h.blockU_card
    omega

variable {G : Type*} [Group G] [Finite G]

/-- Both literal S₅ chief factors contribute to the actual commutator with
O²(H), and hence to its intrinsic core commutator layer. -/
theorem ChosenSmallSource.symmetricFive_residual_displacement
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hprior : SmallSourcePrior T M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5))) :
    let K := (pResidual 2 H).map H.subtype
    256 ≤ Nat.card (⁅conjugateSpan H V,K⁆ : Subgroup G) ∧
      256 ≤ Nat.card (blockU K) := by
  classical
  let := h.prepared.elementary
  let U := (conjugateSpan H V).subgroupOf H
  let R := pResidual 2 H
  have hUH : conjugateSpan H V ≤ H := by
    rw [UniqueFactor.conjugateSpan_eq]
    exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H))
  let := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hUH
  obtain ⟨s⟩ := SeriesOn.exists_series U
  obtain ⟨i,j,hij,hs⟩ := h.symmetricFive_residual_chief_actions hprior hH he s
  have moved (k : Fin s.series.length) (hk : k ∈ ({i,j} : Finset (Fin s.series.length))) :
      Nat.card (subspaceCommutator ((s.factorRepresentation k).comp R.subtype) ⊤ ⊤) = 16 := by
    obtain ⟨_,_,_,_,hker,hi,q,c,hq,hqk,_⟩ := hs k hk
    let ρ := (s.factorRepresentation k).comp R.subtype
    have hn : ∃ g v, ρ g v ≠ v := by
      by_contra! hz
      have hqone (g : R) : q g = 1 := by
        apply MonoidHom.mem_ker.mp
        rw [hqk,←hker,MonoidHom.mem_ker,actionHom_eq_one_iff]
        exact hz g
      obtain ⟨a,ha⟩ := exists_ne (1 : alternatingGroup (Fin 5))
      obtain ⟨g,rfl⟩ := hq a
      exact ha (hqone g)
    rw [irreducible_moved_top ρ hi hn,Module.natCard_eq_pow_finrank (K := ZMod 2),
      finrank_top,c.finrank_eq,
      BinaryPermutation.finrank_natural_odd (Fin 5) (by decide)]
    norm_num
  have hb := s.two_moved_cards_le_commutator R i j hij
  rw [moved i (by simp),moved j (by simp),commutator_comm R U] at hb
  have hbound : 256 ≤ Nat.card (blockU R) := by
    have hl := commutator_le_core_commutator_of_isSubnormal R U
      (inferInstance : R.Normal).isSubnormal (isPPerfect_pResidual 2)
      (IsElementaryAbelian.isPGroup 2 U) le_normalizer_of_normal
    have hc := hb.trans (card_le_of_le hl)
    rw [card_map_of_injective R.subtype_injective] at hc
    exact hc
  refine ⟨?_,?_⟩
  · have hm : (⁅U,R⁆ : Subgroup H).map H.subtype =
        ⁅conjugateSpan H V,R.map H.subtype⁆ := by
      rw [map_commutator,map_subgroupOf_eq_of_le hUH]
    rwa [←hm,card_map_of_injective H.subtype_injective]
  · rw [←blockU_card_congr (equivMapOfInjective R H.subtype H.subtype_injective)]
    exact hbound

/-- The literal rank-one residual in the S₅ pair cannot be either natural
four-dimensional block occurring in F.1.12. -/
theorem ChosenSmallSource.symmetricFive_residual_not_blocks
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hprior : SmallSourcePrior T M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5))) :
    let K := (pResidual 2 H).map H.subtype
    ¬ IsL2EvenBlock K 2 ∧ ¬ IsAlternatingBlock K 5 :=
  no_small_natural_blocks (h.symmetricFive_residual_displacement hprior hH he).2

/-- The two original paired factors contribute to the commutator with the
same actual component K in the wreath-five source configuration. -/
theorem ChosenSmallSource.marked_five_wreath_component_displacement
    {T : Sylow 2 G} {M Mc V H K : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2))))
    (hK : K ∈ Chapter1.cComponentsIn H) :
    letI := h.prepared.elementary
    ∀ (l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
      (Jhat (imageRepresentation M V h.prepared.normalized)).subtype)),
    DihedralMarking l 5 2 →
      256 ≤ Nat.card (⁅conjugateSpan H V,K⁆ : Subgroup G) ∧
      256 ≤ Nat.card (blockU K) := by
  classical
  let := h.prepared.elementary
  intro l hd
  let U := (conjugateSpan H V).subgroupOf H
  let R := K.subgroupOf H
  have hUH : conjugateSpan H V ≤ H := by
    rw [UniqueFactor.conjugateSpan_eq]
    exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H))
  let := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hUH
  obtain ⟨s⟩ := SeriesOn.exists_series U
  obtain ⟨i,j,hij,hs⟩ := h.marked_five_wreath_component_chief_actions hH he hK l hd s
  obtain ⟨_,_,q₀,a₀,_,_,_,_,_,hi⟩ := hs i (by simp)
  obtain ⟨_,_,q₁,a₁,_,_,_,_,_,hj⟩ := hs j (by simp)
  have hb := s.two_moved_cards_le_commutator R i j hij
  rw [hi,hj,commutator_comm R U] at hb
  have hbound : 256 ≤ Nat.card (blockU R) := by
    let : Group.IsPerfect R := hK.2.perfect
    have hl := commutator_le_core_commutator_of_isSubnormal R U hK.2.subnormal
      perfect_twoPerfect (IsElementaryAbelian.isPGroup 2 U) le_normalizer_of_normal
    have hc := hb.trans (card_le_of_le hl)
    rw [card_map_of_injective R.subtype_injective] at hc
    exact hc
  refine ⟨?_,?_⟩
  · have hm : (⁅U,R⁆ : Subgroup H).map H.subtype = ⁅conjugateSpan H V,K⁆ := by
      rw [map_commutator,map_subgroupOf_eq_of_le hUH,map_subgroupOf_eq_of_le hK.1]
    rwa [←hm,card_map_of_injective H.subtype_injective]
  · rw [←blockU_card_congr (subgroupOfEquivOfLe hK.1)]
    exact hbound

/-- Neither natural rank-one block can be the original wreath component,
before either of the source's generated-core cases is chosen. -/
theorem ChosenSmallSource.marked_five_wreath_component_not_blocks
    {T : Sylow 2 G} {M Mc V H K : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2))))
    (hK : K ∈ Chapter1.cComponentsIn H) :
    letI := h.prepared.elementary
    ∀ (l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
      (Jhat (imageRepresentation M V h.prepared.normalized)).subtype)),
      DihedralMarking l 5 2 → ¬ IsL2EvenBlock K 2 ∧ ¬ IsAlternatingBlock K 5 := by
  let := h.prepared.elementary
  intro l hd
  exact no_small_natural_blocks (h.marked_five_wreath_component_displacement hH he hK l hd).2

/-- The original F.1.1 application retains its actual second parabolic H
and rules out both natural four-dimensional block structures on O²(H).
The first factor remains Y₁Rc and need not contain T. -/
theorem SmallResidualWitness.symmetricFive_pair_nonblock
    {T : Sylow 2 G} {M Mc V Y₁ H : Subgroup G} {h : ChosenSmallSource T M Mc V}
    (hw : SmallResidualWitness h Y₁) (hprior : SmallSourcePrior T M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5))) :
    let K := (pResidual 2 H).map H.subtype
    let L := ![Y₁ ⊔ (M ⊓ Mc).pCoreIn 2,K]
    ChapterF.Source.HypothesisF11 L (T : Subgroup G) ∧
      ChapterF.Source.parabolic L (T : Subgroup G) 1 = H ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) ∧
      256 ≤ Nat.card (⁅conjugateSpan H V,K⁆ : Subgroup G) ∧
      256 ≤ Nat.card (blockU K) ∧
      ¬ IsL2EvenBlock K 2 ∧ ¬ IsAlternatingBlock K 5 := by
  have hp := hw.symmetricFive_pair hH he
  have hd := h.symmetricFive_residual_displacement hprior hH he
  exact ⟨hp.1,hp.2.2.1,hp.2.2.2.2.2,hd.1,hd.2,no_small_natural_blocks hd.2⟩

end CFSG.Quasithin.Chapter15.Section02
