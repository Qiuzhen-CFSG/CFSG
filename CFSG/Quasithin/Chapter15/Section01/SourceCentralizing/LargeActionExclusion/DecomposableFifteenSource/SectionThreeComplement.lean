module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableFifteenSource.ReducedPartner
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.PreparedThompsonChiefActions
public import Theory.GroupTheory.TwoLayerActionImage
public import Theory.Representation.BinaryOffender.IrreducibleResidual
public import Theory.SpecificGroups.PermutationThreePrimeCore
public import BenderSuzuki.External.Huppert.IV.ComplementTransfer

/-!
# The original partner section detects failure of three-nilpotence

An original H-star subgroup inside the partner has a noncentral chief
factor whose global Thompson image is S3, S3 squared, S5, or S5 squared.
The section kernel fixes the denominator and the quotient, so its image
on that chief factor is a normal two-subgroup and is trivial. The same
small chief image therefore survives as a quotient of a subgroup of the
centralizer image on the literal section. None of the four images has a
normal three-complement.

Source: original 15.1.12(3), with the actual source section retained.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker NoncentralChiefRefinement
variable {G : Type*} [Group G] [Finite G]

private theorem complement_image {B D : Type*} [Group B] [Finite B] [Group D]
    (f : B →* D) (hf : Function.Surjective f) (h : HasNormalPComplement 3 B) :
    HasNormalPComplement 3 D :=
  hasNormalPComplement_of_equiv 3 (QuotientGroup.quotientKerEquivOfSurjective f hf)
    (BenderSuzuki.External.hkt_hasNormalPComplement_to_quotient f.ker h)

private theorem symmetric_three_not_complement :
    ¬ HasNormalPComplement 3 (Equiv.Perm (Fin 3)) := by
  intro h
  have hp := BenderSuzuki.External.hkt_isPGroup_of_hasNormalPComplement_of_pPrimeCore_eq_bot
    Theory.SpecificGroups.symmetricThree_threePrimeCore h
  have hh := hp.orderOf_coprime (show Nat.Coprime 3 2 by decide)
    (Equiv.swap (0 : Fin 3) 1)
  rw [show orderOf (Equiv.swap (0 : Fin 3) 1) = 2 from
    orderOf_eq_prime (by decide) (by decide)] at hh
  norm_num at hh

private theorem symmetric_five_not_complement :
    ¬ HasNormalPComplement 3 (Equiv.Perm (Fin 5)) := by
  intro h
  have hp := BenderSuzuki.External.hkt_isPGroup_of_hasNormalPComplement_of_pPrimeCore_eq_bot
    Theory.SpecificGroups.symmetricFive_threePrimeCore h
  have hh := hp.orderOf_coprime (show Nat.Coprime 3 2 by decide)
    (Equiv.swap (0 : Fin 5) 1)
  rw [show orderOf (Equiv.swap (0 : Fin 5) 1) = 2 from
    orderOf_eq_prime (by decide) (by decide)] at hh
  norm_num at hh

private theorem small_layer_not_complement {D L : Type*} [Group D] [Group L] [Finite L]
    (h : ChapterB.ChiefSmallActorLayerTypes D L) : ¬ HasNormalPComplement 3 L := by
  intro hc
  rcases h with ⟨_,⟨e⟩⟩ | ⟨_,⟨e⟩⟩ | ⟨_,⟨e⟩⟩ | ⟨_,⟨e⟩⟩
  · exact symmetric_three_not_complement (hasNormalPComplement_of_equiv 3 e hc)
  · exact symmetric_three_not_complement (complement_image (MonoidHom.fst _ _)
      (fun x => ⟨(x,1),rfl⟩) (hasNormalPComplement_of_equiv 3 e hc))
  · exact symmetric_five_not_complement (hasNormalPComplement_of_equiv 3 e hc)
  · exact symmetric_five_not_complement (complement_image (MonoidHom.fst _ _)
      (fun x => ⟨(x,1),rfl⟩) (hasNormalPComplement_of_equiv 3 e hc))

private theorem chief_centralizer_le_kernel {X : Type*} [Group X]
    (U : Subgroup X) [U.Normal] [IsElementaryAbelian 2 U]
    (s : SeriesOn U) (i : Fin s.series.length) :
    centralizer (U : Set X) ≤ (Representation.BinaryOffender.actionHom
      (s.factorRepresentation i)).ker := by
  intro x hx
  apply (actionHom_eq_one_iff _ x).mpr
  intro v
  obtain ⟨u,hu⟩ := QuotientGroup.mk'_surjective
    ((s.lower i).val.subgroupOf (s.upper i).val) v.toMul
  change Additive.ofMul (s.action i x v.toMul) = v
  apply Additive.toMul.injective
  change s.action i x v.toMul = v.toMul
  rw [←hu,s.action_mk]
  congr 1
  apply Subtype.ext
  change x * (u : X) * x⁻¹ = (u : X)
  rw [←hx _ (s.upper_le i u.property),mul_assoc,mul_inv_cancel,mul_one]

private theorem chief_kernel_of_two_layer {X : Type*} [Group X] [Finite X]
    (U E K : Subgroup X) [U.Normal] [IsElementaryAbelian 2 U] [K.Normal]
    (he : IsPGroup 2 E) (hc : K ≤ centralizer (E : Set X)) (hd : ⁅K,U⁆ ≤ E)
    (s : SeriesOn U) (i : Fin s.series.length) :
    K ≤ (Representation.BinaryOffender.actionHom (s.factorRepresentation i)).ker := by
  let ρ := s.factorRepresentation i
  let f := Representation.BinaryOffender.actionHom ρ
  let : IsIrreducible ρ := s.factorRepresentation_irreducible i
  have hp := isPGroup_image_of_two_layer K U E he hc hd f
    (chief_centralizer_le_kernel U s i)
  have hm : (K.map f).Normal := Normal.map inferInstance f ρ.asGroupHom.rangeRestrict_surjective
  have hh : K.map f ≤ pCore 2 (actionImage ρ) := le_sSup ⟨hm,hp⟩
  rw [irreducible_image_twoCore_eq_bot ρ] at hh
  exact (map_eq_bot_iff K).mp (bot_unique hh)

private theorem complement_subgroup_image_of_kernel_le
    {X D A : Type*} [Group X] [Finite X] [Group D] [Finite D] [Group A] [Finite A]
    (q : X →* D) (f : X →* A) (hqf : q.ker ≤ f.ker) (J : Subgroup X)
    (hcomp : HasNormalPComplement 3 (J.map q)) :
    HasNormalPComplement 3 (J.map f) := by
  let qJ : J →* J.map q := q.subgroupMap J
  let fJ : J →* J.map f := f.subgroupMap J
  have hk : qJ.ker ≤ fJ.ker := by
    intro x hx
    apply Subtype.ext
    exact hqf (congrArg Subtype.val hx)
  let a : J.map q →* J.map f := qJ.liftOfSurjective (q.subgroupMap_surjective J) ⟨fJ,hk⟩
  have ha : Function.Surjective a := by
    intro y
    obtain ⟨x,rfl⟩ := f.subgroupMap_surjective J y
    exact ⟨qJ x,qJ.liftOfRightInverse_comp_apply _ _ _ x⟩
  exact complement_image a ha hcomp

private theorem source_section_centralizer_not_complement
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V N H E : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V)
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) (hNM : N ≠ M)
    (hVH : V ≤ H) (hNH : N ≤ normalizer (H : Set G))
    (hNE : N ≤ normalizer (E : Set G)) (he : IsPGroup 2 E)
    (hJE : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (E : Set G))
    (hKE : commutatorPreimage N H E ≤ centralizer (E : Set G))
    {D : Type*} [Group D] [Finite D] (q : N →* D)
    (hq : q.ker = (commutatorPreimage N H E).subgroupOf N) :
    ¬ HasNormalPComplement 3 ((centralizer (E : Set G)).subgroupOf N |>.map q) := by
  classical
  let K := commutatorPreimage N H E
  have hNK : N ≤ normalizer (K : Set G) :=
    commutatorPreimage_normalized N H E N hNE N.le_normalizer hNH hNE
  have ho : N ∈ Chapter1.HOver G (T : Set G) ∧ ¬ N ≤ M :=
    ⟨⟨Chapter1.mem_H_of_isTwoLocal hN.1.1,hN.2⟩,
      fun hn => hNM (hN.1.eq_of_le hM.1.1.1 hn)⟩
  obtain ⟨X,hXN,hX⟩ := Finite.exists_le_minimal (p := fun X : Subgroup G =>
    X ∈ Chapter1.HOver G (T : Set G) ∧ ¬ X ≤ M) ho
  have hTX : (T : Subgroup G) ≤ X := hX.1.1.2
  let U := (conjugateSpan X V).subgroupOf X
  have hUX : conjugateSpan X V ≤ X := by
    rw [UniqueFactor.conjugateSpan_eq]
    exact conjugateSpanBy_le_self ((h.inside_core X hX).trans (twoCore_le X))
  have hUH : conjugateSpan X V ≤ H := by
    rw [UniqueFactor.conjugateSpan_eq]
    exact conjugateSpanBy_le hVH (hXN.trans hNH)
  let := h.elementary
  let := (h.chief_data hG T hempty hM hJ X hX).1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hUX
  let s : SeriesOn U := Classical.choice (SeriesOn.exists_series U)
  have hcount := (h.chief_data hG T hempty hM hJ X hX).2 s
  have hex : ∃ i : Fin s.series.length, ¬ s.Central i := by
    by_contra hn
    have hz := s.noncentralCount_eq_zero_iff.mpr (not_exists_not.mp hn)
    omega
  obtain ⟨i,hi⟩ := hex
  have hsmall := h.chief_thompson_actor_layer_types hG T hempty hM hJ hX s i hi
  let f := Representation.BinaryOffender.actionHom (s.factorRepresentation i)
  let J := elementaryAbelianMaxJ (⊤ : Subgroup X)
  let KX := K.subgroupOf X
  let EX := E.subgroupOf X
  let : KX.Normal := normal_subgroupOf_of_le_normalizer (hXN.trans hNK)
  have hce : KX ≤ centralizer (EX : Set X) := by
    intro k hk e he'
    exact Subtype.ext (hKE hk e he')
  have hde : ⁅KX,U⁆ ≤ EX := by
    apply (map_le_map_iff_of_injective (f := X.subtype) X.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le hUX]
    intro x hx
    have hmapK : KX.map X.subtype ≤ K := by
      rintro y ⟨k,hk,rfl⟩
      exact hk
    have hxE : x ∈ E := ((commutator_mono hmapK hUH).trans
      (commutator_commutatorPreimage_le N H E hNE)) hx
    have hxX : x ∈ X := ((Subgroup.commutator_le_sup _ _).trans
      (sup_le (map_subtype_le KX) hUX)) hx
    exact ⟨⟨x,hxX⟩,hxE,rfl⟩
  have hkf : KX ≤ f.ker := chief_kernel_of_two_layer U EX KX
    (he.comap_subtype) hce hde s i
  let qX := q.comp (inclusion hXN)
  have hqf : qX.ker ≤ f.ker := by
    intro x hx
    apply hkf
    have hh : inclusion hXN x ∈ q.ker := hx
    rw [hq] at hh
    exact hh
  let C := (centralizer (E : Set G)).subgroupOf X
  let : C.Normal := normal_subgroupOf_of_le_normalizer
    ((hXN.trans hNE).trans (normalizer_le_normalizer_centralizer E))
  let S := T.subtype hTX
  have hjmap : (elementaryAbelianMaxJ (S : Subgroup X)).map X.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [←elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective]
    change elementaryAbelianMaxJ (((T : Subgroup G).subgroupOf X).map X.subtype) = _
    rw [map_subgroupOf_eq_of_le hTX]
  have hJC : J ≤ C := by
    rw [show J = elementaryAbelianMaxJ (⊤ : Subgroup X) from rfl,
      elementaryAbelianMaxJ_eq_conjugateSpan_sylow S]
    apply conjugateSpanBy_le ?_ le_normalizer_of_normal
    intro x hx
    exact hJE (hjmap ▸ mem_map_of_mem X.subtype hx)
  intro hc
  have hJq : J.map qX ≤ ((centralizer (E : Set G)).subgroupOf N).map q := by
    rintro y ⟨x,hx,rfl⟩
    exact ⟨inclusion hXN x,hJC hx,rfl⟩
  exact small_layer_not_complement hsmall
    (complement_subgroup_image_of_kernel_le qX f hqf J
      (hasNormalPComplement_of_le 3 hJq hc))

/-- The centralizer image on the actual partner section H/E has no normal
three-complement. The original H-star and small chief witnesses are built
internally, and the quotient is by the literal section action kernel. -/
theorem PreparedChosenModule.decomposable_five_full_partner_section_not_three_complement
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      ∀ _hUcEq : localModule T Mc = thompsonFixed T V,
      let E := thompsonFixed T V
      let H := conjugateSpanBy V (centralizer (E : Set G))
      let K := (commutatorPreimage Mc H E).subgroupOf Mc
      ∃ hK : K.Normal, letI := hK
        ¬ HasNormalPComplement 3
          (((centralizer (E : Set G)).subgroupOf Mc).map (QuotientGroup.mk' K)) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hUcEq
  let E := thompsonFixed T V
  let C := centralizer (E : Set G)
  let H := conjugateSpanBy V C
  let K := (commutatorPreimage Mc H E).subgroupOf Mc
  have hMcE : Mc ≤ normalizer (E : Set G) := by
    change Mc ≤ normalizer (thompsonFixed T V : Set G)
    rw [←hUcEq]
    exact le_normalizer_conjugateSpanBy (centralInvolutions T) Mc
  have hVQ := (h.decomposable_five_full_partner_module_le_core
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hUcEq).2
  have hspan := h.partner_core_span_ff hG T hempty hM hJ hu hne hVQ
  dsimp only at hspan
  rw [hUcEq] at hspan
  have hMcH : Mc ≤ normalizer (H : Set G) := hspan.1
  have hMcC : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMcC.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hMc : Mc ∈ maximalTwoLocalOvergroups (T : Subgroup G) := ⟨hMcC.1,hTMc⟩
  have hn : K.Normal := normal_subgroupOf_of_le_normalizer
    (commutatorPreimage_normalized Mc H E Mc hMcE Mc.le_normalizer hMcH hMcE)
  let := hn
  refine ⟨hn,?_⟩
  have he : IsPGroup 2 E := (IsElementaryAbelian.isPGroup 2 V).to_le inf_le_left
  have hJE : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (E : Set G) :=
    hJ.trans (centralizer_le (inf_le_left.trans h.le_local))
  have hKE := h.decomposable_five_section_kernel_centralizes
    hG T hempty hM hmany hJ hu hne hfull c d hd s π hp hs hdec hq hfive
    H (le_conjugateSpanBy V C) hMcE
  exact source_section_centralizer_not_complement hG T hempty hM hJ h hMc hne.symm
    (le_conjugateSpanBy V C) hMcH hMcE he hJE hKE (QuotientGroup.mk' K)
    (QuotientGroup.ker_mk' K)

end CFSG.Quasithin.Chapter15.Section01
