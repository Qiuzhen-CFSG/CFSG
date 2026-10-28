module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.TwoChiefQuotientExclusions.Five
public import Theory.SpecificGroups.SymmetricFive.SylowOvergroup
public import Theory.GroupAction.SurjectiveFlagCosets
public import Theory.GroupAction.CoreFreeCosetQuotient
public import Theory.GroupTheory.SubgroupCoverTransport
public import Theory.GroupAction.RankTwoCosetGeometry.Kernels
public import Theory.GroupAction.RankTwoCosetGeometry.Valence
public import Theory.Representation.BinaryPermutation.FiveMarking

/-!
# The literal five-point overlap and both chief actions

In the single S₅ branch, the maximal subgroup H ∩ M contains the original
Sylow T. Its image under any prescribed H/O₂(H) marking is a point
stabilizer S₄, while its intersection with O²(H) maps to the corresponding
A₄. This gives an equivariant five-point coset action and identifies its
kernel with O₂(H). The indices are [H : H ∩ M] = 5 and [H ∩ M : T] = 3.

The original F.1.1 pair [Y₁Rc, O²(H)] has full parabolics Y₁(H ∩ M) and H,
with intersection H ∩ M. Its graph has degrees three or five, and five.
The radius-one kernel at H is exactly the embedded O₂(H). Innerness of
S₅ automorphisms aligns both original natural chief factors with the same
prescribed quotient map, so both action kernels give this graph kernel.

These are the actual local action and kernel inputs to the remaining mixed
recognition; they do not assert its classification or a radius-two bound.
The first factor Y₁Rc need not contain T. The two distinct chief intervals,
full second parabolic H, and literal quotient maps are retained throughout.

Source: Aschbacher--Smith 15.1.12 and 15.2.6--8, printed pp.1090,1109--1110;
F.1.1 and F.1.12, printed pp.259,262--264, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem overlap_coatom
    {T : Sylow 2 G} {M H : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    IsCoatom ((H ⊓ M).subgroupOf H) := by
  apply CovBy.isCoatom
  apply (covBy_map_subtype_iff H _ _).mp
  rw [map_subgroupOf_eq_of_le inf_le_left,←MonoidHom.range_eq_map,range_subtype]
  exact (Chapter3.HStar.unique_maximal T hTM hH).2.1

/-- The actual overlap and residual intersection are the S₄ and A₄
point stabilizers under the prescribed quotient map. -/
theorem ChosenSmallSource.symmetricFive_overlap_action
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (e : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5)) :
    let B := (H ⊓ M).subgroupOf H
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
    ∃ i : Fin 5, B.map q = MulAction.stabilizer (Equiv.Perm (Fin 5)) i ∧
      (B ⊓ pResidual 2 H).map q =
        alternatingGroup (Fin 5) ⊓ MulAction.stabilizer (Equiv.Perm (Fin 5)) i ∧
      B.normalCore = pCore 2 H ∧
      ∃ d : (H ⧸ B) ≃ Fin 5,
        (∀ x : H, d (x : H ⧸ B) = q x i) ∧
        (∀ (x : H) ω, d (x • ω) = q x (d ω)) := by
  let B := (H ⊓ M).subgroupOf H
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let P := T.subtype hH.1.1.2
  have hPB : (P : Subgroup H) ≤ B := fun x hx => ⟨x.property,h.maximal.1.2 hx⟩
  have hkB : q.ker ≤ B := hk ▸ (pCore_isPGroup.le_sylow_of_normal P).trans hPB
  have hR : (pResidual 2 H).map q = alternatingGroup (Fin 5) :=
    (map_pResidual_of_surjective 2 q hq).trans (Equiv.Perm.twoResidual_eq_alternating (Fin 5))
  obtain ⟨i,hi,hRi,_⟩ := Theory.SpecificGroups.SymmetricFive.SylowOvergroup.quotient_borel
    q hq P B (pResidual 2 H) hPB (overlap_coatom h.maximal.1.2 hH) hkB hR
  have hc : B.normalCore = q.ker := B.normalCore_eq_ker_of_map_core_free q hq hkB (by
    rw [hi]
    exact MulAction.stabilizer_normalCore_eq_bot_of_faithful i)
  refine ⟨i,hi,hRi,hc.trans hk,MulAction.surjectiveCosetEquiv B q hq hkB i hi,?_,?_⟩
  · exact MulAction.surjectiveCosetEquiv_mk B q hq hkB i hi
  · exact MulAction.surjectiveCosetEquiv_smul B q hq hkB i hi

/-- The full overlap has index five in H and index three above T. -/
theorem ChosenSmallSource.symmetricFive_overlap_indices
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5))) :
    (H ⊓ M).relIndex H = 5 ∧
      (T : Subgroup G).relIndex (H ⊓ M) = 3 := by
  obtain ⟨i,hi,hRi,hcore,d,hrep,hact⟩ := h.symmetricFive_overlap_action hH he.some
  have hB : (H ⊓ M).relIndex H = 5 := by
    change Nat.card (H ⧸ (H ⊓ M).subgroupOf H) = 5
    exact (Nat.card_congr d).trans (Nat.card_fin 5)
  let q := he.some.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : Function.Surjective q := he.some.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ he.some.injective,QuotientGroup.ker_mk']
  let P := T.subtype hH.1.1.2
  let Q := P.mapSurjective hq
  have hQc : Nat.card Q = 8 := by
    rw [Q.card_eq_multiplicity]
    have hc : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
      simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
    rw [hc]
    decide +kernel
  have hQindex := (Q : Subgroup (Equiv.Perm (Fin 5))).index_mul_card
  rw [hQc] at hQindex
  have hc : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  rw [hc] at hQindex
  have hPi : Q.index = P.index := (P : Subgroup H).index_map_eq hq (by
    rw [hk]
    exact pCore_isPGroup.le_sylow_of_normal P)
  rw [hPi] at hQindex
  have hT : (T : Subgroup G).relIndex H = 15 := by
    change P.index = 15
    omega
  have hm := relIndex_mul_relIndex (T : Subgroup G) (H ⊓ M) H
    (le_inf hH.1.1.2 h.maximal.1.2) inf_le_left
  rw [hB,hT] at hm
  exact ⟨hB,by omega⟩

/-- The full parabolics and overlap in the single S₅ branch, with no
containment of T in the first rank-one factor. -/
theorem SmallResidualWitness.symmetricFive_geometry
    {T : Sylow 2 G} {M Mc V Y₁ H : Subgroup G} {h : ChosenSmallSource T M Mc V}
    (hw : SmallResidualWitness h Y₁) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5))) :
    let L := ![Y₁ ⊔ (M ⊓ Mc).pCoreIn 2,(pResidual 2 H).map H.subtype]
    ChapterF.Source.commonBorel L (T : Subgroup G) = H ⊓ M ∧
      ChapterF.Source.parabolic L (T : Subgroup G) 0 = Y₁ ⊔ (H ⊓ M) ∧
      ChapterF.Source.parabolic L (T : Subgroup G) 1 = H ∧
      (Y₁ ⊔ (H ⊓ M)) ⊓ H = H ⊓ M := by
  let := h.prepared.elementary
  let L := ![Y₁ ⊔ (M ⊓ Mc).pCoreIn 2,(pResidual 2 H).map H.subtype]
  obtain ⟨hF,hB₀,hP₁,hN,_⟩ := hw.symmetricFive_pair hH he
  have hB : ChapterF.Source.commonBorel L (T : Subgroup G) = H ⊓ M := by
    rw [hF.commonBorel_eq_normalizer 1,hP₁]
    exact hN.symm
  have hMc : Mc ∈ maximalTwoLocalOvergroups
      (Subgroup.centralizer (centralInvolutions T : Set G)) := h.partner ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hRT : (M ⊓ Mc).pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow (M ⊓ Mc) (T.subtype (le_inf h.maximal.1.2 hTMc))
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le (le_inf h.maximal.1.2 hTMc)] using hh
  have hRB : (M ⊓ Mc).pCoreIn 2 ≤ H ⊓ M :=
    hRT.trans (le_inf hH.1.1.2 h.maximal.1.2)
  have hP₀ : ChapterF.Source.parabolic L (T : Subgroup G) 0 = Y₁ ⊔ (H ⊓ M) := by
    rw [ChapterF.Source.parabolic_eq_sup_commonBorel,hB]
    change (Y₁ ⊔ (M ⊓ Mc).pCoreIn 2) ⊔ (H ⊓ M) = _
    rw [sup_assoc,sup_eq_right.mpr hRB]
  refine ⟨hB,hP₀,hP₁,?_⟩
  have hi := ChapterF.Source.lemma_F_1_3_6 hF
  change ChapterF.Source.parabolic L (T : Subgroup G) 0 ⊓
    ChapterF.Source.parabolic L (T : Subgroup G) 1 = _ at hi
  rwa [hP₀,hP₁,hB] at hi

private theorem commonBorel_parabolic_index
    {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (hF : ChapterF.Source.HypothesisF11 L S) (i : Fin 2) :
    (ChapterF.Source.commonBorel L S).relIndex (ChapterF.Source.parabolic L S i) =
      (ChapterF.Source.borel (L i) S).relIndex (L i) := by
  rw [ChapterF.Source.parabolic_eq_sup_commonBorel,
    relIndex_sup_of_normalizes _ _ (hF.commonBorel_normalizes_local i)]
  rw [←inf_relIndex_right (ChapterF.Source.commonBorel L S) (L i),inf_comm,
    hF.local_inf_commonBorel i]

/-- The actual common Borel has degree three or five at the first
parabolic, and degree five at the full original H. -/
theorem SmallResidualWitness.symmetricFive_parabolic_indices
    {T : Sylow 2 G} {M Mc V Y₁ H : Subgroup G} {h : ChosenSmallSource T M Mc V}
    (hw : SmallResidualWitness h Y₁) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5))) :
    ((H ⊓ M).relIndex (Y₁ ⊔ (H ⊓ M)) = 3 ∨
      (H ⊓ M).relIndex (Y₁ ⊔ (H ⊓ M)) = 5) ∧
      (H ⊓ M).relIndex H = 5 ∧
      (T : Subgroup G) < H ⊓ M := by
  let L₀ := Y₁ ⊔ (M ⊓ Mc).pCoreIn 2
  let L := ![L₀,(pResidual 2 H).map H.subtype]
  obtain ⟨hF,hB₀,_⟩ := hw.symmetricFive_pair hH he
  obtain ⟨hB,hP₀,hP₁,hinter⟩ := hw.symmetricFive_geometry hH he
  have hindex := commonBorel_parabolic_index hF 0
  rw [hB,hP₀] at hindex
  change (H ⊓ M).relIndex (Y₁ ⊔ (H ⊓ M)) =
    (ChapterF.Source.borel L₀ (T : Subgroup G)).relIndex L₀ at hindex
  rw [hB₀] at hindex
  have hs : ∃ P : Sylow 2 L₀,
      (P : Subgroup L₀).map L₀.subtype = (T : Subgroup G) ⊓ L₀ := hF.sylow 0
  obtain ⟨P,hP⟩ := hs
  have hsub : ((T : Subgroup G) ⊓ L₀).subgroupOf L₀ = (P : Subgroup L₀) := by
    rw [←hP]
    exact comap_map_eq_self_of_injective L₀.subtype_injective _
  have hpindex : (H ⊓ M).relIndex (Y₁ ⊔ (H ⊓ M)) = P.index := by
    rw [hindex]
    change (((T : Subgroup G) ⊓ L₀).subgroupOf L₀).index = _
    rw [hsub]
  have hcard : Nat.card (L₀ ⧸ pCore 2 L₀) = 6 ∨
      Nat.card (L₀ ⧸ pCore 2 L₀) = 10 ∨ Nat.card (L₀ ⧸ pCore 2 L₀) = 20 := by
    rcases hw.quotient with h3 | h5 | h20
    · exact Or.inl ((Nat.card_congr h3.some.toEquiv).trans (by
        simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]))
    · exact Or.inr (Or.inl ((Nat.card_congr h5.some.toEquiv).trans (by
        rw [DihedralGroup.nat_card])))
    · exact Or.inr (Or.inr ((Nat.card_congr h20.some.toEquiv).trans
        BenderSuzuki.MatrixGroups.suzukiZero_card))
  have hi := h.symmetricFive_overlap_indices hH he
  refine ⟨?_,hi.1,?_⟩
  · simpa only [hpindex] using sylow_index_small_core_quotient P hcard
  · apply lt_of_le_of_ne (show (T : Subgroup G) ≤ H ⊓ M from
      le_inf hH.1.1.2 h.maximal.1.2)
    intro ht
    have htindex := hi.2
    rw [ht,relIndex_self] at htindex
    omega

open Subgroup.CosetGeometry.RankTwo in
/-- The source graph's quintic endpoint has exactly the original H-core
as its radius-one kernel. This graph keeps the whole overlap H ∩ M. -/
theorem SmallResidualWitness.symmetricFive_graph_kernel
    {T : Sylow 2 G} {M Mc V Y₁ H : Subgroup G} {h : ChosenSmallSource T M Mc V}
    (hw : SmallResidualWitness h Y₁) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5))) :
    let F : Bool → Subgroup G := fun i => if i then H else Y₁ ⊔ (H ⊓ M)
    ballKernel F (base F true) 1 = H.pCoreIn 2 ∧
      Nat.card ((graph F).neighborSet (base F true)) = 5 ∧
      (Nat.card ((graph F).neighborSet (base F false)) = 3 ∨
        Nat.card ((graph F).neighborSet (base F false)) = 5) := by
  let P := Y₁ ⊔ (H ⊓ M)
  let F : Bool → Subgroup G := fun i => if i then H else P
  obtain ⟨_,_,_,hinter⟩ := hw.symmetricFive_geometry hH he
  obtain ⟨i,hi,hRi,hcore,d,hrep,hact⟩ := h.symmetricFive_overlap_action hH he.some
  have hk := congrArg (map H.subtype) (base_ballKernel_one F true)
  have hle : ballKernel F (base F true) 1 ≤ H := by
    simpa only [stabilizer,Subgroup.CosetGeometry.stabilizer_base,F,if_true] using
      ballKernel_le_stabilizer F (base F true) 1
  change ((ballKernel F (base F true) 1).subgroupOf H).map H.subtype =
    ((P ⊓ H).subgroupOf H).normalCore.map H.subtype at hk
  rw [map_subgroupOf_eq_of_le hle,hinter,hcore] at hk
  obtain ⟨hfirst,hsecond,_⟩ := hw.symmetricFive_parabolic_indices hH he
  refine ⟨hk,?_,?_⟩
  · rw [card_neighbor_base]
    change P.relIndex H = 5
    rw [←inf_relIndex_right P H,hinter]
    exact hsecond
  · rw [card_neighbor_base]
    change H.relIndex P = 3 ∨ H.relIndex P = 5
    rw [←inf_relIndex_left P H,hinter]
    exact hfirst

open NoncentralChiefRefinement ChapterB.QuasisimpleSource

/-- Both original chief factors use the prescribed marking of H/O₂(H).
Their linear coordinate changes do not alter the common quotient map. -/
theorem ChosenSmallSource.symmetricFive_marked_chief_actions
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hprior : SmallSourcePrior T M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (e : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5)) :
    letI := h.prepared.elementary
    let U := (conjugateSpan H V).subgroupOf H
    letI := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
    letI : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
      (show conjugateSpan H V ≤ H by
        rw [UniqueFactor.conjugateSpan_eq]
        exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H)))
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
    ∀ s : SeriesOn U, ∃ i j : Fin s.series.length, i ≠ j ∧
      ∀ k ∈ ({i,j} : Finset (Fin s.series.length)), ¬ s.Central k ∧
        (Representation.BinaryOffender.actionHom (s.factorRepresentation k)).ker = pCore 2 H ∧
        Nat.card (s.Factor k) = 16 ∧
        ∃ c : Additive (s.Factor k) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 5),
          ∀ (g : H) v, c (s.factorRepresentation k g v) =
            BinaryPermutation.naturalRepresentation (Fin 5) (q g) (c v) := by
  let := h.prepared.elementary
  let U := (conjugateSpan H V).subgroupOf H
  let := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    (show conjugateSpan H V ≤ H by
      rw [UniqueFactor.conjugateSpan_eq]
      exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H)))
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqk : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  dsimp only
  intro s
  obtain ⟨i,j,hij,hs⟩ := h.symmetricFive_chief_actions hprior hH ⟨e⟩ s
  refine ⟨i,j,hij,?_⟩
  intro k hk
  obtain ⟨hn,hker,⟨a⟩,hcard⟩ := hs k hk
  let ρ := s.factorRepresentation k
  let f := a.groupEquiv.toMonoidHom.comp (Representation.BinaryOffender.actionHom ρ)
  have hf : Function.Surjective f :=
    a.groupEquiv.surjective.comp ρ.asGroupHom.rangeRestrict_surjective
  have hfker : f.ker = (Representation.BinaryOffender.actionHom ρ).ker :=
    MonoidHom.ker_comp_of_injective _ _ a.groupEquiv.injective
  have hfk : q.ker = f.ker := hqk.trans (hker.symm.trans hfker.symm)
  exact ⟨hn,hker,hcard,BinaryPermutation.natural_five_coordinates_of_kernel ρ q f hq hf hfk
    a.linearEquiv (fun g v => a.intertwines (Representation.BinaryOffender.actionHom ρ g) v)⟩

open Subgroup.CosetGeometry.RankTwo in
/-- The actual quintic graph kernel is the embedded action kernel of both
original natural chief factors, using the same prescribed quotient map. -/
theorem SmallResidualWitness.symmetricFive_graph_chief_kernels
    {T : Sylow 2 G} {M Mc V Y₁ H : Subgroup G} {h : ChosenSmallSource T M Mc V}
    (hw : SmallResidualWitness h Y₁) (hprior : SmallSourcePrior T M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (e : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5)) :
    letI := h.prepared.elementary
    let U := (conjugateSpan H V).subgroupOf H
    letI := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
    letI : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
      (show conjugateSpan H V ≤ H by
        rw [UniqueFactor.conjugateSpan_eq]
        exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H)))
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
    let F : Bool → Subgroup G := fun i => if i then H else Y₁ ⊔ (H ⊓ M)
    ∀ s : SeriesOn U, ∃ i j : Fin s.series.length, i ≠ j ∧
      ∀ k ∈ ({i,j} : Finset (Fin s.series.length)), ¬ s.Central k ∧
        (Representation.BinaryOffender.actionHom (s.factorRepresentation k)).ker = pCore 2 H ∧
        ((Representation.BinaryOffender.actionHom (s.factorRepresentation k)).ker).map H.subtype =
          ballKernel F (base F true) 1 ∧
        Nat.card (s.Factor k) = 16 ∧
        ∃ c : Additive (s.Factor k) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 5),
          ∀ (g : H) v, c (s.factorRepresentation k g v) =
            BinaryPermutation.naturalRepresentation (Fin 5) (q g) (c v) := by
  let := h.prepared.elementary
  let U := (conjugateSpan H V).subgroupOf H
  let := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    (show conjugateSpan H V ≤ H by
      rw [UniqueFactor.conjugateSpan_eq]
      exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H)))
  dsimp only
  intro s
  obtain ⟨i,j,hij,hs⟩ := h.symmetricFive_marked_chief_actions hprior hH e s
  have hk := (hw.symmetricFive_graph_kernel hH ⟨e⟩).1
  refine ⟨i,j,hij,?_⟩
  intro k hmem
  obtain ⟨hn,hker,hcard,hcoord⟩ := hs k hmem
  exact ⟨hn,hker,by rw [hker,hk]; rfl,hcard,hcoord⟩

end CFSG.Quasithin.Chapter15.Section02
