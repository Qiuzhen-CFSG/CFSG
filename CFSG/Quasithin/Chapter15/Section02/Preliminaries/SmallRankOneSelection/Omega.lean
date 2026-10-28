module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SmallRankOneSelection
public import Theory.GroupTheory.CubicResidualPreimage
public import Theory.GroupTheory.SpecificGroups.SymmetricThreeProductResidual.CubicSelection
public import Theory.GroupTheory.SpecificGroups.SymmetricThreeProductResidual.ExtraspecialCubicSelection

/-!
# The complete Omega rank-one selection

In the elementary-nine row, a normal cubic direction of the actual action
lifts to the two-residual of its preimage inside Y. In the extraspecial
row, the star action has central kernel. An invariant order-nine preimage
supplies two noncentral cubic generators; at least one is moved by Rc.
Its faithful image then gives the same preimage construction.

All three Omega rows retain the literal chosen action, Y, Rc and quotient
maps. The resulting Y₁ is two-perfect, T-invariant and fully moved by Rc;
its centralizer on V is O₂(Y₁), and Y₁Rc/O₂(Y₁Rc) is S₃. Combining this
with the existing dihedral selections completes the local selection family.
The actual residual-witness and H-star consumers retain only the preceding
maximal-overgroup comparison, which remains with qt-e-152-small-parabolic.
The two-chief exclusions and marked-five wreath exclusion are separate
remaining obligations of that same source-family owner.

Source: Aschbacher--Smith 15.2.3 and 15.2.6--8, printed pp.1105,1109--1110.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

private theorem core_le_sylow
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V) :
    (M ⊓ Mc).pCoreIn 2 ≤ (T : Subgroup G) := by
  have hMc : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := h.partner ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hh := pCoreIn_le_sylow (M ⊓ Mc) (T.subtype (le_inf h.maximal.1.2 hTMc))
  simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le (le_inf h.maximal.1.2 hTMc)] using hh

private theorem selection_of_kernel_and_image
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (X : Subgroup M) (hXY : X ≤ h.residual.subgroupOf M)
    (hSX : (T : Subgroup G).subgroupOf M ≤ normalizer (X : Set M))
    (hk : letI := h.prepared.elementary
      X ⊓ (actionHom M V h.prepared.normalized).rangeRestrict.ker ≤
        pCore 2 M)
    (hC : letI := h.prepared.elementary
      let f := (actionHom M V h.prepared.normalized).rangeRestrict
      ∃ C : Subgroup (actionHom M V h.prepared.normalized).range,
        C ≤ X.map f ∧ Nat.card C = 3 ∧
        ((T : Subgroup G).subgroupOf M).map f ≤ normalizer (C : Set (actionHom M V h.prepared.normalized).range) ∧
        ¬ (((M ⊓ Mc).pCoreIn 2).subgroupOf M).map f ≤ centralizer (C : Set (actionHom M V h.prepared.normalized).range)) :
    ∃ Y₁ : Subgroup G, Y₁ ≤ h.residual ∧ IsPPerfect 2 Y₁ ∧ Y₁ ≠ ⊥ ∧
      (T : Subgroup G) ≤ normalizer (Y₁ : Set G) ∧
      ⁅Y₁,(M ⊓ Mc).pCoreIn 2⁆ = Y₁ ∧
      Y₁ ⊓ centralizer (V : Set G) = Y₁.pCoreIn 2 ∧
      Nonempty (((Y₁ ⊔ (M ⊓ Mc).pCoreIn 2 : Subgroup G) ⧸
        pCore 2 (Y₁ ⊔ (M ⊓ Mc).pCoreIn 2 : Subgroup G)) ≃* Equiv.Perm (Fin 3)) := by
  let := h.prepared.elementary
  let R := ((M ⊓ Mc).pCoreIn 2).subgroupOf M
  let S := (T : Subgroup G).subgroupOf M
  let f := (actionHom M V h.prepared.normalized).rangeRestrict
  obtain ⟨C,hCX,hc,hn,hm⟩ := hC
  have hcoreR : pCore 2 M ≤ R := by
    have hh := (h.prepared.intersection_core_centralizer T h.maximal.1.2 h.partner).symm.le
    intro x hx
    exact (hh (mem_map_of_mem M.subtype hx)).1
  obtain ⟨A,hAX,hAp,hSA,hAC,hmove,hne,hker,⟨e⟩⟩ :=
    exists_cubic_residual_of_invariant_image X R S f hSX
      (comap_mono (core_le_sylow h)) (isPGroup_pCoreIn 2 (M ⊓ Mc)).comap_subtype
      (pCore_isPGroup.to_le hk) (hk.trans hcoreR) C hCX hc hn hm
  let Y₁ := A.map M.subtype
  have hR : R.map M.subtype = (M ⊓ Mc).pCoreIn 2 :=
    map_subgroupOf_eq_of_le ((pCoreIn_le 2 _).trans inf_le_left)
  have hjoin : (A ⊔ R).map M.subtype = Y₁ ⊔ (M ⊓ Mc).pCoreIn 2 := by
    rw [Subgroup.map_sup,hR]
  let j : (A ⊔ R : Subgroup M) ≃* (Y₁ ⊔ (M ⊓ Mc).pCoreIn 2 : Subgroup G) :=
    ((A ⊔ R).equivMapOfInjective M.subtype M.subtype_injective).trans
      (MulEquiv.subgroupCongr hjoin)
  let q := QuotientGroup.congr (pCore 2 (A ⊔ R : Subgroup M))
    (pCore 2 (Y₁ ⊔ (M ⊓ Mc).pCoreIn 2 : Subgroup G)) j (pCore_map_iso 2 j)
  have hpc : (A.pCoreIn 2).map M.subtype = Y₁.pCoreIn 2 := by
    let ea := A.equivMapOfInjective M.subtype M.subtype_injective
    change ((pCore 2 A).map A.subtype).map M.subtype = (pCore 2 Y₁).map Y₁.subtype
    rw [←pCore_map_iso 2 ea,map_map,map_map]
    rfl
  refine ⟨Y₁,?_,hAp.of_surjective (M.subtype.subgroupMap A)
    (M.subtype.subgroupMap_surjective A),?_,?_,?_,?_,⟨q.symm.trans e⟩⟩
  · rintro _ ⟨a,ha,rfl⟩
    exact hXY (hAX ha)
  · intro he
    exact hne ((map_injective M.subtype_injective) (he.trans (Subgroup.map_bot M.subtype).symm))
  · have hh := (map_mono (f := M.subtype) hSA).trans (A.le_normalizer_map M.subtype)
    rwa [map_subgroupOf_eq_of_le h.maximal.1.2] at hh
  · have hh := congrArg (map M.subtype) hmove
    simpa only [map_commutator,hR] using hh
  · rw [←hpc,←hker]
    ext x
    constructor
    · rintro ⟨⟨a,ha,rfl⟩,hx⟩
      refine ⟨a,⟨ha,?_⟩,rfl⟩
      apply Subtype.ext
      change a ∈ (actionHom M V h.prepared.normalized).ker
      rw [actionHom_ker]
      exact hx
    · rintro ⟨a,⟨ha,hak⟩,rfl⟩
      refine ⟨mem_map_of_mem M.subtype ha,?_⟩
      have he : a ∈ (actionHom M V h.prepared.normalized).ker := congrArg Subtype.val hak
      rwa [actionHom_ker] at he

/-- The elementary-nine Omega residual supplies a literal invariant rank-one lift. -/
theorem ChosenSmallSource.omega_elementary_residual_selection
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (ho : letI := h.prepared.elementary
      SourceCases.Omega (imageRepresentation M V h.prepared.normalized))
    (hc : letI := h.prepared.elementary
      Nat.card ((h.residual.subgroupOf M).map (QuotientGroup.mk' (pCore 2 M))) = 9) :
    ∃ Y₁ : Subgroup G, Y₁ ≤ h.residual ∧ IsPPerfect 2 Y₁ ∧ Y₁ ≠ ⊥ ∧
      (T : Subgroup G) ≤ normalizer (Y₁ : Set G) ∧
      ⁅Y₁,(M ⊓ Mc).pCoreIn 2⁆ = Y₁ ∧
      Y₁ ⊓ centralizer (V : Set G) = Y₁.pCoreIn 2 ∧
      Nonempty (((Y₁ ⊔ (M ⊓ Mc).pCoreIn 2 : Subgroup G) ⧸
        pCore 2 (Y₁ ⊔ (M ⊓ Mc).pCoreIn 2 : Subgroup G)) ≃* Equiv.Perm (Fin 3)) := by
  let := h.prepared.elementary
  have hs := source_omega_chosen_residual_complete h.ambient T h.empty h.maximal
    h.centralizing h.partner h.many h.prepared ho
  have hd := hs.alternatives
  rcases hd with ⟨hfull,_,_,_,_,hker,_⟩ | ⟨_,hc27,_⟩ | ⟨_,_,hc3,_⟩
  swap
  · have hh : (9 : ℕ) = 27 := hc.symm.trans hc27
    norm_num at hh
  swap
  · have hh : (9 : ℕ) = 3 := hc.symm.trans hc3
    norm_num at hh
  let Y := h.residual
  let f := (actionHom M V h.prepared.normalized).rangeRestrict
  have hYM : Y ≤ M := source_caseIIResidual_le T h.maximal.1.2 (map_subtype_le _)
  have hYn : M ≤ normalizer (Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hYM).mp hs.normal
  have hQn : ((Y.pCoreIn 2).subgroupOf M).Normal :=
    (normal_subgroupOf_iff_le_normalizer ((pCoreIn_le 2 Y).trans hYM)).mpr
      (hYn.trans (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y)))
  have hQ : (Y.pCoreIn 2).subgroupOf M ≤ pCore 2 M :=
    le_sSup ⟨hQn,(isPGroup_pCoreIn 2 Y).comap_subtype⟩
  apply selection_of_kernel_and_image h (h.residual.subgroupOf M) le_rfl
    ((comap_mono h.residual_invariant).trans (h.residual.le_normalizer_comap M.subtype))
  · intro x hx
    have hxC : (x : G) ∈ centralizer (V : Set G) := by
      have hh : x ∈ (actionHom M V h.prepared.normalized).ker := congrArg Subtype.val hx.2
      rwa [actionHom_ker] at hh
    exact hQ (show (x : G) ∈ Y.pCoreIn 2 from hker ▸ ⟨hx.1,hxC⟩)
  · let S := (T.subtype h.maximal.1.2).mapSurjective
      (f := f) (actionHom M V h.prepared.normalized).rangeRestrict_surjective
    let R := (((M ⊓ Mc).pCoreIn 2).subgroupOf M).map f
    have hRS : R ≤ (S : Subgroup (actionHom M V h.prepared.normalized).range) :=
      map_mono (comap_mono (core_le_sylow h))
    have hm : ⁅pResidual 2 (actionHom M V h.prepared.normalized).range,R⁆ =
        pResidual 2 (actionHom M V h.prepared.normalized).range := by
      simpa only [hfull] using hs.image_movement
    let e : (actionHom M V h.prepared.normalized).range ≃* SymmetricThreeProduct.G :=
      ho.2.2.2.1.some
    obtain ⟨C,hCn,hCP,hCc,hCm⟩ :=
      SymmetricThreeProductResidual.exists_normal_cubic_moved_by_full_actor e S R hRS hm
    let : C.Normal := hCn
    exact ⟨C,hfull.symm ▸ hCP,hCc,le_normalizer_of_normal,hCm⟩

/-- The elementary-nine lift supplies all clauses of 15.2.6 and 15.2.7(ii).
The Omega overgroup comparison remains with this source-family owner. -/
theorem ChosenSmallSource.smallResidualWitness_of_omega_elementary
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (ho : letI := h.prepared.elementary
      SourceCases.Omega (imageRepresentation M V h.prepared.normalized))
    (hc : letI := h.prepared.elementary
      Nat.card ((h.residual.subgroupOf M).map (QuotientGroup.mk' (pCore 2 M))) = 9)
    (hover : maximalTwoLocalOvergroups (T : Subgroup G) = {M,Mc}) :
    ∃ Y₁ : Subgroup G, SmallResidualWitness h Y₁ ∧ SmallCubicNormalizer h Y₁ := by
  obtain ⟨Y₁,hle,hp,hne,hn,hm,hcentral,hquot⟩ := h.omega_elementary_residual_selection ho hc
  exact ⟨Y₁,h.smallResidualWitness_of_moved_selection hover hle hp hne hn hm
    (Or.inl hquot) hcentral⟩

/-- The extraspecial Omega residual supplies a faithful invariant rank-one lift. -/
theorem ChosenSmallSource.omega_extraspecial_residual_selection
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (ho : letI := h.prepared.elementary
      SourceCases.Omega (imageRepresentation M V h.prepared.normalized))
    (hc : letI := h.prepared.elementary
      Nat.card ((h.residual.subgroupOf M).map (QuotientGroup.mk' (pCore 2 M))) = 27) :
    ∃ Y₁ : Subgroup G, Y₁ ≤ h.residual ∧ IsPPerfect 2 Y₁ ∧ Y₁ ≠ ⊥ ∧
      (T : Subgroup G) ≤ normalizer (Y₁ : Set G) ∧
      ⁅Y₁,(M ⊓ Mc).pCoreIn 2⁆ = Y₁ ∧
      Y₁ ⊓ centralizer (V : Set G) = Y₁.pCoreIn 2 ∧
      Nonempty (((Y₁ ⊔ (M ⊓ Mc).pCoreIn 2 : Subgroup G) ⧸
        pCore 2 (Y₁ ⊔ (M ⊓ Mc).pCoreIn 2 : Subgroup G)) ≃* Equiv.Perm (Fin 3)) := by
  let := h.prepared.elementary
  have hs := source_omega_chosen_residual_complete h.ambient T h.empty h.maximal
    h.centralizing h.partner h.many h.prepared ho
  rcases hs.alternatives with ⟨_,_,hc9,_⟩ | ⟨hfull,_,hex,⟨eP⟩,_⟩ | ⟨_,_,hc3,_⟩
  · have hh : (27 : ℕ) = 9 := hc.symm.trans hc9
    norm_num at hh
  swap
  · have hh : (27 : ℕ) = 3 := hc.symm.trans hc3
    norm_num at hh
  let Y := h.residual.subgroupOf M
  let q := QuotientGroup.mk' (pCore 2 M)
  let P := Y.map q
  let R₀ := ((M ⊓ Mc).pCoreIn 2).subgroupOf M
  let R := R₀.map q
  let S₀ := (T : Subgroup G).subgroupOf M
  let S := S₀.map q
  let a := (actionHom M V h.prepared.normalized).rangeRestrict
  let b := omegaStarActor h.prepared.normalized ho
  let e : (actionHom M V h.prepared.normalized).range ≃* SymmetricThreeProduct.G :=
    ho.2.2.2.1.some
  let f := e.toMonoidHom.comp b
  let : Y.Normal := hs.normal
  let : P.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : IsExtraspecial 3 P := hex
  have himP : P.map f = (Y.map a).map e.toMonoidHom := by
    rw [map_map,map_map]
    rfl
  have himR : R.map f = (R₀.map a).map e.toMonoidHom := by
    rw [map_map,map_map]
    rfl
  have him : P.map f = pResidual 2 SymmetricThreeProduct.G := by
    rw [himP,hfull,map_pResidual_of_surjective 2 e.toMonoidHom e.surjective]
  have hnine : Nat.card (Y.map a) = 9 := by
    have hh := congrArg (fun K : Subgroup SymmetricThreeProduct.G => Nat.card K) him
    rw [himP,card_map_of_injective e.injective,SymmetricThreeProductResidual.residual_card] at hh
    exact hh
  have hk : (f.domRestrict P).ker = center P := by
    change (e.toMonoidHom.comp (b.domRestrict P)).ker = center P
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
    exact source_omega_extraspecial_star_kernel T h.maximal.1.2 h.partner h.prepared ho hnine hex
  have hexp : Monoid.exponent P = 3 :=
    (Monoid.exponent_eq_of_mulEquiv eP).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  have hm : ¬ R.map f ≤ centralizer (P.map f : Set _) := by
    intro he
    have hh := commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp he)
    have hmove : ⁅P.map f,R.map f⁆ = P.map f := by
      rw [himP,himR,←map_commutator,hs.image_movement]
    rw [hmove,him] at hh
    have hcard := congrArg (fun K : Subgroup SymmetricThreeProduct.G => Nat.card K) hh
    rw [SymmetricThreeProductResidual.residual_card,card_bot] at hcard
    omega
  obtain ⟨C,hCP,hCc,hSC,hCker,hCm⟩ :=
    SymmetricThreeProductResidual.exists_extraspecial_cubic_moved_by_square_actor
      P hc hexp f him hk S R (T.isPGroup'.comap_subtype.map q) hm
  let X := Y ⊓ C.comap q
  have hSX : S₀ ≤ normalizer (X : Set M) :=
    (le_inf le_normalizer_of_normal
      ((map_le_iff_le_comap.mp hSC).trans (C.le_normalizer_comap q))).trans
        inf_normalizer_le_normalizer_inf
  have hXq : X.map q = C := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact hx.2
    · intro c hcC
      obtain ⟨x,hx,he⟩ := hCP hcC
      exact ⟨x,⟨hx,show q x ∈ C from he.symm ▸ hcC⟩,he⟩
  have hXf : (X.map a).map e.toMonoidHom = C.map f := by
    rw [←hXq,map_map,map_map]
    rfl
  have hfi : Function.Injective (f.subgroupMap C) := by
    apply (injective_iff_map_eq_one _).mpr
    intro x hx
    exact Subtype.ext (disjoint_def.mp hCker x.property (congrArg Subtype.val hx))
  have hcard : Nat.card (X.map a) = 3 := by
    have hh := (Nat.card_congr (MulEquiv.ofBijective (f.subgroupMap C)
      ⟨hfi,f.subgroupMap_surjective C⟩).toEquiv).symm.trans hCc
    rw [←hXf,card_map_of_injective e.injective] at hh
    exact hh
  apply selection_of_kernel_and_image h X inf_le_left hSX
  · intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    apply disjoint_def.mp hCker hx.1.2
    change e (a x) = 1
    rw [show a x = 1 from hx.2,map_one]
  · refine ⟨X.map a,le_rfl,hcard,
      (map_mono hSX).trans (X.le_normalizer_map a),?_⟩
    intro he
    apply hCm
    rw [himR,←hXf]
    rintro _ ⟨r,hr,rfl⟩ _ ⟨x,hx,rfl⟩
    exact (map_mul e.toMonoidHom x r).symm.trans
      ((congrArg e (he hr x hx)).trans (map_mul e.toMonoidHom r x))

/-- The original Omega rank-one construction in all three residual rows,
including the extraspecial central extension and proper chosen supports. -/
theorem ChosenSmallSource.omega_rank_one_selection
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (ho : letI := h.prepared.elementary
      SourceCases.Omega (imageRepresentation M V h.prepared.normalized)) :
    ∃ Y₁ : Subgroup G, Y₁ ≤ h.residual ∧ IsPPerfect 2 Y₁ ∧ Y₁ ≠ ⊥ ∧
      (T : Subgroup G) ≤ normalizer (Y₁ : Set G) ∧
      ⁅Y₁,(M ⊓ Mc).pCoreIn 2⁆ = Y₁ ∧
      Y₁ ⊓ centralizer (V : Set G) = Y₁.pCoreIn 2 ∧
      Nonempty (((Y₁ ⊔ (M ⊓ Mc).pCoreIn 2 : Subgroup G) ⧸
        pCore 2 (Y₁ ⊔ (M ⊓ Mc).pCoreIn 2 : Subgroup G)) ≃* Equiv.Perm (Fin 3)) := by
  let := h.prepared.elementary
  have hs := source_omega_chosen_residual_complete h.ambient T h.empty h.maximal
    h.centralizing h.partner h.many h.prepared ho
  rcases hs.alternatives with ⟨_,_,hc9,_⟩ | ⟨_,hc27,_⟩ | ⟨hc3,_⟩
  · exact h.omega_elementary_residual_selection ho hc9
  · exact h.omega_extraspecial_residual_selection ho hc27
  · obtain ⟨hm,hne,hq,hcentral⟩ := h.omega_cubic_residual_selection ho hc3
    exact ⟨h.residual,le_rfl,h.residual_perfect,hne,h.residual_invariant,hm,hcentral,hq⟩

/-- All Omega rows supply 15.2.6--7 once the preceding overgroup comparison
is discharged by the same source-family owner, qt-e-152-small-parabolic. -/
theorem ChosenSmallSource.smallResidualWitness_of_omega
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (ho : letI := h.prepared.elementary
      SourceCases.Omega (imageRepresentation M V h.prepared.normalized))
    (hover : maximalTwoLocalOvergroups (T : Subgroup G) = {M,Mc}) :
    ∃ Y₁ : Subgroup G, SmallResidualWitness h Y₁ ∧ SmallCubicNormalizer h Y₁ := by
  obtain ⟨Y₁,hle,hp,hne,hn,hm,hcentral,hquot⟩ := h.omega_rank_one_selection ho
  exact ⟨Y₁,h.smallResidualWitness_of_moved_selection hover hle hp hne hn hm
    (Or.inl hquot) hcentral⟩

/-- The complete rank-one family for every small chosen action. Only original
15.2.5 remains explicit; no subgroup-selection or recognition callback remains. -/
theorem ChosenSmallSource.smallResidualWitness_of_overgroups
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hover : maximalTwoLocalOvergroups (T : Subgroup G) = {M,Mc}) :
    ∃ Y₁ : Subgroup G, SmallResidualWitness h Y₁ ∧ SmallCubicNormalizer h Y₁ := by
  rcases h.small with hd | ho
  · exact ⟨h.residual,h.smallResidualWitness_of_dihedral hd⟩
  · exact h.smallResidualWitness_of_omega ho hover

/-- Apply the complete Omega selection to the actual H-star quotient.
The two-chief S₃ and S₅ exclusions remain with the source-family assembly. -/
theorem ChosenSmallSource.HStar_quotient_of_omega
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (ho : letI := h.prepared.elementary
      SourceCases.Omega (imageRepresentation M V h.prepared.normalized))
    (hover : maximalTwoLocalOvergroups (T : Subgroup G) = {M,Mc})
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) ∨
      Nonempty ((H ⧸ pCore 2 H) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))) ∨
      Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5)) := by
  obtain ⟨Y₁,hw,_⟩ := h.smallResidualWitness_of_omega ho hover
  rcases h.HStar_small_quotient_of_residual_unique hw.residual_unique hH with
    h3 | hwr | h5 | h5wr
  · exact Or.inl h3
  · exact Or.inr (Or.inl hwr)
  · exact Or.inr (Or.inr h5)
  · let := h.prepared.elementary
    exact (source_omega_chosen_HStar_not_symmetricFive_wreath h.ambient T h.empty
      h.maximal h.centralizing h.partner h.many h.prepared ho hH h5wr).elim

end CFSG.Quasithin.Chapter15.Section02
