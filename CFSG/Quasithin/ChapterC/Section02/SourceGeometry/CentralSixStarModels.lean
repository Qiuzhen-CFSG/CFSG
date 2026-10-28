module
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.AlternatingStarSixExclusion
public import Theory.Alternating.SixSolvableSection


/-!
# C.2.7 exclusions retaining the central alternating-six cover

The original star homomorphisms have solvable kernels. They therefore
preserve the quotient by the solvable radical, and hence the alternating-six
order divisor and odd-rank obstruction, even when the residual has a
nontrivial central cover. The inherited Sylow and literal relative normality
exclude every source model, including the binary five-space endpoint.

The ambient fixed-coset application is in
`LocalAnalysisCentralizersSixSourceRigidity`. Source: Aschbacher--Smith,
C.2.7(3), printed pp.145--147, used in 12.3.6, printed p.809.
-/

public noncomputable section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.C27Source.CentralSix
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Theory.Alternating.SixSolvableSection
open BinaryLinear.OuterCyclic
variable {G : Type*} [Group G] [Finite G] {H K R M B : Subgroup G}

theorem starM_perfect_three_rank_two_of_six
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hB : B ≤ M ⊓ K) [Group.IsPerfect B]
    (e : (B ⧸ solvableRadical B) ≃* alternatingGroup (Fin 6)) :
    ∃ A : Subgroup (starM K R M), Group.IsPerfect A ∧ 2 ≤ primeRank 3 A := by
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
  refine ⟨f.range,Group.IsPerfect.range f,?_⟩
  exact image_rank_ge_two e f

theorem starM_card_dvd_of_six
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hB : B ≤ M ⊓ K)
    (e : (B ⧸ solvableRadical B) ≃* alternatingGroup (Fin 6)) :
    360 ∣ Nat.card (starM K R M) := by
  let f := (toStarImage K R).comp (inclusion (hB.trans inf_le_right))
  let : Group.IsSolvable f.ker := six_star_map_ker_solvable h _
  have hr : f.range ≤ (starM K R M).subgroupOf (starImage K R K) := by
    rintro _ ⟨b,rfl⟩
    exact mem_map_of_mem (QuotientGroup.mk' (starKernel K R)) (hB b.property)
  have hd := (image_card_dvd e f).trans (card_dvd_of_le hr)
  rwa [Nat.card_congr (subgroupOfEquivOfLe (starM_le K R M)).toEquiv] at hd

theorem starM_five_dvd_of_six
    (h : Input KnownSimple.IsKnownSimple H R M K) (hB : B ≤ M ⊓ K)
    (e : (B ⧸ solvableRadical B) ≃* alternatingGroup (Fin 6)) :
    5 ∣ Nat.card (starM K R M) :=
  (by decide : 5 ∣ 360).trans (starM_card_dvd_of_six h hB e)

theorem starM_nine_dvd_of_six
    (h : Input KnownSimple.IsKnownSimple H R M K) (hB : B ≤ M ⊓ K)
    (e : (B ⧸ solvableRadical B) ≃* alternatingGroup (Fin 6)) :
    9 ∣ Nat.card (starM K R M) :=
  (by decide : 9 ∣ 360).trans (starM_card_dvd_of_six h hB e)

/-- Rank-one star models cannot contain the surviving A6 image. -/
theorem no_linearTwo_star_of_six
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hB : B ≤ M ⊓ K) [Group.IsPerfect B]
    (e6 : (B ⧸ solvableRadical B) ≃* alternatingGroup (Fin 6))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : starImage K R K ≃* SL(2,F)) : False := by
  obtain ⟨A,hAp,hAr⟩ := starM_perfect_three_rank_two_of_six h hB e6
  let j := e.toMonoidHom.comp ((inclusion (starM_le K R M)).comp A.subtype)
  have hj : Function.Injective j := e.injective.comp
    ((inclusion_injective (starM_le K R M)).comp A.subtype_injective)
  have hr := (Theory.GroupTheory.primeRank_le_of_injective 3 j hj).trans
    (Matrix.SL2.binary_odd_primeRank_le_one (F := F) (by decide : Odd 3))
  omega

/-- Symplectic star models are excluded by the inherited Sylow and the
perfect rank-two image, uniformly in the field. -/
theorem no_symplectic_star_of_six
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hB : B ≤ M ⊓ K) [Group.IsPerfect B]
    (e6 : (B ⧸ solvableRadical B) ≃* alternatingGroup (Fin 6))
    (T : Sylow 2 G) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hTM : (T : Subgroup G) ≤ M)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 2 < Nat.card F)
    (e : starImage K R K ≃* Matrix.symplecticGroup (Fin 2) F) : False := by
  obtain ⟨U,hU⟩ := starM_contains_sylow (R := R) T hTK hTM
  obtain ⟨A,hAp,hAr⟩ := starM_perfect_three_rank_two_of_six h hB e6
  let := hAp
  let D := (starM K R M).subgroupOf (starImage K R K)
  let j := e.toMonoidHom.comp ((inclusion (starM_le K R M)).comp A.subtype)
  have hj : Function.Injective j := e.injective.comp
    ((inclusion_injective (starM_le K R M)).comp A.subtype_injective)
  have he := Theory.SpecificGroups.SymplecticFour.perfect_odd_rank_two_sylow_overgroup_eq_top
    (by decide : Odd 3) hAr hF (U.mapSurjective e.surjective) (D.map e.toMonoidHom)
    (map_mono hU) j hj (by
      rintro _ ⟨a,rfl⟩
      exact mem_map_of_mem _ a.val.property)
  apply starM_subgroupOf_ne_top h
  exact map_injective e.injective (he.trans (map_top_of_surjective _ e.surjective).symm)

/-- The same full-Sylow argument excludes every nonbinary G2 star model. -/
theorem no_g2_star_of_six
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hB : B ≤ M ⊓ K) [Group.IsPerfect B]
    (e6 : (B ⧸ solvableRadical B) ≃* alternatingGroup (Fin 6))
    (T : Sylow 2 G) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hTM : (T : Subgroup G) ≤ M)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 2 < Nat.card F)
    (e : starImage K R K ≃* Atlas.G2.Model F) : False := by
  obtain ⟨U,hU⟩ := starM_contains_sylow (R := R) T hTK hTM
  obtain ⟨A,hAp,hAr⟩ := starM_perfect_three_rank_two_of_six h hB e6
  let := hAp
  let D := (starM K R M).subgroupOf (starImage K R K)
  let j := e.toMonoidHom.comp ((inclusion (starM_le K R M)).comp A.subtype)
  have hj : Function.Injective j := e.injective.comp
    ((inclusion_injective (starM_le K R M)).comp A.subtype_injective)
  have he := Atlas.G2.PerfectSubgroups.perfect_odd_rank_two_sylow_overgroup_eq_top
    (by decide : Odd 3) hAr hF (U.mapSurjective e.surjective) (D.map e.toMonoidHom)
    (map_mono hU) j hj (by
      rintro _ ⟨a,rfl⟩
      exact mem_map_of_mem _ a.val.property)
  apply starM_subgroupOf_ne_top h
  exact map_injective e.injective (he.trans (map_top_of_surjective _ e.surjective).symm)

/-- The binary derived G2 model is already excluded by the factor five. -/
theorem no_binaryG2_star_of_six
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hB : B ≤ M ⊓ K)
    (e6 : (B ⧸ solvableRadical B) ≃* alternatingGroup (Fin 6))
    (e : starImage K R K ≃* commutator (Atlas.G2.Model (ZMod 2))) : False := by
  have hd := (starM_five_dvd_of_six h hB e6).trans (card_dvd_of_le (starM_le K R M))
  rw [Nat.card_congr e.toEquiv, Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hd
  norm_num at hd

/-- The SL3 source model is excluded through its literal projective map;
the central kernel does not remove the alternating-six section. -/
theorem no_linearThree_star_of_six
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hB : B ≤ M ⊓ K) [Group.IsPerfect B]
    (e6 : (B ⧸ solvableRadical B) ≃* alternatingGroup (Fin 6))
    (T : Sylow 2 G) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hTM : (T : Subgroup G) ≤ M)
    (F : ChapterB.QuasisimpleSource.BinaryField)
    (e : starImage K R K ≃* SL(3,F.Carrier)) : False := by
  by_cases hn : F.degree = 1
  · have hf2 : Nat.card F.Carrier = 2 := by rw [F.card_eq,hn]; rfl
    have hc : Nat.card SL(3,F.Carrier) = 168 := by
      have hs := (center SL(3,F.Carrier)).card_mul_index
      rw [index_eq_card,Atlas.ExceptionalSupport.card_sl_center,Fintype.card_fin,hf2,
        Matrix.PSL3.LinearThree.card_projective,hf2] at hs
      norm_num at hs
      exact hs.symm
    have hd := (starM_five_dvd_of_six h hB e6).trans (card_dvd_of_le (starM_le K R M))
    rw [Nat.card_congr e.toEquiv,hc] at hd
    norm_num at hd
  have hn : 1 < F.degree := by have := F.degree_pos; omega
  let q : starImage K R K →* PSL(3,F.Carrier) :=
    (QuotientGroup.mk' (center SL(3,F.Carrier))).comp e.toMonoidHom
  have hq : Function.Surjective q := (QuotientGroup.mk'_surjective _).comp e.surjective
  have hqk : q.ker ≤ center (starImage K R K) := by
    intro x hx
    have he : e x ∈ center SL(3,F.Carrier) := (QuotientGroup.eq_one_iff _).mp hx
    have hh := (centerCongr e.symm ⟨e x,he⟩).property
    change e.symm (e x) ∈ center (starImage K R K) at hh
    simpa only [e.symm_apply_apply] using hh
  let : Group.IsSolvable q.ker := Group.isSolvable_of_isSolvable_injective
    (inclusion_injective hqk)
  let f := (toStarImage K R).comp (inclusion (hB.trans inf_le_right))
  let : Group.IsSolvable f.ker := six_star_map_ker_solvable h _
  let g := q.comp f
  let : Group.IsSolvable g.ker := isSolvable_comap_of_solvable_ker f q.ker
  let : Group.IsPerfect g.range := Group.IsPerfect.range g
  have hr : 2 ≤ primeRank 3 g.range := image_rank_ge_two e6 g
  obtain ⟨U,hU⟩ := starM_contains_sylow (R := R) T hTK hTM
  let D := (starM K R M).subgroupOf (starImage K R K)
  apply starM_central_image_ne_top h q hqk
  exact Matrix.PSL3.LinearThree.PerfectSubgroups.perfect_odd_rank_two_sylow_overgroup_eq_top
    F.Carrier (by decide : Odd 3) hr hn F.card_eq
    (U.mapSurjective hq) (D.map q) (map_mono hU) g.range.subtype
    g.range.subtype_injective (by
      rintro _ ⟨x,rfl⟩
      obtain ⟨b,hb⟩ := x.property
      change (x : PSL(3,F.Carrier)) ∈ D.map q
      rw [←hb]
      apply mem_map_of_mem q
      exact mem_map_of_mem (QuotientGroup.mk' (starKernel K R)) (hB b.property))

/-- A central A6 quotient is too small for the proper marked intersection. -/
theorem no_central_six_star_of_six
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hB : B ≤ M ⊓ K) [Group.IsPerfect B]
    (e6 : (B ⧸ solvableRadical B) ≃* alternatingGroup (Fin 6))
    (q : starImage K R K →* alternatingGroup (Fin 6))
    (hqk : q.ker ≤ center (starImage K R K)) : False := by
  let : Group.IsSolvable q.ker := Group.isSolvable_of_isSolvable_injective
    (inclusion_injective hqk)
  let f := (toStarImage K R).comp (inclusion (hB.trans inf_le_right))
  let : Group.IsSolvable f.ker := six_star_map_ker_solvable h _
  let g := q.comp f
  let : Group.IsSolvable g.ker := isSolvable_comap_of_solvable_ker f q.ker
  have hg : g.range = ⊤ := by
    apply eq_top_of_card_eq
    have hc : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      rw [nat_card_alternatingGroup]; norm_num [Nat.factorial]
    have hd := image_card_dvd e6 g
    have hl := g.range.card_le_card_group
    rw [hc] at hl ⊢
    exact le_antisymm hl (Nat.le_of_dvd (Nat.card_pos (α := g.range)) hd)
  apply starM_central_image_ne_top h q hqk
  apply top_unique
  rw [←hg]
  rintro _ ⟨b,rfl⟩
  apply mem_map_of_mem q
  exact mem_map_of_mem (QuotientGroup.mk' (starKernel K R)) (hB b.property)

/-- Neither of the small alternating star models can enlarge the residual. -/
theorem no_small_alternating_star_of_six
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hB : B ≤ M ⊓ K) [Group.IsPerfect B]
    (e6 : (B ⧸ solvableRadical B) ≃* alternatingGroup (Fin 6))
    {n : ℕ} (hn : n = 5 ∨ n = 6)
    (e : starImage K R K ≃* alternatingGroup (Fin n)) : False := by
  rcases hn with rfl | rfl
  · have hd := (starM_nine_dvd_of_six h hB e6).trans (card_dvd_of_le (starM_le K R M))
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup] at hd
    norm_num [Nat.factorial] at hd
  · exact no_central_six_star_of_six h hB e6 e.toMonoidHom
      (by rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective]; exact bot_le)

/-- The actual triple-six star model is excluded through its central quotient,
without assuming its C.2.7 plane-stabilizer clause. -/
theorem no_tripleSix_star_of_six
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hB : B ≤ M ⊓ K) [Group.IsPerfect B]
    (e6 : (B ⧸ solvableRadical B) ≃* alternatingGroup (Fin 6))
    (e : (starImage K R K ⧸ center (starImage K R K)) ≃* alternatingGroup (Fin 6)) :
    False := by
  apply no_central_six_star_of_six h hB e6
    (e.toMonoidHom.comp (QuotientGroup.mk' (center (starImage K R K))))
  rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']

omit [Finite G] in
private theorem star_image_normalizes_radical {k : K}
    (hk : (k : G) ∈ normalizer (R : Set G)) :
    (toStarImage K R k : StarQuotient K R) ∈ normalizer (starImage K R R : Set _) := by
  apply (R.subgroupOf (K ⊔ R)).le_normalizer_map (QuotientGroup.mk' (starKernel K R))
  apply mem_map_of_mem
  rw [←subgroupOf_normalizer_eq (show R ≤ K ⊔ R from le_sup_right)]
  exact hk

/-- Direct exclusion of both large alternating star models. The original
radical is normalized by the A6 residual and by the inherited Sylow. -/
theorem no_large_alternating_star_of_six
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hB : B ≤ M ⊓ K) [Group.IsPerfect B]
    (e6 : (B ⧸ solvableRadical B) ≃* alternatingGroup (Fin 6))
    (hBR : B ≤ normalizer (R : Set G))
    (T : Sylow 2 G) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hTR : (T : Subgroup G) ≤ normalizer (R : Set G))
    {n : ℕ} (hn : n = 7 ∨ n = 8)
    (e : starImage K R K ≃* alternatingGroup (Fin n)) : False := by
  obtain ⟨f,hf,hfe⟩ := alternating_star_embedding h (by omega) (by omega) e
  let A := starImage K R K
  let Q := (starImage K R R).map f
  let b := (toStarImage K R).comp (inclusion (hB.trans inf_le_right))
  let g := f.comp (A.subtype.comp b)
  let N := g.range
  have hR : IsPGroup 2 R := by
    have hh := h.setup.radical.isPGroup.map H.subtype
    rwa [map_subgroupOf_eq_of_le h.setup.radical_le] at hh
  have hQ : IsPGroup 2 Q := (hR.comap_subtype.map (QuotientGroup.mk' (starKernel K R))).map f
  have hQne : Q ≠ ⊥ := by
    intro hh
    let : (K.subgroupOf (K ⊔ R)).Normal :=
      normal_subgroupOf_of_le_normalizer (sup_le le_normalizer h.normalizes)
    exact star_radical_ne_bot (source_join_input h)
      (((starImage K R R).map_eq_bot_iff_of_injective hf).mp hh)
  have hN : N ≤ alternatingGroup (Fin n) := by
    rintro _ ⟨x,rfl⟩
    change f (b x) ∈ _
    rw [hfe]
    exact (e (b x)).property
  have hnorm (k : K) (hk : (k : G) ∈ normalizer (R : Set G)) :
      f (toStarImage K R k) ∈ normalizer (Q : Set _) :=
    (starImage K R R).le_normalizer_map f
      (mem_map_of_mem f (star_image_normalizes_radical hk))
  have hNQ : N ≤ normalizer (Q : Set _) := by
    rintro _ ⟨x,rfl⟩
    exact hnorm (inclusion (hB.trans inf_le_right) x) (hBR x.property)
  let : Group.IsSolvable g.ker := by
    dsimp only [g]
    rw [MonoidHom.ker_comp_of_injective _ _ hf,
      MonoidHom.ker_comp_of_injective _ _ A.subtype_injective]
    exact six_star_map_ker_solvable h _
  have h5 : 5 ∣ Nat.card N := (by decide : 5 ∣ 360).trans (image_card_dvd e6 g)
  rcases hn with rfl | rfl
  · have hr : 2 ≤ primeRank 3 N := image_rank_ge_two e6 g
    exact Theory.SpecificGroups.AlternatingSixNormalizer.seven_no_normalized_two Q N hQ hQne hN hNQ h5 hr
  · obtain ⟨U,hU⟩ := Subgroup.NormalSylowQuotientAction.intersection_sylow T K hTK
    let P := (U.mapSurjective (toStarImage_surjective K R)).mapSurjective
      (f := e.toMonoidHom) e.surjective
    apply Theory.SpecificGroups.AlternatingSixNormalizer.eight_no_normalized_two Q N hQ hQne hN hNQ h5 P
    rintro _ ⟨x,⟨y,⟨k,hk,rfl⟩,rfl⟩,rfl⟩
    change (e (toStarImage K R k) : Equiv.Perm (Fin 8)) ∈ normalizer (Q : Set _)
    rw [←hfe]
    apply hnorm
    apply hTR
    change k ∈ (U : Subgroup K) at hk
    rw [hU] at hk
    exact hk

private theorem no_normal_six_image {B D : Type*} [Group B] [Finite B] [Group D] [Finite D]
    (e6 : (B ⧸ solvableRadical B) ≃* alternatingGroup (Fin 6))
    (f : B →* D) [f.range.Normal] [Group.IsSolvable f.ker]
    (e8 : (D ⧸ pCore 2 D) ≃* alternatingGroup (Fin 8)) : False := by
  let q := e8.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 D))
  have hq : Function.Surjective q := e8.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqk : q.ker = pCore 2 D := by
    dsimp only [q]
    rw [MonoidHom.ker_comp_of_injective _ _ e8.injective,QuotientGroup.ker_mk']
  let : Group.IsNilpotent (pCore 2 D) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable q.ker := hqk.symm ▸ inferInstanceAs (Group.IsSolvable (pCore 2 D))
  let g := q.comp f
  let : Group.IsSolvable g.ker := isSolvable_comap_of_solvable_ker f q.ker
  let : g.range.Normal := by
    dsimp only [g]
    rw [MonoidHom.range_comp]
    exact Subgroup.Normal.map inferInstance q hq
  let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect (alternatingGroup (Fin 8)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  rcases (inferInstance : g.range.Normal).eq_bot_or_eq_top with hg | hg
  · have hd := image_card_dvd e6 g
    rw [hg,card_bot] at hd
    norm_num at hd
  · have hr : solvableRadical (alternatingGroup (Fin 8)) = ⊥ := by
      rcases (inferInstance : (solvableRadical (alternatingGroup (Fin 8))).Normal).eq_bot_or_eq_top with hh | hh
      · exact hh
      · let : Group.IsSolvable (alternatingGroup (Fin 8)) :=
          Group.isSolvable_of_surjective
            (f := (solvableRadical (alternatingGroup (Fin 8))).subtype)
            (by intro x; exact ⟨⟨x,hh.symm ▸ mem_top x⟩,rfl⟩)
        exact (Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 8)) inferInstance).elim
    let a := (solvableRadicalQuotientEquiv g (MonoidHom.range_eq_top.mp hg)).trans
      ((QuotientGroup.quotientMulEquivOfEq hr).trans QuotientGroup.quotientBot)
    have he := Nat.card_congr (e6.symm.trans a).toEquiv
    rw [nat_card_alternatingGroup, nat_card_alternatingGroup] at he
    norm_num [Nat.factorial] at he

private theorem no_six_starM_eight_quotient
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hB : B ≤ M ⊓ K) (hn : M ⊓ K ≤ normalizer (B : Set G)) [Group.IsPerfect B]
    (e6 : (B ⧸ solvableRadical B) ≃* alternatingGroup (Fin 6))
    (a : (starM K R M ⧸ pCore 2 (starM K R M)) ≃* alternatingGroup (Fin 8)) : False := by
  let q := QuotientGroup.mk' (starKernel K R)
  let D := M ⊓ K
  let d : D →* starM K R M :=
    (q.comp (inclusion (inf_le_right.trans le_sup_left))).codRestrict _
      (fun x => mem_map_of_mem q x.property)
  have hd : Function.Surjective d := by
    intro y
    obtain ⟨x,hx,he⟩ := y.property
    exact ⟨⟨x.val,hx⟩,Subtype.ext he⟩
  let f : B →* starM K R M := d.comp (inclusion hB)
  have hr : f.range = (B.subgroupOf D).map d := by
    dsimp only [f]
    rw [MonoidHom.range_comp]
    congr 1
    ext x
    constructor
    · rintro ⟨b,rfl⟩
      exact b.property
    · intro hx
      exact ⟨⟨x.val,hx⟩,Subtype.ext rfl⟩
  let : (B.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer hn
  let : f.range.Normal := hr.symm ▸ Subgroup.Normal.map inferInstance d hd
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
  exact no_normal_six_image e6 f a

/-- The original Sylow intersection excludes the SL₅(2) star model directly,
without assuming the C.2.7 alternatives or a flag placement. -/
theorem no_linearFive_star_of_normal_six
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hB : B ≤ M ⊓ K) (hn : M ⊓ K ≤ normalizer (B : Set G)) [Group.IsPerfect B]
    (e6 : (B ⧸ solvableRadical B) ≃* alternatingGroup (Fin 6))
    (T : Sylow 2 G) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hTM : (T : Subgroup G) ≤ M)
    (e5 : starImage K R K ≃* SL(5,ZMod 2)) : False := by
  let e := e5.trans (slEquivLinear 5)
  let D := (starM K R M).subgroupOf (starImage K R K)
  let P := D.map e.toMonoidHom
  obtain ⟨U,hU⟩ := Subgroup.NormalSylowQuotientAction.intersection_sylow T K hTK
  let Q := (U.mapSurjective (toStarImage_surjective K R)).mapSurjective
    (f := e.toMonoidHom) e.surjective
  have hQP : (Q : Subgroup (LinearGroup 5)) ≤ P := by
    rintro x ⟨y,⟨k,hk,rfl⟩,rfl⟩
    apply mem_map_of_mem e.toMonoidHom
    have hkT : (k : G) ∈ (T : Subgroup G) := by
      change k ∈ (U : Subgroup K) at hk
      rw [hU] at hk
      exact hk
    exact mem_map_of_mem (QuotientGroup.mk' (starKernel K R))
      (show (k : G) ∈ M ⊓ K from ⟨hTM hkT,k.property⟩)
  obtain ⟨b,cuts,hP⟩ := BinaryLinear.FiveFlagGeometry.isFlagParabolic_of_sylow_le Q P hQP
  have hproper : P ≠ ⊤ := by
    intro ht
    have hD : D = ⊤ := map_injective e.injective
      (ht.trans (map_top_of_surjective _ e.surjective).symm)
    exact (star_thompson_intersection_from_source h).2.not_ge (subgroupOf_eq_top.mp hD)
  have h5 : 5 ∣ Nat.card (BinaryLinear.FiveFlagGeometry.flagStabilizer b cuts) := by
    rw [←hP,card_map_of_injective e.injective,
      Nat.card_congr (subgroupOfEquivOfLe (starM_le K R M)).toEquiv]
    exact starM_five_dvd_of_six h hB e6
  have hp' : BinaryLinear.FiveFlagGeometry.flagStabilizer b cuts ≠ ⊤ :=
    hP ▸ hproper
  rcases BinaryLinear.FiveFlagGeometry.cuts_eq_singleton_end_of_five_dvd b cuts hp' h5
    with hc | hc
  all_goals
    rw [hc] at hP
    let t := ((subgroupOfEquivOfLe (starM_le K R M)).symm.trans
      (e.subgroupMap D)).trans (MulEquiv.subgroupCongr hP)
    let q := QuotientGroup.congr _ _ t (pCore_map_iso 2 t)
    apply no_six_starM_eight_quotient h hB hn e6
  · exact q.trans ((BinaryLinear.FiveFlagGeometry.MaximalOvergroups.lineQuotientEquiv b).trans
      Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.symm)
  · exact q.trans ((BinaryLinear.FiveFlagGeometry.MaximalOvergroups.hyperplaneQuotientEquiv b).trans
      Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.symm)

end CFSG.Quasithin.ChapterC.C27Source.CentralSix
