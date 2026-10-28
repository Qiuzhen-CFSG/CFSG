module
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.BinaryLinearSixExclusion
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.PerfectSubgroups
public import Theory.AtlasPort.LinearGroups.G2.PerfectSubgroups
public import Theory.GroupTheory.PerfectCentralCoverEmbeddingRigidity

/-!
# Direct source-model exclusions for a six-point residual

The original C.2.7 input supplies a proper marked star intersection. An
inherited ambient Sylow maps to a full Sylow of the star component inside
that intersection. The perfect A6 two-core section survives the solvable
star kernel, and the actual central projection in the SL3 case. The proved
Sylow-overgroup geometry excludes every binary SL3, Sp4 and nonbinary G2
model. Rank and order exclude SL2, binary derived G2, A5 and the central
A6 models, including the triple cover.

No C.2.7 alternative or universal source implication is assumed. The
literal fixed-coset applications belong to SourceAlternatingSeven's
LocalAnalysisSylowResidualsComponentsSourceModels extension.

Source: Aschbacher--Smith C.2.7, printed pp.145--147, and 3.3.22, p.597.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {H K R M B : Subgroup G}

/-- The original full Sylow maps into the literal marked intersection. -/
theorem starM_contains_sylow (T : Sylow 2 G)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hTM : (T : Subgroup G) ≤ M) :
    ∃ U : Sylow 2 (starImage K R K),
      (U : Subgroup _) ≤ (starM K R M).subgroupOf (starImage K R K) := by
  obtain ⟨U,hU⟩ := Subgroup.NormalSylowQuotientAction.intersection_sylow T K hTK
  refine ⟨U.mapSurjective (toStarImage_surjective K R),?_⟩
  rintro x ⟨k,hk,rfl⟩
  have hkT : (k : G) ∈ (T : Subgroup G) := by
    change k ∈ (U : Subgroup K) at hk
    rw [hU] at hk
    exact hk
  exact mem_map_of_mem (QuotientGroup.mk' (starKernel K R))
    (show (k : G) ∈ M ⊓ K from ⟨hTM hkT,k.property⟩)

/-- The marked intersection is proper in the actual star component. -/
theorem starM_subgroupOf_ne_top (h : Input KnownSimple.IsKnownSimple H R M K) :
    (starM K R M).subgroupOf (starImage K R K) ≠ ⊤ := by
  intro ht
  exact (star_thompson_intersection_from_source h).2.not_ge (subgroupOf_eq_top.mp ht)

private theorem six_rank {D : Type*} [Group D] [Finite D]
    (e : (D ⧸ pCore 2 D) ≃* alternatingGroup (Fin 6)) : primeRank 3 D = 2 := by
  rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 D) pCore_isPGroup,
    primeRank_equiv 3 e,
    GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 6 3 (by decide) (by decide)]

/-- Rank-one star models cannot contain the surviving A6 image. -/
theorem no_linearTwo_star_of_six
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hB : B ≤ M ⊓ K) [Group.IsPerfect B]
    (e6 : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))
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
    (e6 : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))
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
    (e6 : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))
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
    (e6 : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))
    (e : starImage K R K ≃* commutator (Atlas.G2.Model (ZMod 2))) : False := by
  have hd := (starM_five_dvd_of_six h hB e6).trans (card_dvd_of_le (starM_le K R M))
  rw [Nat.card_congr e.toEquiv, Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hd
  norm_num at hd

/-- Restriction of the original star map has a solvable kernel. -/
theorem six_star_map_ker_solvable
    (h : Input KnownSimple.IsKnownSimple H R M K) (hBK : B ≤ K) :
    Group.IsSolvable ((toStarImage K R).comp (inclusion hBK)).ker := by
  let f := (toStarImage K R).comp (inclusion hBK)
  let j : f.ker →* (toStarImage K R).ker :=
    { toFun := fun b => ⟨inclusion hBK b.val,b.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := fun x y hh =>
    Subtype.ext (inclusion_injective hBK (congrArg Subtype.val hh))
  let : Group.IsSolvable (toStarImage K R).ker := toStarImage_ker_solvable_from_source h
  exact Group.isSolvable_of_isSolvable_injective hj

omit [Finite G] in
private theorem perfect_star (h : Input KnownSimple.IsKnownSimple H R M K) :
    Group.IsPerfect (starImage K R K) := by
  let : IsQuasisimple (K ⧸ pCore 2 K) := h.quasisimple
  exact Group.IsPerfect.ofSurjective (coreToStar_surjective h.normalizes)

/-- Central projection preserves properness of the marked intersection. -/
theorem starM_central_image_ne_top
    (h : Input KnownSimple.IsKnownSimple H R M K)
    {D : Type*} [Group D] (q : starImage K R K →* D)
    (hq : q.ker ≤ center (starImage K R K)) :
    ((starM K R M).subgroupOf (starImage K R K)).map q ≠ ⊤ := by
  let A := (starM K R M).subgroupOf (starImage K R K)
  let : Group.IsPerfect (starImage K R K) := perfect_star h
  intro ht
  have hs : Function.Surjective (q.comp A.subtype) := by
    rw [←MonoidHom.range_eq_top, MonoidHom.range_comp, range_subtype]
    exact ht
  have ha := PerfectCentralCovering.surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
    q A.subtype hs hq
  exact starM_subgroupOf_ne_top h (eq_top_iff.mpr fun x _ => by
    obtain ⟨a,rfl⟩ := ha x
    exact a.property)

/-- The SL3 source model is excluded through its literal projective map;
the central kernel does not remove the simple A6 section. -/
theorem no_linearThree_star_of_six
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hB : B ≤ M ⊓ K) [Group.IsPerfect B]
    (e6 : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))
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
  let : Group.IsSolvable g.rangeRestrict.ker := by
    have he : g.rangeRestrict.ker = g.ker := by ext x; exact Subtype.ext_iff
    exact he.symm ▸ inferInstanceAs (Group.IsSolvable g.ker)
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (B ⧸ pCore 2 B) := e6.isSimpleGroup
  let : Group.IsPerfect g.range := Group.IsPerfect.range g
  have hr : 2 ≤ primeRank 3 g.range := by
    have hh := PerfectCoreTwoExtension.odd_rank_le_of_solvable_kernel
      (by decide : Odd 3) g.rangeRestrict
    rwa [six_rank e6] at hh
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

/-- A solvable kernel preserves the order divisor of the simple A6 section. -/
theorem six_card_dvd_range {D A : Type*} [Group D] [Finite D] [Group A] [Finite A]
    [Group.IsPerfect D] (e6 : (D ⧸ pCore 2 D) ≃* alternatingGroup (Fin 6))
    (f : D →* A) [Group.IsSolvable f.ker] : 360 ∣ Nat.card f.range := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (D ⧸ pCore 2 D) := e6.isSimpleGroup
  have hk := PerfectCoreTwoExtension.solvable_ker_le_core f
  let q : (D ⧸ f.ker) →* (D ⧸ pCore 2 D) :=
    QuotientGroup.lift f.ker (QuotientGroup.mk' (pCore 2 D)) (by
      simpa only [QuotientGroup.ker_mk'] using hk)
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨d,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 D) x
    exact ⟨QuotientGroup.mk' f.ker d,rfl⟩
  have hd := card_dvd_of_surjective q hq
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv,
    Nat.card_congr e6.toEquiv,nat_card_alternatingGroup] at hd
  norm_num [Nat.factorial] at hd
  exact hd

/-- A central A6 quotient is too small for the proper marked intersection. -/
theorem no_central_six_star_of_six
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hB : B ≤ M ⊓ K) [Group.IsPerfect B]
    (e6 : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))
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
    have hd := six_card_dvd_range e6 g
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
    (e6 : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))
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
    (e6 : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))
    (e : (starImage K R K ⧸ center (starImage K R K)) ≃* alternatingGroup (Fin 6)) :
    False := by
  apply no_central_six_star_of_six h hB e6
    (e.toMonoidHom.comp (QuotientGroup.mk' (center (starImage K R K))))
  rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']

end CFSG.Quasithin.ChapterC.C27Source
