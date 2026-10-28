module
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.SixStarModels
public import Theory.SpecificGroups.PSL3Two.ClassicalSectionObstructions
public import Theory.AtlasPort.LinearGroups.G2.SevenSylowOvergroupTransport

/-!
# C.2.7 star models containing the central-line PSL₃(2) section

The literal marked star intersection retains the factor 168 from the
perfect residual with PSL₃(2) two-core quotient, since the star kernel is
solvable. This excludes the small rows. The inherited full Sylow and the
rank-one parabolic obstruction exclude the nonbinary symplectic and G₂
rows; the binary G₂ derived row is excluded by its actual seven-divisible
Sylow-overgroup theorem. The full binary G₂ group is not perfect.

Every comparison uses the original star map and marked intersection.
The A₈ natural row remains for the augmentation/transvection argument in
LocalAnalysisNaturalFourExclusionSelection, the actual 12.3.3 consumer.
Source: Aschbacher–Smith, C.2.7, B.5.1(2), and Lemma 12.3.3, p.808.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {H K R M B : Subgroup G}

private theorem linearThree_card_dvd_range {D A : Type*} [Group D] [Finite D]
    [Group A] [Finite A] [Group.IsPerfect D]
    (e : (D ⧸ pCore 2 D) ≃* Matrix.PSL3Two.PSL)
    (f : D →* A) [Group.IsSolvable f.ker] : 168 ∣ Nat.card f.range := by
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup (D ⧸ pCore 2 D) := e.isSimpleGroup
  have hk := PerfectCoreTwoExtension.solvable_ker_le_core f
  let q : (D ⧸ f.ker) →* (D ⧸ pCore 2 D) :=
    QuotientGroup.lift f.ker (QuotientGroup.mk' (pCore 2 D)) (by
      simpa only [QuotientGroup.ker_mk'] using hk)
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨d,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 D) x
    exact ⟨QuotientGroup.mk' f.ker d,rfl⟩
  have hd := card_dvd_of_surjective q hq
  rwa [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv,
    Nat.card_congr e.toEquiv,Matrix.PSL3Two.card_PSL] at hd

theorem starM_card_dvd_of_linearThree
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hB : B ≤ M ⊓ K) [Group.IsPerfect B]
    (e : (B ⧸ pCore 2 B) ≃* Matrix.PSL3Two.PSL) :
    168 ∣ Nat.card (starM K R M) := by
  let f := (toStarImage K R).comp (inclusion (hB.trans inf_le_right))
  let : Group.IsSolvable f.ker := six_star_map_ker_solvable h _
  let D := (starM K R M).subgroupOf (starImage K R K)
  have hf : f.range ≤ D := by
    rintro _ ⟨b,rfl⟩
    exact mem_map_of_mem (QuotientGroup.mk' (starKernel K R)) (hB b.property)
  have hd := (linearThree_card_dvd_range e f).trans (card_dvd_of_le hf)
  rwa [Nat.card_congr (subgroupOfEquivOfLe (starM_le K R M)).toEquiv] at hd

theorem no_small_star_of_linearThree
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hB : B ≤ M ⊓ K) [Group.IsPerfect B]
    (e : (B ⧸ pCore 2 B) ≃* Matrix.PSL3Two.PSL)
    (hcard : Nat.card (starImage K R K) ≤ 168) : False := by
  have hd := starM_card_dvd_of_linearThree h hB e
  have hlo : 168 ≤ Nat.card (starM K R M) := Nat.le_of_dvd Nat.card_pos hd
  exact (star_thompson_intersection_from_source h).2.ne
    (eq_of_le_of_card_ge (starM_le K R M) (hcard.trans hlo))

theorem no_star_of_not_seven_dvd
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hB : B ≤ M ⊓ K) [Group.IsPerfect B]
    (e : (B ⧸ pCore 2 B) ≃* Matrix.PSL3Two.PSL)
    (hcard : ¬7 ∣ Nat.card (starImage K R K)) : False := by
  exact hcard ((by decide : 7 ∣ 168).trans
    ((starM_card_dvd_of_linearThree h hB e).trans (card_dvd_of_le (starM_le K R M))))

theorem no_linearTwo_star_of_linearThree
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hB : B ≤ M ⊓ K) [Group.IsPerfect B]
    (e : (B ⧸ pCore 2 B) ≃* Matrix.PSL3Two.PSL)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (a : starImage K R K ≃* SL(2,F)) : False := by
  let f := (toStarImage K R).comp (inclusion (hB.trans inf_le_right))
  let : Group.IsSolvable f.ker := six_star_map_ker_solvable h _
  let j := a.toMonoidHom.comp f
  let : Group.IsSolvable j.ker := by
    dsimp only [j]
    rw [MonoidHom.ker_comp_of_injective _ _ a.injective]
    infer_instance
  exact Matrix.SpecialLinearGroup.no_binaryLinearTwo_of_solvable_kernel e j

theorem no_symplectic_star_of_linearThree
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hB : B ≤ M ⊓ K) [Group.IsPerfect B]
    (e : (B ⧸ pCore 2 B) ≃* Matrix.PSL3Two.PSL)
    (T : Sylow 2 G) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hTM : (T : Subgroup G) ≤ M)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 2 < Nat.card F)
    (a : starImage K R K ≃* Matrix.symplecticGroup (Fin 2) F) : False := by
  obtain ⟨U,hU⟩ := starM_contains_sylow (R := R) T hTK hTM
  let D := (starM K R M).subgroupOf (starImage K R K)
  let f := (toStarImage K R).comp (inclusion (hB.trans inf_le_right))
  let : Group.IsSolvable f.ker := six_star_map_ker_solvable h _
  let j := a.toMonoidHom.comp f
  let : Group.IsSolvable j.ker := by
    dsimp only [j]
    rw [MonoidHom.ker_comp_of_injective _ _ a.injective]
    infer_instance
  have hj : j.range ≤ D.map a.toMonoidHom := by
    rintro _ ⟨b,rfl⟩
    exact mem_map_of_mem _ (mem_map_of_mem (QuotientGroup.mk' (starKernel K R)) (hB b.property))
  have ht := Theory.SpecificGroups.SymplecticFour.linearThree_section_sylow_overgroup_eq_top
    e hF (U.mapSurjective a.surjective) (D.map a.toMonoidHom) (map_mono hU) j hj
  exact starM_subgroupOf_ne_top h
    (map_injective a.injective (ht.trans (map_top_of_surjective _ a.surjective).symm))

theorem no_g2_star_of_linearThree
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hB : B ≤ M ⊓ K) [Group.IsPerfect B]
    (e : (B ⧸ pCore 2 B) ≃* Matrix.PSL3Two.PSL)
    (T : Sylow 2 G) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hTM : (T : Subgroup G) ≤ M)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 2 < Nat.card F)
    (a : starImage K R K ≃* Atlas.G2.Model F) : False := by
  obtain ⟨U,hU⟩ := starM_contains_sylow (R := R) T hTK hTM
  let D := (starM K R M).subgroupOf (starImage K R K)
  let f := (toStarImage K R).comp (inclusion (hB.trans inf_le_right))
  let : Group.IsSolvable f.ker := six_star_map_ker_solvable h _
  let j := a.toMonoidHom.comp f
  let : Group.IsSolvable j.ker := by
    dsimp only [j]
    rw [MonoidHom.ker_comp_of_injective _ _ a.injective]
    infer_instance
  have hj : j.range ≤ D.map a.toMonoidHom := by
    rintro _ ⟨b,rfl⟩
    exact mem_map_of_mem _ (mem_map_of_mem (QuotientGroup.mk' (starKernel K R)) (hB b.property))
  have ht := Atlas.G2.linearThree_section_sylow_overgroup_eq_top
    e hF (U.mapSurjective a.surjective) (D.map a.toMonoidHom) (map_mono hU) j hj
  exact starM_subgroupOf_ne_top h
    (map_injective a.injective (ht.trans (map_top_of_surjective _ a.surjective).symm))

theorem no_binarySymplectic_star_of_linearThree
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hB : B ≤ M ⊓ K) [Group.IsPerfect B]
    (e : (B ⧸ pCore 2 B) ≃* Matrix.PSL3Two.PSL)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2)
    (a : starImage K R K ≃* Matrix.symplecticGroup (Fin 2) F) : False := by
  let b := a.trans ((Theory.SpecificGroups.SymplecticFour.Binary.fieldEquivSp
    (Theory.SpecificGroups.SymplecticFour.Binary.fieldEquivZModTwo F hF)).trans
      Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm)
  apply no_star_of_not_seven_dvd h hB e
  rw [Nat.card_congr b.toEquiv]
  norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]

omit [Finite G] in
theorem no_full_binaryG2_star
    (h : Input KnownSimple.IsKnownSimple H R M K)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2)
    (a : starImage K R K ≃* Atlas.G2.Model F) : False := by
  let : IsQuasisimple (K ⧸ pCore 2 K) := h.quasisimple
  let : Group.IsPerfect (starImage K R K) :=
    Group.IsPerfect.ofSurjective (coreToStar_surjective h.normalizes)
  let : Group.IsPerfect (Atlas.G2.Model F) :=
    Group.IsPerfect.ofSurjective (f := a.toMonoidHom) a.surjective
  have hc := Atlas.G2.DerivedEvenOrder.card_derived_binary hF
  rw [Group.IsPerfect.commutator_eq_top,card_top,Atlas.G2.card_Model,hF] at hc
  norm_num at hc

theorem no_binaryG2_star_of_linearThree
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hB : B ≤ M ⊓ K) [Group.IsPerfect B]
    (e : (B ⧸ pCore 2 B) ≃* Matrix.PSL3Two.PSL)
    (T : Sylow 2 G) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hTM : (T : Subgroup G) ≤ M)
    (a : starImage K R K ≃* commutator (Atlas.G2.Model (ZMod 2))) : False := by
  let C := commutator (Atlas.G2.Model (ZMod 2))
  obtain ⟨U,hU⟩ := starM_contains_sylow (R := R) T hTK hTM
  let D := (starM K R M).subgroupOf (starImage K R K)
  let P := U.mapSurjective (f := a.toMonoidHom) a.surjective
  let E := D.map a.toMonoidHom
  have hPE : (P : Subgroup C) ≤ E := map_mono hU
  have h7 : 7 ∣ Nat.card E := by
    rw [←Nat.card_congr (D.equivMapOfInjective a.toMonoidHom a.injective).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe (starM_le K R M)).toEquiv]
    exact (by decide : 7 ∣ 168).trans (starM_card_dvd_of_linearThree h hB e)
  have ht' : E = ⊤ :=
    Atlas.G2.BinaryParabolicPair.SevenSylowOvergroups.eq_top_of_sylow_of_seven_dvd P E hPE h7
  exact starM_subgroupOf_ne_top h
    (map_injective a.injective (ht'.trans (map_top_of_surjective _ a.surjective).symm))
end CFSG.Quasithin.ChapterC.C27Source
