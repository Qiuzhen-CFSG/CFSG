module
public import CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape.Star
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.OriginalGeometry
public import Theory.SpecificGroups.PSL3Two.ClassicalSectionObstructions
public import Theory.SpecificGroups.HigherLinear.RadicalParabolics
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.PerfectSpecialLinear
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.SubspaceTransport
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.DefiningSylow
public import Theory.SpecificGroups.Classical.BinaryLinearThreeRank
public import Theory.AtlasPort.LinearGroups.G2.EvenThreeRank

/-!
# The binary linear-three reciprocal model exclusion

The preserved PSL₃(2) section gives an order divisor 168. The reciprocal
odd-rank bound excludes symplectic, G₂, large alternating and SL₅(2)
models. A binary SL₂ image is impossible by its two-subgroup exponent.
In SL₃(2ⁿ), the binary model is too small and every larger model has
order above 8!, so the literal source radical lies inside it. Its
normalizer is parabolic, whose perfect residual maps to binary SL₂
with solvable kernel. This excludes the same preserved section.

Source: Aschbacher--Smith, terminal argument of 4.2.5, printed p.610,
using C.2.7 and the rank bound of 4.2.10(2).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape.LinearThreeModels
variable {B : Type*} [Group B] [Finite B] [Group.IsPerfect B]
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

open Matrix.PSL3.LinearThree in
private theorem no_linearThree_parabolic (e : (B ⧸ pCore 2 B) ≃* Matrix.PSL3Two.PSL)
    (hF : 4 ≤ Nat.card F)
    (f : B →* SL(3,F)) [Group.IsSolvable f.ker]
    (hp : f.range ≤ pointParabolicSL F ∨ f.range ≤ lineParabolicSL F) : False := by
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  rcases hp with hp | hp
  · have hl : f.range ≤ pointLocalSL F := by
      rw [←pointParabolicSL_residual F hF]
      exact le_map_solvableResidual_of_isPerfect _ _ hp
    let j := f.codRestrict (pointLocalSL F) (fun x => hl ⟨x,rfl⟩)
    have hk : j.ker = f.ker := by ext x; exact Subtype.ext_iff
    let : Group.IsSolvable j.ker := hk.symm ▸ inferInstanceAs (Group.IsSolvable f.ker)
    let r := (pointLocalSLCoreQuotientEquiv F).toMonoidHom.comp
      (QuotientGroup.mk' (pCore 2 (pointLocalSL F)))
    let : Group.IsSolvable r.ker := by
      rw [MonoidHom.ker_comp_of_injective _ _ (pointLocalSLCoreQuotientEquiv F).injective,
        QuotientGroup.ker_mk']
      let : Group.IsNilpotent (pCore 2 (pointLocalSL F)) := pCore_isPGroup.isNilpotent
      infer_instance
    exact Matrix.PSL3Two.no_solvable_kernel_rankOne_local e j r
  · have hl : f.range ≤ lineLocalSL F := by
      rw [←lineParabolicSL_residual F hF]
      exact le_map_solvableResidual_of_isPerfect _ _ hp
    let j := f.codRestrict (lineLocalSL F) (fun x => hl ⟨x,rfl⟩)
    have hk : j.ker = f.ker := by ext x; exact Subtype.ext_iff
    let : Group.IsSolvable j.ker := hk.symm ▸ inferInstanceAs (Group.IsSolvable f.ker)
    let r := (lineLocalSLCoreQuotientEquiv F).toMonoidHom.comp
      (QuotientGroup.mk' (pCore 2 (lineLocalSL F)))
    let : Group.IsSolvable r.ker := by
      rw [MonoidHom.ker_comp_of_injective _ _ (lineLocalSLCoreQuotientEquiv F).injective,
        QuotientGroup.ker_mk']
      let : Group.IsNilpotent (pCore 2 (lineLocalSL F)) := pCore_isPGroup.isNilpotent
      infer_instance
    exact Matrix.PSL3Two.no_solvable_kernel_rankOne_local e j r

private theorem no_linearThree_subspace (e : (B ⧸ pCore 2 B) ≃* Matrix.PSL3Two.PSL)
    (hF : 4 ≤ Nat.card F)
    (W : Submodule F (Fin 3 → F)) (hW : W ≠ ⊥) (hWt : W ≠ ⊤)
    (f : B →* Matrix.HigherLinear.parabolicSL W) [Group.IsSolvable f.ker] : False := by
  rcases Matrix.PSL3.LinearThree.SubspaceTransport.exists_parabolic_equiv W hW hWt with ha | ha
  all_goals obtain ⟨a⟩ := ha
  · let j := (Matrix.PSL3.LinearThree.pointParabolicSL F).subtype.comp (a.toMonoidHom.comp f)
    let : Group.IsSolvable j.ker := by
      dsimp only [j]
      rw [MonoidHom.ker_comp_of_injective _ _ (Matrix.PSL3.LinearThree.pointParabolicSL F).subtype_injective,
        MonoidHom.ker_comp_of_injective _ _ a.injective]
      infer_instance
    exact no_linearThree_parabolic e hF j
      (Or.inl (by rintro _ ⟨x,rfl⟩; exact (a (f x)).property))
  · let j := (Matrix.PSL3.LinearThree.lineParabolicSL F).subtype.comp (a.toMonoidHom.comp f)
    let : Group.IsSolvable j.ker := by
      dsimp only [j]
      rw [MonoidHom.ker_comp_of_injective _ _ (Matrix.PSL3.LinearThree.lineParabolicSL F).subtype_injective,
        MonoidHom.ker_comp_of_injective _ _ a.injective]
      infer_instance
    exact no_linearThree_parabolic e hF j
      (Or.inr (by rintro _ ⟨x,rfl⟩; exact (a (f x)).property))

private theorem no_linearThree_radical (e : (B ⧸ pCore 2 B) ≃* Matrix.PSL3Two.PSL) (hF : 4 ≤ Nat.card F)
    (U : Subgroup SL(3,F)) (hU : U.IsPRadical 2)
    (f : B →* SL(3,F)) [Group.IsSolvable f.ker]
    (hn : f.range ≤ normalizer (U : Set SL(3,F))) : False := by
  obtain ⟨k,W,hk,_,_,hW,he⟩ :=
    Matrix.HigherLinear.radical_normalizer_eq_partialFlag (by decide : 2 ≤ 3) U hU
  let i : Fin k := ⟨0,hk⟩
  have hf : f.range ≤ Matrix.HigherLinear.parabolicSL (W i) :=
    hn.trans (he.le.trans (iInf_le _ i))
  let j := f.codRestrict _ (fun x => hf ⟨x,rfl⟩)
  have hj : j.ker = f.ker := by ext x; exact Subtype.ext_iff
  let : Group.IsSolvable j.ker := hj.symm ▸ inferInstanceAs (Group.IsSolvable f.ker)
  exact no_linearThree_subspace e hF (W i) (hW i).1 (hW i).2 j

open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source

/-- The literal reciprocal star image cannot retain a PSL₃(2) section
while its component has three-rank at most one. -/
theorem no_source_linearThree_normalizing_radical
    {G : Type*} [Group G] [Finite G] {H R M K J : Subgroup G}
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hJ : J ≤ M ⊓ K) (hn : J ≤ normalizer (R : Set G))
    [Group.IsPerfect J]
    (e : (J ⧸ pCore 2 J) ≃* Matrix.PSL3Two.PSL)
    (hr : primeRank 3 (starImage K R K) ≤ 1) : False := by
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup (J ⧸ pCore 2 J) := e.isSimpleGroup
  let E := starImage K R J
  let C := starImage K R K
  let P := starM K R M
  have hEK : E ≤ C := map_mono (comap_mono (hJ.trans inf_le_right))
  have hEP : E ≤ P := map_mono (comap_mono hJ)
  obtain ⟨a,_⟩ := starSubgroupMap_coreQuotient_equiv h (hJ.trans inf_le_right)
  let b : (E ⧸ pCore 2 E) ≃* Matrix.PSL3Two.PSL := a.symm.trans e
  have hd : 168 ∣ Nat.card C := by
    rw [←Matrix.PSL3Two.card_PSL,←Nat.card_congr b.toEquiv]
    exact (card_quotient_dvd_card _).trans (card_dvd_of_le hEK)
  have hlo : 168 ≤ Nat.card P := Nat.le_of_dvd Nat.card_pos (by
    rw [←Matrix.PSL3Two.card_PSL,←Nat.card_congr b.toEquiv]
    exact (card_quotient_dvd_card _).trans (card_dvd_of_le hEP))
  have hPC : P < C := (star_thompson_intersection_from_source h).2
  let : Group.IsPerfect E := Group.IsPerfect.ofSurjective
    (f := starSubgroupMap K R J (hJ.trans inf_le_right))
    (starSubgroupMap_surjective K R J (hJ.trans inf_le_right))
  have hNR : E ≤ normalizer (starImage K R R : Set (StarQuotient K R)) := by
    let D := K ⊔ R
    let q := QuotientGroup.mk' (starKernel K R)
    have hJD : J.subgroupOf D ≤ normalizer (R.subgroupOf D : Set D) := by
      rw [←subgroupOf_normalizer_eq (show R ≤ D from le_sup_right)]
      exact comap_mono hn
    exact (map_mono hJD).trans (le_normalizer_map q)
  cases star_model_from_source h with
  | linearTwo F c =>
    let f := c.toMonoidHom.comp (inclusion hEK)
    let : Group.IsSolvable f.ker := by
      rw [f.ker_eq_bot (c.injective.comp (inclusion_injective hEK))]
      infer_instance
    exact Matrix.SpecialLinearGroup.no_binaryLinearTwo_of_solvable_kernel b f
  | linearThree F c =>
    by_cases hF : Nat.card F.Carrier = 2
    · have hc : Nat.card C = 168 := by
        rw [Nat.card_congr c.toEquiv,
          Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear,hF]
        norm_num
      exact hPC.ne (eq_of_le_of_card_ge hPC.le (hc.le.trans hlo))
    have hF4 : 4 ≤ Nat.card F.Carrier := by
      rw [F.card_eq] at hF ⊢
      have hn : 2 ≤ F.degree := by
        have hp := F.degree_pos
        by_contra hh
        have he : F.degree = 1 := by omega
        simp [he] at hF
      exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hn
    have hlarge : 40320 < Nat.card C := by
      rw [Nat.card_congr c.toEquiv,
        Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear]
      have hq3 : 64 ≤ Nat.card F.Carrier ^ 3 := by
        exact (pow_le_pow_left' hF4 3).trans_eq (by norm_num)
      have hq2 : 16 ≤ Nat.card F.Carrier ^ 2 := by
        exact (pow_le_pow_left' hF4 2).trans_eq (by norm_num)
      have hm := Nat.mul_le_mul (Nat.mul_le_mul hq3
        (by omega : 63 ≤ Nat.card F.Carrier ^ 3 - 1))
        (by omega : 15 ≤ Nat.card F.Carrier ^ 2 - 1)
      norm_num at hm
      omega
    have hU := (star_intersection_placement_from_source_of_large_order h hlarge).1
    let f := c.toMonoidHom.comp (inclusion hEK)
    let : Group.IsSolvable f.ker := by
      rw [f.ker_eq_bot (c.injective.comp (inclusion_injective hEK))]
      infer_instance
    apply no_linearThree_radical b hF4
      ((((starImage K R R).subgroupOf C)).map c.toMonoidHom) (hU.map_equiv c) f
    rw [MonoidHom.range_comp,←map_equiv_normalizer_eq]
    apply map_mono
    rintro _ ⟨x,rfl⟩
    apply mem_normalizer_iff.mpr
    intro u
    exact mem_normalizer_iff.mp (hNR x.property) (u : StarQuotient K R)
  | symplectic F hF c =>
    have htwo := Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.symplectic
      (F := F.Carrier)
    have hu := Theory.GroupTheory.primeRank_le_of_injective 3
      (commutator (Matrix.symplecticGroup (Fin 2) F.Carrier)).subtype
      (commutator (Matrix.symplecticGroup (Fin 2) F.Carrier)).subtype_injective
    have hh := htwo.trans hu
    rw [←primeRank_equiv 3 c] at hh
    omega
  | g2 F hF c =>
    have hh := Atlas.G2.EvenThreeRank.two_le_primeRank (K := F.Carrier)
    rw [←primeRank_equiv 3 c] at hh
    omega
  | g2DerivedTwo c =>
    have hh := Atlas.G2.EvenThreeRank.two_le_primeRank_derived
    rw [←primeRank_equiv 3 c] at hh
    omega
  | alternating n hn c =>
    rcases hn with rfl | rfl | rfl | rfl
    · rw [Nat.card_congr c.toEquiv,nat_card_alternatingGroup] at hd
      norm_num [Nat.factorial] at hd
    · have hh := alternatingGroup.TwoThreeCycles.two_le_primeRank (n := 6) (by decide)
      rw [←primeRank_equiv 3 c] at hh
      omega
    · have hh := alternatingGroup.TwoThreeCycles.two_le_primeRank (n := 7) (by decide)
      rw [←primeRank_equiv 3 c] at hh
      omega
    · have hh := alternatingGroup.TwoThreeCycles.two_le_primeRank (n := 8) (by decide)
      rw [←primeRank_equiv 3 c] at hh
      omega
  | linearFiveTwo c =>
    have hh := Theory.SpecificGroups.Classical.BinaryLinearThreeRank.two_le_primeRank
      (by decide : 4 ≤ 5)
    rw [←primeRank_equiv 3 c] at hh
    omega
  | tripleSix ez c =>
    rw [card_eq_card_quotient_mul_card_subgroup (center C),
      Nat.card_congr c.toEquiv,Nat.card_congr ez.toEquiv,nat_card_alternatingGroup] at hd
    norm_num [Nat.factorial] at hd

end CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape.LinearThreeModels
