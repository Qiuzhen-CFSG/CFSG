module
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.StarModels
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Symplectic
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.LinearThreePrimeRank
public import Theory.GroupTheory.CComponent.SylowOvergroupUniqueTop
public import Theory.GroupTheory.CComponent.TwoRankObstruction
public import Theory.GroupTheory.ComponentLocalPrimeFree
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.SylowComponentUnique
public import Theory.SpecificGroups.SymplecticFour.SylowComponentUnique
public import Theory.SpecificGroups.G2.SylowComponentUnique
public import Theory.SpecificGroups.BinaryLinear.SylowComponentUnique
public import Theory.SpecificGroups.BinaryLinear.ThreeFreeSylowOvergroups
public import Theory.SpecificGroups.G2Even.BinaryDerivedSolvableOvergroups
public import Theory.SpecificGroups.Classical.EvenDerivedThree

/-!
# Full-Sylow tests for the actual C.2.7 star models

Every star model has at most one C-component in each full-Sylow overgroup.
For the central covers this follows from the top C-component and conjugate
parabolic coverage, rather than an assumption of simplicity. Each model is
also either smaller than the first Suzuki group or has a cubic divisor in
every normalized local C-component. The latter test uses the actual local
core quotients, or solvability of three-free full-Sylow overgroups.

`Chapter10.PointControl.HalfUniqueness.Components.ConstrainedStar` applies
both tests to the literal C.2.7 star map and discharges the constrained
containing-component branch of 10.2.6. No cubic-divisor condition is imposed
on the original source factor.
Source: Aschbacher--Smith A.3.12, C.2.7 and 10.2.6.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.C27Source.StarModels
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings

/-- Cubic divisibility in a local component normalized by its full ambient Sylow. -/
@[expose] def NormalizedLocalCubic (X : Type*) [Group X] : Prop :=
  ∀ (S : Sylow 2 X) (A : Subgroup X), A ∈ localCComponents S →
    (S : Subgroup X) ≤ normalizer (A : Set X) → 3 ∣ Nat.card A

private theorem cubic_of_surjective {X Y : Type*} [Group X] [Group Y] [Finite X]
    (q : X →* Y) (hq : Function.Surjective q) [Group.IsSolvable q.ker]
    (hc : NormalizedLocalCubic Y) : NormalizedLocalCubic X := by
  intro S A hA hnA
  have hm := Chapter1.Section02.localCComponents_map_of_solvable_ker hA q
  exact (hc (S.mapSurjective hq) (A.map q) hm
    ((map_mono hnA).trans (le_normalizer_map q))).trans
    (card_dvd_of_surjective (q.subgroupMap A) (q.subgroupMap_surjective A))

private theorem cubic_of_equiv {X Y : Type*} [Group X] [Group Y] [Finite X]
    (e : X ≃* Y) (hc : NormalizedLocalCubic Y) : NormalizedLocalCubic X := by
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot e.injective]
    infer_instance
  exact cubic_of_surjective e.toMonoidHom e.surjective hc

private theorem cubic_of_three_free_solvable {X : Type*} [Group X] [Finite X]
    (hf : ∀ (S : Sylow 2 X) (P : Subgroup X), (S : Subgroup X) ≤ P →
      ¬ 3 ∣ Nat.card P → Group.IsSolvable P) : NormalizedLocalCubic X := by
  intro S A hA hnA
  by_contra h3
  have hS3 : ¬ 3 ∣ Nat.card S := by
    obtain ⟨n,he⟩ := S.isPGroup'.exists_card_eq
    rw [he]
    exact fun h => (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h)
  let := hf S (A ⊔ (S : Subgroup X)) le_sup_right
    (not_dvd_card_sup_of_normalizes Nat.prime_three A S hnA h3 hS3)
  exact hA.not_isSolvable inferInstance

private theorem cubic_of_solvable_proper {X : Type*} [Group X] [Finite X]
    (hf : SolvableSylowOvergroups X) (h3 : 3 ∣ Nat.card X) : NormalizedLocalCubic X := by
  apply cubic_of_three_free_solvable
  intro S P hSP hP
  apply hf S P hSP
  intro he
  rw [he,card_top] at hP
  exact hP h3

private theorem sl2_cubic (F : Type*) [Field F] [Finite F] [CharP F 2] :
    3 ∣ Nat.card SL(2,F) :=
  ((Theory.SpecificGroups.Classical.EvenDerivedThree.three_dvd_card_psl_commutator
    (F := F) (i := (0 : Fin 2)) (j := 1) (by decide)).trans (card_subgroup_dvd_card _)).trans
      (card_quotient_dvd_card _)

private theorem psl3_unique {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (ht : (⊤ : Subgroup PSL(3,F)).IsCComponent) : SylowOvergroupComponentUnique PSL(3,F) := by
  by_cases h1 : n = 1
  · exact .of_top_component_and_solvable_proper ht
      (Matrix.PSL3Two.solvableSylowOvergroups_projective_of_card_two (by simpa [h1] using hF))
  apply SylowOvergroupComponentUnique.of_top_component_and_conjugate_cover ht
  intro S P hSP hP
  obtain ⟨g,hg⟩ := Matrix.PSL3.LinearThree.UnipotentOvergroups.proper_sylow_overgroup_parabolic_cover
    F hn hF S P hSP hP
  have hfour : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ n)
  rcases hg with hg | hg
  · exact ⟨g,_,hg,Matrix.PSL3.LinearThree.pointParabolic_sylow_component_unique F hfour⟩
  · exact ⟨g,_,hg,Matrix.PSL3.LinearThree.lineParabolic_sylow_component_unique F hfour⟩

private theorem psl3_cubic {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n) : NormalizedLocalCubic PSL(3,F) := by
  have h3 : 3 ∣ Nat.card PSL(3,F) :=
    (Theory.SpecificGroups.Classical.EvenDerivedThree.three_dvd_card_psl_commutator
      (F := F) (i := (0 : Fin 3)) (j := 1) (by decide)).trans (card_subgroup_dvd_card _)
  by_cases h1 : n = 1
  · exact cubic_of_solvable_proper
      (Matrix.PSL3Two.solvableSylowOvergroups_projective_of_card_two (by simpa [h1] using hF)) h3
  intro S A hA _
  by_cases he : A = ⊤
  · simpa [he] using h3
  obtain ⟨a⟩ := linear_three_local_core_quotient hF (by omega) S A hA he
  exact ((Nat.card_congr a.toEquiv).symm ▸ sl2_cubic F).trans (card_quotient_dvd_card _)

private theorem sp4_unique {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (ht : (⊤ : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F)).IsCComponent) :
    SylowOvergroupComponentUnique (Theory.SpecificGroups.SymplecticFour.Sp F) := by
  apply SylowOvergroupComponentUnique.of_top_component_and_conjugate_cover ht
  intro S P hSP hP
  have htwo : 2 < Nat.card F := by
    rw [hF]
    exact (show (2 : ℕ)^1 < 2^n from Nat.pow_lt_pow_right (by decide) hn)
  obtain ⟨g,hg⟩ := Theory.SpecificGroups.SymplecticFour.ThreeResidualPlacement.proper_sylow_overgroup_parabolic_cover
    htwo S P hSP hP
  rcases hg with hg | hg
  · exact ⟨g,_,hg,Theory.SpecificGroups.SymplecticFour.pointParabolic_sylow_component_unique F hF hn⟩
  · exact ⟨g,_,hg,Theory.SpecificGroups.SymplecticFour.planeParabolic_sylow_component_unique F hF hn⟩

private theorem sp4_cubic {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n) :
    NormalizedLocalCubic (Theory.SpecificGroups.SymplecticFour.Sp F) := by
  intro S A hA _
  by_cases he : A = ⊤
  · rw [he,card_top]
    exact Theory.SpecificGroups.Classical.EvenDerivedThree.three_dvd_card_sp4_commutator.trans
      (card_subgroup_dvd_card _)
  obtain ⟨g,hg⟩ := FiveLocalFF.symplectic_local_placement hF hn S A hA he
  let a := (MulAut.conj g).subgroupMap A
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  have hq : Nonempty (((A.map (MulAut.conj g).toMonoidHom) ⧸
      pCore 2 (A.map (MulAut.conj g).toMonoidHom)) ≃* SL(2,F)) := by
    rcases hg with hg | hg
    · rw [hg]
      exact ⟨Theory.SpecificGroups.SymplecticFour.pointLocalCoreQuotientEquiv hF hn⟩
    · rw [hg]
      exact ⟨Theory.SpecificGroups.SymplecticFour.planeLocalCoreQuotientEquiv hF hn⟩
  have hd : 3 ∣ Nat.card (A ⧸ pCore 2 A) :=
    (Nat.card_congr (aq.trans hq.some).toEquiv).symm ▸ sl2_cubic F
  exact hd.trans (card_quotient_dvd_card _)

private theorem g2_unique {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hq : 2 < Nat.card F) (ht : (⊤ : Subgroup (Atlas.G2.Model F)).IsCComponent) :
    SylowOvergroupComponentUnique (Atlas.G2.Model F) := by
  apply SylowOvergroupComponentUnique.of_top_component_and_conjugate_cover ht
  intro S P hSP hP
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Atlas.G2.Model F) S (Atlas.G2.LieParabolicSetup.sylow (F := F))
  let a := MulAut.conj g
  have hS : (S : Subgroup (Atlas.G2.Model F)).map a.toMonoidHom = (Atlas.G2.LieParabolicSetup.sylow (F := F) : Subgroup _) :=
    congrArg Sylow.toSubgroup hg
  have hp : P.map a.toMonoidHom ≠ ⊤ := by
    intro he
    apply hP
    apply map_injective (f := a.toMonoidHom) a.injective
    rw [he,map_top_of_surjective _ a.surjective]
  obtain hp | hp := Atlas.G2.ProperSylowOvergroups.le_parabolic (P.map a.toMonoidHom)
    (by simpa only [hS, Atlas.G2.LieParabolicSetup.sylow_coe] using map_mono (f := a.toMonoidHom) hSP) (lt_top_iff_ne_top.mpr hp)
  · exact ⟨g,_,hp,Atlas.G2.parabolic_sylow_component_unique F hq 0⟩
  · exact ⟨g,_,hp,Atlas.G2.parabolic_sylow_component_unique F hq 1⟩

private theorem g2_cubic {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : 2 < Nat.card F) : NormalizedLocalCubic (Atlas.G2.Model F) := by
  intro S A hA _
  by_cases he : A = ⊤
  · rw [he,card_top]
    have hr := (Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.g2 (F := F)).trans
      (Theory.GroupTheory.primeRank_le_of_injective 3 (commutator (Atlas.G2.Model F)).subtype Subtype.val_injective)
    by_contra hd
    have hz := PrimeRank.eq_zero_iff_not_dvd_card.mpr hd
    omega
  obtain ⟨g,hg⟩ := FiveLocalFF.G2.local_placement hF S A hA he
  let a := (MulAut.conj g).subgroupMap A
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  have hq : Nonempty (((A.map (MulAut.conj g).toMonoidHom) ⧸
      pCore 2 (A.map (MulAut.conj g).toMonoidHom)) ≃* SL(2,F)) := by
    rcases hg with hg | hg
    · rw [hg]
      exact ⟨(QuotientGroup.quotientMulEquivOfEq Atlas.G2.LieParabolicSetup.local₁_intrinsic_pCore).trans
        Atlas.G2.LieParabolicSetup.local₁RadicalQuotientEquivSL⟩
    · rw [hg]
      exact ⟨(QuotientGroup.quotientMulEquivOfEq Atlas.G2.LieParabolicSetup.local₂_pCore).trans
        Atlas.G2.LieParabolicSetup.local₂RadicalQuotientEquivSL⟩
  have hd : 3 ∣ Nat.card (A ⧸ pCore 2 A) :=
    (Nat.card_congr (aq.trans hq.some).toEquiv).symm ▸ sl2_cubic F
  exact hd.trans (card_quotient_dvd_card _)

private instance (n : ℕ) : Finite (BinaryLinear.OuterCyclic.LinearGroup n) :=
  Finite.of_injective (fun g : BinaryLinear.OuterCyclic.LinearGroup n =>
    (g : BinaryLinear.OuterCyclic.Space n → BinaryLinear.OuterCyclic.Space n)) DFunLike.coe_injective

private theorem binary_five_cubic : NormalizedLocalCubic (BinaryLinear.OuterCyclic.LinearGroup 5) := by
  apply cubic_of_three_free_solvable
  intro S P hSP h3
  rw [BinaryLinear.ThreeFreeSylowOvergroups.eq_sylow_of_three_free S P hSP h3]
  let := S.isPGroup'.isNilpotent
  infer_instance

private theorem alternating_unique {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) :
    SylowOvergroupComponentUnique (alternatingGroup (Fin n)) := by
  rcases hn with rfl | rfl | rfl | rfl
  · apply SylowOvergroupComponentUnique.of_not_sixteen_dvd_card
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  · apply SylowOvergroupComponentUnique.of_not_sixteen_dvd_card
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  · apply SylowOvergroupComponentUnique.of_not_sixteen_dvd_card
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  · exact .of_equiv (Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.trans
    (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 4)))
      (BinaryLinear.sylow_overgroup_component_unique_le_five 4 (by decide))

private theorem top_model {X Y : Type*} [Group X] [Group Y]
    (ht : (⊤ : Subgroup X).IsCComponent) (e : X ≃* Y) : (⊤ : Subgroup Y).IsCComponent := by
  simpa only [map_top_of_surjective e.toMonoidHom e.surjective] using ht.map_equiv e

private theorem center_solvable (X : Type*) [Group X] : Group.IsSolvable (center X) :=
  Group.isSolvable_of_comm (fun a b => Subtype.ext (mem_center_iff.mp a.property b).symm)

/-- Every actual C.2.7 star model has the two full-Sylow tests used by 10.2.6.
Small models force a cubic through Suzuki's lower order bound; the remaining
models force it in the literal normalized local component. -/
theorem sylow_tests {X : Type*} [Group X] [Finite X]
    (hm : Model X) (ht : (⊤ : Subgroup X).IsCComponent) :
    SylowOvergroupComponentUnique X ∧ (Nat.card X < 29120 ∨ NormalizedLocalCubic X) := by
  cases hm with
  | linearTwo F e =>
    exact ⟨.of_equiv e (Matrix.SpecialLinearGroup.sylow_overgroup_component_unique F.Carrier),
      .inr (cubic_of_equiv e (cubic_of_solvable_proper
        Matrix.SpecialLinearGroup.isSolvable_of_proper_sylow_overgroup (sl2_cubic F.Carrier)))⟩
  | linearThree F e =>
    let q := Matrix.PSL3.projection F.Carrier
    let : Group.IsSolvable q.ker := by
      rw [Matrix.PSL3.projection_ker]
      exact center_solvable _
    have hq := Matrix.PSL3.projection_surjective F.Carrier
    have htq : (⊤ : Subgroup PSL(3,F.Carrier)).IsCComponent := by
      rw [← map_top_of_surjective q hq]
      exact cComponent_map_of_solvable_ker (top_model ht e) q hq
    exact ⟨.of_equiv e (.of_surjective q hq (psl3_unique F.degree_pos F.card_eq htq)),
      .inr (cubic_of_equiv e (cubic_of_surjective q hq (psl3_cubic F.degree_pos F.card_eq)))⟩
  | symplectic F hn e =>
    exact ⟨.of_equiv e (sp4_unique hn F.card_eq (top_model ht e)),
      .inr (cubic_of_equiv e (sp4_cubic hn F.card_eq))⟩
  | g2 F hn e =>
    have hq : 2 < Nat.card F.Carrier := by
      rw [F.card_eq]
      exact (show (2 : ℕ)^1 < 2^F.degree from Nat.pow_lt_pow_right (by decide) hn)
    exact ⟨.of_equiv e (g2_unique hq (top_model ht e)),.inr (cubic_of_equiv e (g2_cubic hq))⟩
  | g2DerivedTwo e =>
    exact ⟨.of_equiv e (.of_top_component_and_solvable_proper (top_model ht e)
      Atlas.G2.binaryDerived_solvableSylowOvergroups),.inl (by
        rw [Nat.card_congr e.toEquiv,Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)]
        norm_num)⟩
  | alternating n hn e =>
    refine ⟨.of_equiv e (alternating_unique hn),.inl ?_⟩
    rw [Nat.card_congr e.toEquiv]
    rcases hn with rfl | rfl | rfl | rfl <;> rw [nat_card_alternatingGroup] <;> norm_num [Nat.factorial]
  | linearFiveTwo e =>
    let a := e.trans (BinaryLinear.OuterCyclic.slEquivLinear 5)
    exact ⟨.of_equiv a (BinaryLinear.sylow_overgroup_component_unique_le_five 5 (by decide)),
      .inr (cubic_of_equiv a binary_five_cubic)⟩
  | tripleSix ez e =>
    let := center_solvable X
    refine ⟨.of_quotient (center X) (.of_equiv e (alternating_unique (.inr (.inl rfl)))),.inl ?_⟩
    rw [card_eq_card_quotient_mul_card_subgroup (center X),Nat.card_congr e.toEquiv,
      Nat.card_congr ez.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]

end CFSG.Quasithin.ChapterC.C27Source.StarModels
