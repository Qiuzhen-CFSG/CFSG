module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof.RankOne
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding.SplitOrRee
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.SpecialLinearThreeLocalQuotient

/-!
# Proper local quotients in split and Ree point overcomponents

Restrict the original full Sylow to a containing component and pass through
its literal two-core quotient. The proper local image retains its intrinsic
two-core quotient and Sylow normalization. The concrete parabolic residuals
in SL₃, PSL₃, Sp₄ and G₂ have binary rank-one quotients; in Ree they have
PSL₂ or Suzuki quotients. Each therefore has solvable proper Sylow overgroups.
The SL₃ central cover and the Suzuki residual are both retained.

Comparison.Overcomponent.EmbeddingProof.Lie uses these calculations to
exclude a strict seed--point--container chain, and EmbeddingProof applies
that exclusion to the original chosen flag. Earlier geometry and the seed
marking retain final discharge by qt-d-1222-shadow-components. The remaining
proper-pair sieve belongs to qt-d-1222-shadow-component-comparison.
Source: Aschbacher--Smith A.3.12, 11.1.1 and 11.4.2, printed pp.47--48,761,776.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings Chapter1.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- The proper local image in a containing two-core quotient retains the
intrinsic two-core quotient, full Sylow normalization and top C-component. -/
theorem proper_local_model_image {B J : Subgroup G}
    (hB : B ∈ Chapter1.L G (T : Subgroup G))
    (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hTJ : (T : Subgroup G) ≤ normalizer (J : Set G))
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G)) (hBJ : B < J)
    {A : Type*} [Group A] [Finite A] (e : (J ⧸ pCore 2 J) ≃* A) :
    ∃ (S : Sylow 2 A) (C : Subgroup A), C ∈ localCComponents S ∧ C ≠ ⊤ ∧
      (S : Subgroup A) ≤ normalizer (C : Set A) ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* (C ⧸ pCore 2 C)) ∧
      (⊤ : Subgroup A).IsCComponent := by
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T J hTJ
  let D := B.subgroupOf J
  have hd : D ∈ localCComponents P := by
    rw [hP]
    exact local_restrict hB.1 hBJ.le
  have ht : (⊤ : Subgroup J).IsCComponent := by
    simpa only [subgroupOf_self] using hJ.1.subgroupOf_of_le le_rfl le_sup_left
  let q := QuotientGroup.mk' (pCore 2 J)
  let f := e.toMonoidHom.comp q
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 J := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let := pCore_isNilpotent (p := 2) (G := J)
  let : Group.IsSolvable f.ker := hk ▸ (inferInstance : Group.IsSolvable (pCore 2 J))
  let S := P.mapSurjective (f := f) hf
  let C := D.map f
  have hp : C ≠ ⊤ := by
    intro he
    have heq : D.map q = (⊤ : Subgroup J).map q := by
      apply map_injective (f := e.toMonoidHom) e.injective
      rw [map_map,map_map,map_top_of_surjective f hf]
      exact he
    have hD := Chapter1.Section02.MovedMaximality.eq_of_twoCore_images_eq P hd ht le_top heq
    exact hBJ.not_ge (subgroupOf_eq_top.mp hD)
  have hn : (P : Subgroup J) ≤ normalizer (D : Set J) := by
    rw [hP]
    intro x hx
    exact mem_normalizer_iff.mpr (fun y => (mem_normalizer_iff.mp (hTB hx) y.val))
  have hker : IsPGroup 2 (f.subgroupMap D).ker := by
    rw [ker_subgroupMap,hk]
    exact pCore_isPGroup.comap_subtype
  let d := subgroupOfEquivOfLe hBJ.le
  let dq := QuotientGroup.congr _ _ d (pCore_map_iso 2 d)
  let a := (f.subgroupMap D).quotientPCoreEquivOfSurjective (f.subgroupMap_surjective D) hker
  refine ⟨S,C,Chapter1.Section02.localCComponents_map_of_solvable_ker hd f,hp,
    (map_mono hn).trans (D.le_normalizer_map f),⟨dq.symm.trans a⟩,?_⟩
  have hh := (ht.map_quotient (pCore 2 J)).map_equiv e
  simpa only [map_top_of_surjective (QuotientGroup.mk' (pCore 2 J)) (QuotientGroup.mk'_surjective _),
    map_top_of_surjective e.toMonoidHom e.surjective] using hh

private theorem linear_local_solvable {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (S : Sylow 2 PSL(3,F)) (C : Subgroup PSL(3,F))
    (hC : C ∈ localCComponents S) (hp : C ≠ ⊤) :
    SolvableSylowOvergroups (C ⧸ pCore 2 C) := by
  obtain ⟨g,hg⟩ := FiveLocalFF.linear_three_local_placement hF hn S C hC hp
  let a := (MulAut.conj g).subgroupMap C
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  apply SolvableSylowOvergroups.of_equiv aq
  change SolvableSylowOvergroups ((C.map (MulAut.conj g).toMonoidHom) ⧸
    pCore 2 (C.map (MulAut.conj g).toMonoidHom))
  rcases hg with hg | hg
  · rw [hg]
    exact SolvableSylowOvergroups.of_equiv (Matrix.PSL3.LinearThree.pointLocalCoreQuotientEquiv F)
      Matrix.SpecialLinearGroup.isSolvable_of_proper_sylow_overgroup
  · rw [hg]
    exact SolvableSylowOvergroups.of_equiv (Matrix.PSL3.LinearThree.lineLocalCoreQuotientEquiv F)
      Matrix.SpecialLinearGroup.isSolvable_of_proper_sylow_overgroup

private theorem symplectic_local_solvable {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (S : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F))
    (C : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F))
    (hC : C ∈ localCComponents S) (hp : C ≠ ⊤) :
    SolvableSylowOvergroups (C ⧸ pCore 2 C) := by
  obtain ⟨g,hg⟩ := FiveLocalFF.symplectic_local_placement hF hn S C hC hp
  let a := (MulAut.conj g).subgroupMap C
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  apply SolvableSylowOvergroups.of_equiv aq
  change SolvableSylowOvergroups ((C.map (MulAut.conj g).toMonoidHom) ⧸
    pCore 2 (C.map (MulAut.conj g).toMonoidHom))
  rcases hg with hg | hg
  · rw [hg]
    exact SolvableSylowOvergroups.of_equiv
      (Theory.SpecificGroups.SymplecticFour.pointLocalCoreQuotientEquiv hF hn)
      Matrix.SpecialLinearGroup.isSolvable_of_proper_sylow_overgroup
  · rw [hg]
    exact SolvableSylowOvergroups.of_equiv
      (Theory.SpecificGroups.SymplecticFour.planeLocalCoreQuotientEquiv hF hn)
      Matrix.SpecialLinearGroup.isSolvable_of_proper_sylow_overgroup

private theorem g2_local_solvable {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hq : 2 < Nat.card F) (S : Sylow 2 (Atlas.G2.Model F))
    (C : Subgroup (Atlas.G2.Model F)) (hC : C ∈ localCComponents S) (hp : C ≠ ⊤) :
    SolvableSylowOvergroups (C ⧸ pCore 2 C) := by
  obtain ⟨g,hg⟩ := FiveLocalFF.G2.local_placement hq S C hC hp
  let a := (MulAut.conj g).subgroupMap C
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  apply SolvableSylowOvergroups.of_equiv aq
  change SolvableSylowOvergroups ((C.map (MulAut.conj g).toMonoidHom) ⧸
    pCore 2 (C.map (MulAut.conj g).toMonoidHom))
  rcases hg with hg | hg
  · rw [hg]
    exact SolvableSylowOvergroups.of_equiv
      ((QuotientGroup.quotientMulEquivOfEq Atlas.G2.LieParabolicSetup.local₁_intrinsic_pCore).trans
        Atlas.G2.LieParabolicSetup.local₁RadicalQuotientEquivSL)
      Matrix.SpecialLinearGroup.isSolvable_of_proper_sylow_overgroup
  · rw [hg]
    exact SolvableSylowOvergroups.of_equiv
      ((QuotientGroup.quotientMulEquivOfEq Atlas.G2.LieParabolicSetup.local₂_pCore).trans
        Atlas.G2.LieParabolicSetup.local₂RadicalQuotientEquivSL)
      Matrix.SpecialLinearGroup.isSolvable_of_proper_sylow_overgroup

private theorem ree_local_solvable {m : ℕ} (hm : 1 ≤ m)
    (htop : (⊤ : Subgroup (ReeF4.Model m)).IsCComponent)
    (S : Sylow 2 (ReeF4.Model m)) (C : Subgroup (ReeF4.Model m))
    (hC : C ∈ localCComponents S) (hp : C ≠ ⊤) :
    SolvableSylowOvergroups (C ⧸ pCore 2 C) := by
  obtain ⟨g,s,hg⟩ := ReeLocal.local_placement hm htop S C hC hp
  let a := ((MulAut.conj g).subgroupMap C).trans (MulEquiv.subgroupCongr hg)
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  apply SolvableSylowOvergroups.of_equiv aq
  cases s with
  | linear =>
    apply bender_solvable_proper_sylow_overgroup
    exact .linear (2 * m + 1) (by omega)
      ⟨ReeF4.CoefficientField m,inferInstance,inferInstance,ReeF4.field_card m,
        ⟨ReeF4.Parabolics.linearLocalQuotientEquiv m⟩⟩
  | suzuki =>
    apply bender_solvable_proper_sylow_overgroup
    exact .suzuki m hm ⟨ReeF4.Parabolics.suzukiLocalQuotientEquiv m⟩

/-- All four split rank-two quotient models force a rank-one proper local quotient. -/
theorem split_quotient_local_solvable {B J : Subgroup G}
    (hB : B ∈ Chapter1.L G (T : Subgroup G))
    (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hTJ : (T : Subgroup G) ≤ normalizer (J : Set G))
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G)) (hBJ : B < J)
    {n : ℕ} (hn : 1 < n)
    (hm : Source.IsSL (J ⧸ pCore 2 J) 3 (2 ^ n) ∨
      ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 3 (2 ^ n) ∨
      Source.IsSp (J ⧸ pCore 2 J) 2 (2 ^ n) ∨
      ClassificationModels.IsG2At (J ⧸ pCore 2 J) (2 ^ n)) :
    SolvableSylowOvergroups (B ⧸ pCore 2 B) := by
  rcases hm with hm | hm | hm | hm
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    obtain ⟨S,C,hC,hp,_,⟨a⟩,_⟩ := proper_local_model_image hB hJ hTJ hTB hBJ e
    obtain ⟨b⟩ := special_linear_three_local_core_quotient hF hn S C hC hp
    exact SolvableSylowOvergroups.of_equiv (a.trans b)
      Matrix.SpecialLinearGroup.isSolvable_of_proper_sylow_overgroup
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    obtain ⟨S,C,hC,hp,_,⟨a⟩,_⟩ := proper_local_model_image hB hJ hTJ hTB hBJ e
    exact SolvableSylowOvergroups.of_equiv a (linear_local_solvable hF hn S C hC hp)
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    obtain ⟨S,C,hC,hp,_,⟨a⟩,_⟩ := proper_local_model_image hB hJ hTJ hTB hBJ e
    exact SolvableSylowOvergroups.of_equiv a (symplectic_local_solvable hF hn S C hC hp)
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    obtain ⟨S,C,hC,hp,_,⟨a⟩,_⟩ := proper_local_model_image hB hJ hTJ hTB hBJ e
    have hq : 2 < Nat.card F := by
      rw [hF]
      exact (by norm_num : 2 = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) hn
    exact SolvableSylowOvergroups.of_equiv a (g2_local_solvable hq S C hC hp)

/-- Both genuine Ree parabolic residuals have rank-one intrinsic quotients. -/
theorem ree_quotient_local_solvable {B J : Subgroup G}
    (hB : B ∈ Chapter1.L G (T : Subgroup G))
    (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hTJ : (T : Subgroup G) ≤ normalizer (J : Set G))
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G)) (hBJ : B < J)
    {m : ℕ} (hm : 1 ≤ m)
    (hmodel : Chapter1.Section02.LocalModels.IsReeF4At (J ⧸ pCore 2 J) m) :
    SolvableSylowOvergroups (B ⧸ pCore 2 B) := by
  obtain ⟨d,⟨e⟩⟩ := hmodel
  obtain ⟨S,C,hC,hp,_,⟨a⟩,htop⟩ := proper_local_model_image hB hJ hTJ hTB hBJ (e.trans d.modelEquiv)
  exact SolvableSylowOvergroups.of_equiv a (ree_local_solvable hm htop S C hC hp)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
