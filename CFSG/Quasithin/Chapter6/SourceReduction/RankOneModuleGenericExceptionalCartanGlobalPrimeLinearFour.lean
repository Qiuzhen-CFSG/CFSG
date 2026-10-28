module
public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.TwoCoreCoveredFour
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeAssembly
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeLinearGeometry

/-!
# Complete linear source factor selection, including field four

The original component image in X/O₂(X) maps to the marked projective
component with kernel equal to its embedded center. The intrinsic
non-PSL₃(4) assumption forces this center to be nontrivial at field four.
The overlap two-core fixes that odd center and the projective Borel torus,
so it preserves both whole parabolics and hence their perfect residuals.
All quotient maps retain the original marking and the possible cubic center.

Combining this calculation with the higher-field, symplectic, exchanged
and single-Bender constructions discharges SourceLocalConstruction in full.
Each resulting literal prime pair has the genuine F.1.1 zero-core branch
or the index-two moving-factor branch. The model exclusions, field reduction
and changed-Sylow normalization remain with the same local-to-global owner.

Source: Aschbacher–Smith E.2.2, 5.1.11(3), 5.2.1–2, printed
pp.215–216,635,646–649 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
open Matrix.PSL3.LinearThree
open Matrix.PSL3.LinearThree.OuterExtensions
variable {X : Type*} [Group X] [Finite X]
variable {F : Type} [Field F] [Finite F] [CharP F 2]

/-- At field four the actual nonprojective residual forces preservation of
both whole factors by the overlap two-core. -/
theorem linearSourceFactor.twoCore_normalizes_four
    {M C U : Subgroup X} [C.Normal]
    (hC : C.IsCComponent) (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hO : pCore 2 X ≤ sourceKernel M) (hc : SingleClauses M C U)
    (hnot : ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 4)
    (hF : Nat.card F = 4) (e : sourceImage M C ≃* PSL(3,F))
    (he : (componentOverlap M C).map e.toMonoidHom = borel F) (i : Bool) :
    M.pCoreIn 2 ≤ normalizer (linearSourceFactor M C e i : Set X) := by
  let q0 := QuotientGroup.mk' (pCore 2 X)
  let qJ := QuotientGroup.mk' (sourceKernel M)
  have hO' : pCore 2 X ≤ (sourceKernel M).comap (MonoidHom.id X) := by
    simpa only [comap_id] using hO
  let q := QuotientGroup.map (pCore 2 X) (sourceKernel M) (MonoidHom.id X) hO'
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (sourceKernel M) y
    exact ⟨q0 x,rfl⟩
  have hqcomp : q.comp q0 = qJ := by ext x; rfl
  let K := actorImage C
  let M0 := M.map q0
  let : K.Normal := Normal.map inferInstance q0 (QuotientGroup.mk'_surjective _)
  let ec : (C ⧸ pCore 2 C) ≃* K := cComponentTwoCoreQuotientEquiv hC
  let := hqs
  let : IsQuasisimple K := IsQuasisimple.of_mulEquiv ec
  have hk0 : pCore 2 K = ⊥ := by
    rw [←pCore_map_iso 2 ec,pCore_quotient_pCore_eq_bot,Subgroup.map_bot]
  have ho : Odd (Nat.card (center K)) := by
    have hfit : center K ≤ fittingSubgroup K := le_sSup ⟨inferInstance,inferInstance⟩
    apply Nat.coprime_two_left.mp
    exact pPrimeCore_coprime_card.of_dvd_right (card_dvd_of_le
      (hfit.trans (fitting_le_pPrimeCore_of_pCore_eq_bot 2 hk0)))
  have hk : q.ker = (center K).map K.subtype := by
    dsimp only [q]
    rw [QuotientGroup.ker_map,comap_id]
    exact hc.kernel_center
  have hkM : q.ker ≤ M0 := by
    dsimp only [q]
    rw [QuotientGroup.ker_map,comap_id]
    exact map_mono M.normalCore_le
  have hK : K.map q = sourceImage M C := by
    change (C.map q0).map q = C.map qJ
    rw [map_map,hqcomp]
  have hM0 : M0.map q = M.map qJ := by
    change (M.map q0).map q = _
    rw [map_map,hqcomp]
  let eqK : K.map q ≃* sourceImage M C := MulEquiv.subgroupCongr hK
  let eqp : PSL(3,F) ≃* K.map q := e.symm.trans eqK.symm
  have hj : (K.map q).subtype.comp eqp.toMonoidHom =
      (sourceImage M C).subtype.comp e.symm.toMonoidHom := by
    ext x
    rfl
  have hb : (M0.map q).comap ((K.map q).subtype.comp eqp.toMonoidHom) = borel F := by
    rw [hM0,hj]
    rw [source_overlap_coordinate] at he
    exact (comap_equiv_eq_map_symm e.symm _).trans he
  have hz : center K ≠ ⊥ := by
    intro hz
    have hker : q.ker = ⊥ := by rw [hk,hz,Subgroup.map_bot]
    have hi : Function.Injective (q.subgroupMap K) := by
      intro x y hh
      exact Subtype.ext (q.ker_eq_bot_iff.mp hker (congrArg Subtype.val hh))
    let a := MulEquiv.ofBijective (q.subgroupMap K) ⟨hi,q.subgroupMap_surjective K⟩
    exact hnot ⟨F,inferInstance,inferInstance,hF,⟨ec.trans (a.trans (eqK.trans e))⟩⟩
  have hn := twoCore_normalizes_parabolic_four_cover hF K M0 q hq hk hkM ho hz eqp hb i
  rw [hj] at hn
  have hcore : (M.pCoreIn 2).map q0 ≤ M0.pCoreIn 2 := by
    have hh : (pCore 2 M).map (q0.subgroupMap M) ≤ pCore 2 M0 :=
      le_sSup ⟨Normal.map inferInstance _ (q0.subgroupMap_surjective M),pCore_isPGroup.map _⟩
    have hh' := map_mono (f := M0.subtype) hh
    have heq : M0.subtype.comp (q0.subgroupMap M) = q0.comp M.subtype := by ext x; rfl
    simpa only [pCoreIn,map_map,heq] using hh'
  intro x hx
  apply linearSourceFactor.normalizes_of_parabolic e i
  have hh := hn (mem_map_of_mem q (hcore (mem_map_of_mem q0 hx)))
  exact hh

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
open Matrix.PSL3.LinearThree
variable {G : Type*} [Group G] [Finite G]

/-- The original non-PSL₃(4) hypothesis closes the scalar-cover branch of
linear factor selection at every independently marked residual degree. -/
theorem linear_source_rightData_of_nonprojective_four
    {T : Sylow 2 G} {L H A B : Subgroup G} {f : ℕ}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H)) (hf : 1 < f)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ f)
    (e : sourceImage ((normalizer (L : Set G)).subgroupOf H) C ≃* PSL(3,F))
    (he : (componentOverlap ((normalizer (L : Set G)).subgroupOf H) C).map
      e.toMonoidHom = borel F)
    (hmove : MovesDiagram ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H) e (pointParabolic F) (lineParabolic F)) :
    ∃ R : Bool → Subgroup G, ∀ i, RightData T L H B (R i) ∧
      ClassicalGroup.IsPSL (R i ⧸ pCore 2 (R i)) 2 (2 ^ f) := by
  by_cases hf2 : f = 2
  · subst f
    let S := T.subtype hH.1.1.2
    let M := (normalizer (L : Set G)).subgroupOf H
    let : C.Normal := DiagramHall.single_component_normal S hC hc
    have hCeq : C = pResidual 2 H := (DiagramHall.single_component_eq_twoResidual S hC hc).symm
    have hnot : ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 4 := hCeq.symm ▸ hthree
    have hO : pCore 2 H ≤ sourceKernel M := normal_le_normalCore.mpr
      ((pCore_isPGroup.le_sylow_of_normal S).trans (comap_mono hTL))
    exact linear_source_rightData_of_factor_normalizes hTL hH hpar c hC hqs hc hf hF e he hmove
      (fun i => linearSourceFactor.twoCore_normalizes_four hC hqs hO hc hnot
        (by simpa using hF) e he i)
  · exact linear_source_rightData hTL hH hpar c hC hqs hc hf hf2 hF e he hmove

/-- Both linear factors now give the literal prime pair at every source field,
including four, with the original nonprojective hypothesis and no added premise. -/
theorem linear_source_prime_pair_of_nonprojective_four
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p f : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H)) (hf : 1 < f)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ f)
    (e : sourceImage ((normalizer (L : Set G)).subgroupOf H) C ≃* PSL(3,F))
    (he : (componentOverlap ((normalizer (L : Set G)).subgroupOf H) C).map
      e.toMonoidHom = borel F)
    (hmove : MovesDiagram ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H) e (pointParabolic F) (lineParabolic F)) :
    ∃ R : Bool → Subgroup G, ∀ i,
      ClassicalGroup.IsPSL (R i ⧸ pCore 2 (R i)) 2 (2 ^ f) ∧
      LocalData T L H B D (R i) ∧
      (((generated L H D (R i)).pCoreIn 2 = ⊥ ∧
        ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H,R i] (Global.sourceS L H)) ∨
       ((generated L H D (R i)).pCoreIn 2 ≠ ⊥ ∧ ¬ D ≤ normalizer (R i : Set G) ∧
        (normalizingSylow T (R i)).relIndex (T : Subgroup G) = 2)) := by
  obtain ⟨R,hr⟩ := linear_source_rightData_of_nonprojective_four
    h.sylow_normalizes hH hpar hthree c hC hqs hc hf hF e he hmove
  refine ⟨R,?_⟩
  intro i
  let d := (hr i).1.localData h hH c hd
  refine ⟨(hr i).2,d,?_⟩
  by_cases hz : (generated L H D (R i)).pCoreIn 2 = ⊥
  · exact Or.inl ⟨hz,d.hypothesisF11 h hH c hd hz⟩
  · exact Or.inr ⟨hz,d.prime_actor_not_normalizes_right h hH c hd hz,
      d.normalizingSylow_index hH.1.1.2 c hd hz⟩

/-- Every original source row supplies a literal prime pair. In the field-four
linear row the excluded intrinsic PSL₃(4) quotient retains a scalar center,
which rules out two-core diagram movement. -/
theorem source_prime_pair
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    ∃ R : Subgroup G, LocalData T L H B D R := by
  rcases source_prime_pair_or_four_linear_diagram h hH hpar c hd with hr | hs
  · exact hr
  obtain ⟨C,hC,hqs,_,hc,F,_,_,_,hF,e,he,hmove⟩ := hs
  obtain ⟨R,hr⟩ := linear_source_rightData_of_nonprojective_four h.sylow_normalizes hH hpar
    hthree c hC hqs hc (f := 2) (by decide) (by simpa using hF) e he hmove
  exact ⟨R true,(hr true).1.localData h hH c hd⟩

/-- The constructed source pair has the genuine F.1.1 alternative or the
moving-factor/index-two alternative; neither is a model-recognition callback. -/
theorem source_prime_pair_core_alternatives
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    ∃ R : Subgroup G, LocalData T L H B D R ∧
      (((generated L H D R).pCoreIn 2 = ⊥ ∧
        ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H)) ∨
       ((generated L H D R).pCoreIn 2 ≠ ⊥ ∧ ¬ D ≤ normalizer (R : Set G) ∧
        (normalizingSylow T R).relIndex (T : Subgroup G) = 2)) := by
  obtain ⟨R,d⟩ := source_prime_pair h hH hpar hthree c hd
  refine ⟨R,d,?_⟩
  by_cases hz : (generated L H D R).pCoreIn 2 = ⊥
  · exact Or.inl ⟨hz,d.hypothesisF11 h hH c hd hz⟩
  · exact Or.inr ⟨hz,d.prime_actor_not_normalizes_right h hH c hd hz,
      d.normalizingSylow_index hH.1.1.2 c hd hz⟩

/-- The original pre-normalization selection obligation is discharged from the
source hypotheses. The module-degree and local-control premises are not needed
for selection; they remain available for the subsequent model exclusions. -/
theorem sourceLocalConstruction : SourceLocalConstruction G := by
  intro T L W n h H hH hpar hthree A B c _ _ p D hd
  exact source_prime_pair h hH hpar hthree c hd

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
