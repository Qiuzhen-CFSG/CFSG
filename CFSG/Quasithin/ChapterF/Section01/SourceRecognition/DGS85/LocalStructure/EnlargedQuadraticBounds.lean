module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SmallProjectiveUnitarySections
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SmallSpecialUnitaryEnlargement
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.EnlargementCatalogue
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.EndpointModelBounds

/-!
# Quadratic estimates for the actual enlarged quotient

The full F.1.1 catalogue gives the lower quadratic index estimate on each
original enlarged endpoint. A sharp index forces its actual two-core
quotient to be linear. The possible PSU₃(2) enlargement of order 144 is
retained: fixed generation makes its nontrivial action faithful, and its
strict cubic ratio rules out a sharp index. No order-144 exclusion is an
input. The quotient estimates are transported through the original
completion inclusion and conjugation to every intrinsic graph actor.

`CriticalActorSelection` applies these estimates to the full critical-center
actions and discharges every fixed-generation and Sylow-faithfulness premise.
This is a source-specific substitute for the catalogue input at that
consumer, not the unrestricted enlargement assertion in 6.1.
Source: DGS, *Groups and Graphs* (1985), 6.1, pp.118--119, and the opening
of 7.1, pp.126--127, using the corrected generation premise in 5.12.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition Theory.GroupTheory.AmalgamGraph
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem small_projective_sharp_impossible (h : HypothesisF11 L S) (i : Fin 2)
    (hm : ClassicalGroup.IsPSU (L i ⧸ pCore 2 (L i)) 3 2)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (σ : Representation (ZMod 2) (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)) W)
    (T : Sylow 2 (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)))
    (A : Subgroup (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)))
    (hAT : A ≤ T) (hA : 1 < Nat.card A) (hq : IsQuadratic σ A)
    (hg : ∀ R : Sylow 2 (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)), GeneratedByFixedSpace σ R)
    (hd : Disjoint σ.ker (T : Subgroup _))
    (hb : Nat.card (W ⧸ fixedSpace σ A) ≤ Nat.card A) : False := by
  let := h.finite_parabolic i
  let : Finite (enlargedEndpoint L S i) := Finite.of_injective
    (inclusion (show enlargedEndpoint L S i ≤ parabolic L S i from
      sup_le (starredParabolic_le i) ((pCoreIn_le 2 _).trans (commonBorel_le_parabolic i))))
    (inclusion_injective _)
  let : FiniteDimensional (ZMod 2) W := Module.Finite.of_finite
  have hnt : σ ≠ 1 := by
    intro he
    have hAb : A = ⊥ := by
      apply bot_unique
      intro a ha
      exact hd.le_bot ⟨by change σ a = 1; rw [he]; rfl,hAT ha⟩
    rw [hAb,card_bot] at hA
    omega
  have hf := original_small_projective_enlargement_faithful h i hm σ hg hnt
  let : IsElementaryAbelian 2 A := elementary_of_faithful_quadratic σ hf A hq
  have hE : IsElementaryTwo A := ⟨fun he => by
    have hh : Nat.card A = 1 := card_eq_one.mpr he
    omega,inferInstance⟩
  have hpow : 2 ^ fixedCodim σ A ≤ 2 ^ rank A := by
    rw [←hE.card_eq_two_pow_rank]
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hb
    exact hb
  have hff : IsFFModule σ := ⟨A,hE,
    (Nat.pow_le_pow_iff_right (by decide : 1 < (2:ℕ))).mp hpow⟩
  exact (not_lt_of_ge (((isFFModule_iff_cubicRatio_le_one σ).mp hff).trans (by norm_num)))
    (original_small_projective_enlargement_cubic_bound h i hm σ hf)

/-- The actual enlarged quotient obeys the source quadratic bound even in the
possible strict projective enlargement. Sharp index forces a linear quotient. -/
theorem original_enlarged_quadratic_bounds (h : HypothesisF11 L S) (i : Fin 2)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (σ : Representation (ZMod 2) (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)) W)
    (T : Sylow 2 (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)))
    (A : Subgroup (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)))
    (hAT : A ≤ T) (hA : 1 < Nat.card A) (hq : IsQuadratic σ A)
    (hg : ∀ R : Sylow 2 (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)), GeneratedByFixedSpace σ R)
    (hd : Disjoint σ.ker (T : Subgroup _)) :
    Nat.card A ≤ Nat.card (W ⧸ fixedSpace σ A) ∧
      (Nat.card (W ⧸ fixedSpace σ A) ≤ Nat.card A →
        ∃ n, 0 < n ∧ ClassicalGroup.IsPSL
          (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)) 2 (2^n)) := by
  let := h.finite_parabolic i
  let : Finite (enlargedEndpoint L S i) := Finite.of_injective
    (inclusion (show enlargedEndpoint L S i ≤ parabolic L S i from
      sup_le (starredParabolic_le i) ((pCoreIn_le 2 _).trans (commonBorel_le_parabolic i))))
    (inclusion_injective _)
  have bound (hm : IsRankOneModel (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i))) :=
    And.intro (Noncommuting.rankOne_sylow_faithful_quadratic_bound hm σ T A hAT hA hq (hg T) hd)
      (Noncommuting.rankOne_linear_of_sylow_faithful_sharp_index hm σ T A hAT hA hq (hg T) hd)
  rcases reduced_enlargement_rankOne_or_small_unitary h i with hm | hp | hs
  · exact bound hm
  · have hn := small_projective_sharp_impossible h i hp σ T A hAT hA hq hg hd
    exact ⟨by by_contra hh; exact hn (by omega),fun hb => (hn hb).elim⟩
  · exact bound (.special_unitary 1 (by decide)
      (by simpa using original_small_special_enlarged_marking h i hs))


/-- Transport the estimates through an actual enlarged-quotient marking. -/
theorem marked_enlarged_quadratic_bounds (h : HypothesisF11 L S) (i : Fin 2)
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (e : D ≃* (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)))
    (σ : Representation (ZMod 2) D W) (T : Sylow 2 D) (A : Subgroup D)
    (hAT : A ≤ T) (hA : 1 < Nat.card A) (hq : IsQuadratic σ A)
    (hg : ∀ R : Sylow 2 D, GeneratedByFixedSpace σ R)
    (hd : Disjoint σ.ker (T : Subgroup D)) :
    Nat.card A ≤ Nat.card (W ⧸ fixedSpace σ A) ∧
      (Nat.card (W ⧸ fixedSpace σ A) ≤ Nat.card A →
        ∃ n, 0 < n ∧ ClassicalGroup.IsPSL D 2 (2^n)) := by
  let ρ := σ.comp e.symm.toMonoidHom
  let R := T.mapSurjective (f := e.toMonoidHom) e.surjective
  have hg' : ∀ U : Sylow 2 (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)), GeneratedByFixedSpace ρ U := by
    intro U
    obtain ⟨V,rfl⟩ := Sylow.mapSurjective_surjective (f := e.toMonoidHom) e.surjective 2 U
    exact generatedByFixedSpace_of_equivariant_surjection σ ρ e.toMonoidHom
      LinearMap.id Function.surjective_id (by intro g v; simp [ρ]) V (hg V)
  have hd' : Disjoint ρ.ker (R : Subgroup _) := by
    apply disjoint_iff.mpr
    apply bot_unique
    rintro _ ⟨hk,x,hx,rfl⟩
    have hxk : x ∈ σ.ker := by simpa [ρ] using hk
    have hx1 := mem_bot.mp (hd.le_bot ⟨hxk,hx⟩)
    simp only [hx1,map_one,mem_bot]
  have hq' : IsQuadratic ρ (A.map e.toMonoidHom) := by
    rintro a ⟨b,hb,rfl⟩ c ⟨d,hd,rfl⟩ v
    simpa only [ρ,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,e.symm_apply_apply] using hq b hb d hd v
  have hf : fixedSpace ρ (A.map e.toMonoidHom) = fixedSpace σ A := by
    rw [fixedSpace_comp_map,map_map]
    have he : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id D := by ext x; simp
    rw [he,map_id]
  have hc : Nat.card (A.map e.toMonoidHom) = Nat.card A := card_map_of_injective e.injective
  obtain ⟨hb,hl⟩ := original_enlarged_quadratic_bounds h i ρ R (A.map e.toMonoidHom)
    (map_mono hAT) (hc.symm ▸ hA) hq' hg' hd'
  rw [hf,hc] at hb hl
  refine ⟨hb,fun hh => ?_⟩
  obtain ⟨n,hn,he⟩ := hl hh
  exact ⟨n,hn,he.of_mulEquiv e⟩

open Subgroup.CosetGeometry.RankTwo in
/-- The full original catalogue supplies quadratic bounds for every intrinsic
graph actor, without an order-144 or model premise. -/
theorem reduced_graph_quadratic_bounds (h : HypothesisF11 L S)
    (v : Vertex (reducedFamily L S))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (σ : Representation (ZMod 2) (graphLocalGroup (reducedFamily L S) v ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) v)) W)
    (T : Sylow 2 (graphLocalGroup (reducedFamily L S) v ⧸ pCore 2 (graphLocalGroup (reducedFamily L S) v)))
    (A : Subgroup (graphLocalGroup (reducedFamily L S) v ⧸ pCore 2 (graphLocalGroup (reducedFamily L S) v)))
    (hAT : A ≤ T) (hA : 1 < Nat.card A) (hq : IsQuadratic σ A)
    (hg : ∀ R : Sylow 2 (graphLocalGroup (reducedFamily L S) v ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) v)), GeneratedByFixedSpace σ R)
    (hd : Disjoint σ.ker (T : Subgroup _)) :
    Nat.card A ≤ Nat.card (W ⧸ fixedSpace σ A) ∧
      (Nat.card (W ⧸ fixedSpace σ A) ≤ Nat.card A →
        ∃ n, 0 < n ∧ ClassicalGroup.IsPSL (graphLocalGroup (reducedFamily L S) v ⧸
          pCore 2 (graphLocalGroup (reducedFamily L S) v)) 2 (2^n)) := by
  let : ∀ j, Finite ((reducedFamily L S) j) := finite_endpoints (reduced_triple h)
  let : Finite (graphLocalGroup (reducedFamily L S) v) := Finite.of_injective
    (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let F := reducedFamily L S
  obtain ⟨g,hg₀⟩ := Subgroup.CosetGeometry.exists_smul_base F v
  let M := graphLocalGroup F (base F v.type)
  have heq : M.map (MulAut.conj g).toMonoidHom = graphLocalGroup F v :=
    (graphLocalGroup_conjugate (reduced_triple h) g (base F v.type)).symm.trans
      (congrArg (graphLocalGroup F) hg₀)
  let a : M ≃* graphLocalGroup F v :=
    (M.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
      (MulEquiv.subgroupCongr heq)
  let e := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm.trans
    (reduced_graphEnlargementQuotient h v.type)
  let i : Fin 2 := if v.type then 1 else 0
  have hj : family (enlargedEndpoint L S) v.type = enlargedEndpoint L S i := by
    dsimp only [i]
    cases v.type <;> rfl
  let b := MulEquiv.subgroupCongr hj
  exact marked_enlarged_quadratic_bounds h i
    (e.trans (QuotientGroup.congr _ _ b (pCore_map_iso 2 b))) σ T A hAT hA hq hg hd

end CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
