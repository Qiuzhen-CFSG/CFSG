module
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.LinearFourAction
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.SeedNormalizerRank
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.NormalizerTheta
public import Theory.SpecificGroups.BinaryLinear.FourPlaneRank
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.Lifting
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.ModelExtension.Earlier
/-!
# Original13.7.6(1), the contained four-dimensional case

The whole natural H* action contains the full four-dimensional binary linear
group. Its original seed is a plane, whose stabilizer has three-rank two.
The literal K/O₂(K) quotient transfers this rank to N_K(V₃); original
13.7.5(4) supplies the covered local quotient. The full quotient image of K
and the original Sylow subgroup also give H=KT.

Source: Aschbacher–Smith, 13.7.6(1), printed p.939, n=4 and L₁≤K case.
The n=3 exclusion and noncontained-L₁ cases remain separate source branches.
-/
@[expose] public section
open Subgroup Representation
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section07.ModelExclusions
open Section08.SourceCompletion
open Section08.TransvectionRecognition Component
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionRecognition.Component.RecognitionStep
open Section08.TransvectionParabolic.Marking
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
  [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]
include d
/-- The original four-dimensional natural component gives the full actor, covered quotient and H=KT. -/
theorem linear_four_source_case_of_one_le
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinear.GL (Fin 4 → ZMod 2))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH (linearRepresentation 4) eK) :
    (H : Set G) = (K : Set G) * (T : Set G) ∧
    Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
    primeRank 3 (K ⊓ normalizer (V₃ : Set G) : Subgroup G) = 2 ∧
    ∃ (eH : Section08.Source.Hstar H ≃* BinaryLinear.GL (Fin 4 → ZMod 2))
      (eV : Additive (Section08.Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2)),
      (∀ k : K, eH (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)) =
        eK (QuotientGroup.mk' (pCore 2 K) k)) ∧
      ∀ a v, eV (ρ a v) = eH a (eV v) := by
  obtain ⟨eH,eV,heK,heV⟩ := linear_four_full_action_of_one_le d hH hF9 hKH hK hL₁K ρ hρ eK hs
  have hprod : (H : Set G) = (K : Set G) * (T : Set G) := by
    apply product_of_star_product_sylow T H K hF9.T_le_H hKH
    intro x
    obtain ⟨y,hy⟩ := eK.surjective (eH x)
    obtain ⟨k,hk⟩ := QuotientGroup.mk'_surjective (pCore 2 K) y
    have he : QuotientGroup.mk' (pCore 2 H) (inclusion hKH k) = x := eH.injective (by rw [heK,hk,hy])
    refine ⟨_,⟨inclusion hKH k,k.property,rfl⟩,1,one_mem _,?_⟩
    exact (mul_one _).trans he |>.symm
  have hd : Module.finrank (ZMod 2) ((sectionImage H V₃ V₁ V₃).map eV.toLinearMap) = 2 :=
    (eV.finrank_map_eq _).trans
      (sectionImage_seed_finrank (d.line_le_plane.trans d.plane_le_seed) d.line_card d.seed_card)
  have he : ∀ k : K, ∀ v,
      eV (ρ (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)) v) =
        linearRepresentation 4 (eK (QuotientGroup.mk' (pCore 2 K) k)) (eV v) := by
    intro k v
    rw [heV,heK]
    rfl
  let : Finite (BinaryLinear.GL (Fin 4 → ZMod 2)) := Finite.of_injective
    (fun g : BinaryLinear.GL (Fin 4 → ZMod 2) => (g : (Fin 4 → ZMod 2) → (Fin 4 → ZMod 2)))
    DFunLike.coe_injective
  have hrank : primeRank 3 (K ⊓ normalizer (V₃ : Set G) : Subgroup G) = 2 := by
    rw [seed_normalizer_rank_of_model (d.line_le_plane.trans d.plane_le_seed) hKH ρ hρ
      (linearRepresentation 4) eK eV he]
    exact BinaryLinear.FourPlaneRank.parabolic_rank (by simp) _ hd
  have hcover := (covered_and_theta_of_one_le_rank_two d h hH hF9 hcentral hKH hK hL₁K hrank).1
  exact ⟨hprod,hcover,hrank,eH,eV,heK,heV⟩
/-- The same original branch in the literal projective matrix convention of13.7.6(1). -/
theorem projective_four_source_case_of_one_le
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : (K ⧸ pCore 2 K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH projectiveFourRepresentation eK) :
    (H : Set G) = (K : Set G) * (T : Set G) ∧
    Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
    ∃ (eH : Section08.Source.Hstar H ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2))
      (eV : Additive (Section08.Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2)),
      (∀ k : K, eH (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)) =
        eK (QuotientGroup.mk' (pCore 2 K) k)) ∧
      ∀ a v, eV (ρ a v) = projectiveFourRepresentation (eH a) (eV v) := by
  let c := BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 4)
  have hs' : HasSectionModel H V₃ V₁ ρ K hKH (linearRepresentation 4) (eK.trans c) := by
    obtain ⟨hst,e,he⟩ := hs
    exact ⟨hst,e,he⟩
  obtain ⟨hp,hc,_,eH,eV,heK,heV⟩ :=
    linear_four_source_case_of_one_le d h hH hF9 hcentral hKH hK hL₁K ρ hρ (eK.trans c) hs'
  refine ⟨hp,hc,eH.trans c.symm,eV,?_,?_⟩
  · intro k
    change c.symm (eH (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k))) = _
    rw [heK]
    exact c.symm_apply_apply _
  · intro a v
    change eV (ρ a v) = linearRepresentation 4 (c (c.symm (eH a))) (eV v)
    rw [c.apply_symm_apply]
    exact heV a v
end CFSG.Quasithin.Chapter13.Section07.ModelExclusions
