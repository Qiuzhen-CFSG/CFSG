module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalCentralizerAction
public import Theory.Representation.CentralizerCosetEmbedding

/-!
# The original seed-centralizer permutation embedding

An index-two seed centralizer gives a binary functional on the literal
Q/C_Q(U_L). The corrected representatives in L₁T fix that functional, and
five actual seed conjugates separate the quotient. Evaluation on cosets
therefore embeds the quotient in the fifteen-pair permutation module.
The point stabilizer is obtained from the original natural action and
its marked seed line; the central kernel and actor map are unchanged.

Source: Aschbacher--Smith, 13.8.33, printed pp.967--968. This supplies the
noncentral quotient for the subsequent chief-factor comparison. It does
not assert the central-seed exclusion or strictness of the denominators.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open TransvectionRecognition.Component.ModelExtension A6Endgame.IntersectionBalance
open TransvectionQuotients TransvectionQuotients.FourLocalFactors TransvectionParabolic FiveSeed
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

theorem original_seed_pair_stabilizer
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hsurj : Function.Surjective (Section07.NaturalAction.permutation (localNaturalSetup d))) :
    ∃ s : BinaryPermutation.SixPairsQuadratic.Pair, ∀ a : Equiv.Perm (Fin 6),
      a ∈ ((sourceOne L T V₁ ⊔ (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G))).map
        (Section07.NaturalAction.permutation (localNaturalSetup d)) ↔
      BinaryPermutation.SixPairsQuadratic.pairPerm a s = s := by
  let _ := local_elementary d
  let P := L ⊔ (T : Subgroup G)
  let π := Section07.NaturalAction.permutation (localNaturalSetup d)
  let E : Additive V ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6) :=
    d.coordinate.toAdditiveLeft.toLinearEquiv (ZMod.map_smul _)
  obtain ⟨s,hs⟩ := BarMarking.exists_pair_of_flag P V V₁ d.normalizes_V
    (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)) d.line_card E π
    (fun p v => Section07.NaturalAction.conjugation (localNaturalSetup d) p v.toMul)
  have hR : sourceOne L T V₁ ⊔ (T : Subgroup G) = P ⊓ normalizer (V₁ : Set G) := by
    rw [original_point_parabolic_eq d (H := G₁) rfl,d.first_normalizer]
  refine ⟨s,fun a => ?_⟩
  constructor
  · rintro ⟨p,hp,rfl⟩
    apply (hs p).mp
    change (p : G) ∈ sourceOne L T V₁ ⊔ (T : Subgroup G) at hp
    rw [hR] at hp
    exact hp.2
  · intro ha
    obtain ⟨p,rfl⟩ := hsurj a
    refine ⟨p,?_,rfl⟩
    change (p : G) ∈ sourceOne L T V₁ ⊔ (T : Subgroup G)
    rw [hR]
    exact ⟨p.property,(hs p).mpr ha⟩

variable [IsElementaryAbelian 2 (Source.UH H V₃)]

theorem full_denominators_noncentral_seed_functional
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hH : H = G₁)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (K : Subgroup G) (hK : (K.subgroupOf H).IsCComponent)
    (hprod : (H : Set G) = (K : Set G) * (T : Set G))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (model : CompatibleModel H V₃ V₁ a e)
    (earlier1354 : EarlierCore.Earlier1354 T L V)
    (earlier1376 : Marking.NaturalSection.Earlier1376 L (EarlierCore.localResidual L V₁)
      T (normalizer (V₁ : Set G)) M V₂ V₃ V₁)
    (chief : ChiefGeneration.Earlier1376ChiefFactors (sourceOne L T V₁) T G₁ M V₃ V₁)
    (hnc : ¬ Source.U1 H K V₃ ≤
      centralizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)) :
    let P := L ⊔ (T : Subgroup G)
    let Q := P.pCoreIn 2
    let C := A6Endgame.ActionAnalysis33.CQUL Q L H V₃
    let R := sourceOne L T V₁ ⊔ (T : Subgroup G)
    let π := Section07.NaturalAction.permutation (localNaturalSetup d)
    ∃ u : Source.U1 H K V₃, (u : G) ∉ V ∧
    ∃ hN : (C.subgroupOf Q).Normal,
      let _ := hN
      ∃ hE : IsElementaryAbelian 2 (Q ⧸ C.subgroupOf Q),
        let _ := hE
        ∃ hn : P ≤ normalizer (Q : Set G),
          ∃ ρ : Representation (ZMod 2) (Equiv.Perm (Fin 6))
              (Additive (Q ⧸ C.subgroupOf Q)),
            SectionConjugationAlong P Q C π hn ρ ∧
            1 ≤ Module.finrank (ZMod 2) (Additive (Q ⧸ C.subgroupOf Q)) ∧
            Module.finrank (ZMod 2) (Additive (Q ⧸ C.subgroupOf Q)) ≤ 5 ∧
            ∃ f : Additive (Q ⧸ C.subgroupOf Q) →ₗ[ZMod 2] ZMod 2,
              (∀ q : Q, f (Additive.ofMul (QuotientGroup.mk' _ q)) = 0 ↔
                (q : G) ∈ centralizer ({(u : G)} : Set G)) ∧
              (∀ a ∈ (R.subgroupOf P).map π, ∀ x, f (ρ a x) = f x) ∧
              (∀ x, (∀ a, f (ρ a x) = 0) → x = 0) := by
  obtain ⟨_,_,_,hN,hE,hn,ρ,hρ,hpos,hd⟩ := full_denominators_noncentral_core_action
    d h c hDH hDg hH hcentral hHz K hK hprod eL a e model earlier1354 earlier1376 chief hnc
  dsimp only [A6Endgame.ActionAnalysis33.CQUL] at hN hE
  let _ : ((((L ⊔ (T : Subgroup G)).pCoreIn 2) ⊓ centralizer (Source.UL L H V₃ : Set G)).subgroupOf
    ((L ⊔ (T : Subgroup G)).pCoreIn 2)).Normal := hN
  let _ : IsElementaryAbelian 2 (((L ⊔ (T : Subgroup G)).pCoreIn 2) ⧸
      (((L ⊔ (T : Subgroup G)).pCoreIn 2) ⊓ centralizer (Source.UL L H V₃ : Set G)).subgroupOf
        ((L ⊔ (T : Subgroup G)).pCoreIn 2)) := hE
  obtain ⟨u,hu,g,hgen⟩ := full_denominators_seed_generators d h c hDH hDg
    hH hcentral hHz K hK hprod eL a e model earlier1354 earlier1376 chief
  obtain ⟨_,F,hF,hp⟩ := full_denominators_abelian_cover d h c hDH hDg
    hH hcentral hHz K hK hprod eL a e model earlier1354 earlier1376 chief
  obtain ⟨hi,_,him⟩ := original_cover_seed_parabolic_centralizer d h c hDH hDg
    hHz K hK hprod a e F hF hp u hu hH eL hnc
  refine ⟨u,hu,hN,hE,hn,ρ,hρ,hpos,hd,?_⟩
  exact CentralizerCosetEmbedding.exists_separating_functional
    (L ⊔ (T : Subgroup G)) ((L ⊔ (T : Subgroup G)).pCoreIn 2)
    (Source.UL L H V₃) V (sourceOne L T V₁ ⊔ (T : Subgroup G))
    (Section07.NaturalAction.permutation (localNaturalSetup d)) hn ρ hρ
    ⟨u,(le_conjugateSpanBy _ _) u.property.1⟩ hi him
    (fun i => inclusion le_sup_left (g i)) hgen
    (localNaturalSetup d).chosen.core_centralizes

theorem full_denominators_noncentral_pair_embedding
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hH : H = G₁)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (K : Subgroup G) (hK : (K.subgroupOf H).IsCComponent)
    (hprod : (H : Set G) = (K : Set G) * (T : Set G))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (model : CompatibleModel H V₃ V₁ a e)
    (earlier1354 : EarlierCore.Earlier1354 T L V)
    (earlier1376 : Marking.NaturalSection.Earlier1376 L (EarlierCore.localResidual L V₁)
      T (normalizer (V₁ : Set G)) M V₂ V₃ V₁)
    (chief : ChiefGeneration.Earlier1376ChiefFactors (sourceOne L T V₁) T G₁ M V₃ V₁)
    (hnc : ¬ Source.U1 H K V₃ ≤
      centralizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)) :
    let P := L ⊔ (T : Subgroup G)
    let Q := P.pCoreIn 2
    let C := A6Endgame.ActionAnalysis33.CQUL Q L H V₃
    ∃ hN : (C.subgroupOf Q).Normal,
      let _ := hN
      ∃ hE : IsElementaryAbelian 2 (Q ⧸ C.subgroupOf Q),
        let _ := hE
        ∃ hn : P ≤ normalizer (Q : Set G),
          ∃ ρ : Representation (ZMod 2) (Equiv.Perm (Fin 6))
              (Additive (Q ⧸ C.subgroupOf Q)),
            SectionConjugationAlong P Q C
              (Section07.NaturalAction.permutation (localNaturalSetup d)) hn ρ ∧
            1 ≤ Module.finrank (ZMod 2) (Additive (Q ⧸ C.subgroupOf Q)) ∧
            Module.finrank (ZMod 2) (Additive (Q ⧸ C.subgroupOf Q)) ≤ 5 ∧
            ∃ j : ρ.IntertwiningMap BinaryPermutation.SixPairsQuadratic.action,
              Function.Injective j := by
  classical
  obtain ⟨_,_,hN,hE,hn,ρ,hρ,hpos,hd,f,_,hf,hsep⟩ :=
    full_denominators_noncentral_seed_functional d h c hDH hDg hH hcentral hHz
      K hK hprod eL a e model earlier1354 earlier1376 chief hnc
  let _ := hN
  let _ := hE
  obtain ⟨s,hs⟩ := original_seed_pair_stabilizer d
    (full_denominators_natural_surjective d h c hDH hDg)
  let D := ((sourceOne L T V₁ ⊔ (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G))).map
    (Section07.NaturalAction.permutation (localNaturalSetup d))
  let _ : Fintype ((Equiv.Perm (Fin 6)) ⧸ D) := Fintype.ofFinite _
  let E := BinaryPermutation.SixPairsQuadratic.pairCosets (MonoidHom.id (Equiv.Perm (Fin 6)))
    (fun g => ⟨g.val,rfl⟩) D s hs
  have hE' := BinaryPermutation.SixPairsQuadratic.pairCosets_equivariant
    (MonoidHom.id (Equiv.Perm (Fin 6))) (fun g => ⟨g.val,rfl⟩) D s hs
  obtain ⟨j,hj⟩ := BinaryCosetFunctional.exists_reindexed_embedding ρ D f hf hsep
    BinaryPermutation.SixPairsQuadratic.pairHom E hE'
  exact ⟨hN,hE,hn,ρ,hρ,hpos,hd,j,hj⟩

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
