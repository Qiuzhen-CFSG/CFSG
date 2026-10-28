module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalCentralizerCubic

/-!
# The whole cover in the original six-letter action

The previously constructed whole section U_L/V is the five-dimensional
augmentation cover. Reindex its original coset surjection using the literal
natural action on V and the actual point stabilizer. This identifies the
whole section under that same action, including its constant line and
original actor kernel. Restriction to the specified outer-marked cubic
therefore contributes exactly one to the source filtration.

The final source application is in OriginalLeftFiltration. The central-seed
13.4.1 argument, H-side dual comparison and strict denominators remain open.
Source: Aschbacher--Smith, 13.8.33, printed pp.967--968.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open TransvectionRecognition.Component.ModelExtension A6Endgame.IntersectionBalance
open TransvectionQuotients TransvectionQuotients.FourLocalFactors TransvectionParabolic FiveSeed
open A6Endgame.ActionAnalysis33.ChiefModels
open Representation.BinaryFixedPoints
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

private noncomputable def CoverPermutationData.remark
    (p : CoverPermutationData L H K (T : Subgroup G) (sourceOne L T V₁) V₃ V)
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hsur : Function.Surjective (Section07.NaturalAction.permutation (localNaturalSetup d))) :
    CoverPermutationData L H K (T : Subgroup G) (sourceOne L T V₁) V₃ V := by
  classical
  let _ := p.actor_normal
  let P := L ⊔ (T : Subgroup G)
  let N := actorKernel P V
  let π := Section07.NaturalAction.permutation (localNaturalSetup d)
  have hk : π.ker = N := by
    ext x
    exact Section07.permutation_eq_one_iff (localNaturalSetup d) x
  let E := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective π hsur)
  let f := E.toMonoidHom
  have he (x : P) : f (QuotientGroup.mk' N x) = π x := rfl
  let s := (original_seed_pair_stabilizer d hsur).choose
  have hs := (original_seed_pair_stabilizer d hsur).choose_spec
  have hstab (x : P ⧸ N) :
      x ∈ ((sourceOne L T V₁ ⊔ (T : Subgroup G)).subgroupOf P).map (QuotientGroup.mk' N) ↔
        BinaryPermutation.SixPairsQuadratic.pairPerm (f x) s = s := by
    rw [← hs]
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨y,hy,(he y).symm⟩
    · rintro ⟨y,hy,hyx⟩
      exact ⟨y,hy,E.injective ((he y).trans hyx)⟩
  have halt (g : alternatingGroup (Fin 6)) : ∃ x, f x = g.val := E.surjective g.val
  exact { p with
    permutation := f
    faithful := E.injective
    alternating := halt
    pair := s
    stabilizer := hstab
    cosets := BinaryPermutation.SixPairsQuadratic.pairCosets f halt _ s hstab
    equivariant := BinaryPermutation.SixPairsQuadratic.pairCosets_equivariant f halt _ s hstab }

private theorem CoverPermutationData.remark_permutation
    (p : CoverPermutationData L H K (T : Subgroup G) (sourceOne L T V₁) V₃ V)
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hsur : Function.Surjective (Section07.NaturalAction.permutation (localNaturalSetup d)))
    (x : (L ⊔ (T : Subgroup G) : Subgroup G)) :
    let _ := (p.remark d hsur).actor_normal
    (p.remark d hsur).permutation (QuotientGroup.mk' (actorKernel (L ⊔ (T : Subgroup G)) V) x) =
      Section07.NaturalAction.permutation (localNaturalSetup d) x := by rfl

theorem CoverPermutationData.whole_natural_action
    (p : CoverPermutationData L H K (T : Subgroup G) (sourceOne L T V₁) V₃ V)
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hsur : Function.Surjective (Section07.NaturalAction.permutation (localNaturalSetup d)))
    (heq : Source.U0 L H K V₃ = Source.UL L H V₃) :
    ∃ hn : L ⊔ (T : Subgroup G) ≤ normalizer (Source.UL L H V₃ : Set G),
      ∃ hN : (V.subgroupOf (Source.UL L H V₃)).Normal,
        let _ := hN
        ∃ hE : IsElementaryAbelian 2 (Source.ULsection L H V₃ V),
          let _ := hE
          ∃ ρ : Representation (ZMod 2) (Equiv.Perm (Fin 6))
              (Additive (Source.ULsection L H V₃ V)),
            SectionConjugationAlong (L ⊔ (T : Subgroup G)) (Source.UL L H V₃) V
              (Section07.NaturalAction.permutation (localNaturalSetup d)) hn ρ ∧
            ∃ q : BinaryPermutation.SixPairsQuadratic.action.IntertwiningMap ρ,
              Function.Surjective q := by
  let p' := p.remark d hsur
  let _ := p'.actor_normal
  obtain ⟨hn,hN,hE,τ,hτ,q,hq⟩ := p'.wholeSection_of_eq heq
  let _ := hN
  let _ := hE
  have hsur' : Function.Surjective p'.permutation := by
    intro z
    obtain ⟨x,rfl⟩ := hsur z
    exact ⟨QuotientGroup.mk' _ x, p.remark_permutation d hsur x⟩
  let E := MulEquiv.ofBijective p'.permutation ⟨p'.faithful,hsur'⟩
  let ρ := τ.comp E.symm.toMonoidHom
  have hρ : SectionConjugationAlong (L ⊔ (T : Subgroup G)) (Source.UL L H V₃) V
      (Section07.NaturalAction.permutation (localNaturalSetup d)) hn ρ := by
    intro x u
    change τ (E.symm (Section07.NaturalAction.permutation (localNaturalSetup d) x)) _ = _
    rw [← p.remark_permutation d hsur x]
    change τ (E.symm (E (QuotientGroup.mk' _ x))) _ = _
    rw [E.symm_apply_apply]
    exact hτ x u
  let q' : BinaryPermutation.SixPairsQuadratic.action.IntertwiningMap ρ := {
    toLinearMap := q.toLinearMap
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro v
      have he := IntertwiningMap.isIntertwining _ _ q (E.symm g) v
      change q (BinaryPermutation.SixPairsQuadratic.action (E (E.symm g)) v) = _ at he
      rw [E.apply_symm_apply] at he
      exact he }
  exact ⟨hn,hN,hE,ρ,hρ,q',hq⟩

variable [IsElementaryAbelian 2 (Source.UH H V₃)]

theorem full_denominators_whole_original_marking
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
    (chief : ChiefGeneration.Earlier1376ChiefFactors (sourceOne L T V₁) T G₁ M V₃ V₁) :
    ∃ hn : L ⊔ (T : Subgroup G) ≤ normalizer (Source.UL L H V₃ : Set G),
      ∃ hN : (V.subgroupOf (Source.UL L H V₃)).Normal,
        let _ := hN
        ∃ hE : IsElementaryAbelian 2 (Source.ULsection L H V₃ V),
          let _ := hE
          ∃ ρ : Representation (ZMod 2) (Equiv.Perm (Fin 6))
              (Additive (Source.ULsection L H V₃ V)),
            SectionConjugationAlong (L ⊔ (T : Subgroup G)) (Source.UL L H V₃) V
              (Section07.NaturalAction.permutation (localNaturalSetup d)) hn ρ ∧
            Nonempty (Representation.Equiv (ρ.comp (alternatingGroup (Fin 6)).subtype)
              (BinaryPermutation.alternatingCoreRepresentation (Fin 6))) := by
  obtain ⟨_,hlt,p,_,_⟩ := full_denominators_whole_permutation d h c hDH hDg hH
    hcentral hHz K hK hprod eL a e model earlier1354 earlier1376 chief
  have heq := full_denominators_U0_eq_UL d h c hDH hDg hH hcentral hHz
    K hK hprod eL a e model earlier1354 earlier1376 chief
  obtain ⟨hn,hN,hE,ρ,hρ,q,hq⟩ := p.whole_natural_action d
    (full_denominators_natural_surjective d h c hDH hDg) heq
  let _ := hN
  let _ := hE
  have hUP : Source.UL L H V₃ ≤ L ⊔ (T : Subgroup G) :=
    (Section07.span_UH_L_le_core (localNaturalSetup d) h
      (show IsMulCommutative (Source.UH H V₃) from inferInstance)).trans (pCoreIn_le 2 _)
  have hgen := section_fully_moved (Source.UL L H V₃) V (L ⊔ (T : Subgroup G)) L
    hUP hlt.le le_sup_left (Section07.NaturalAction.permutation (localNaturalSetup d))
    hn ρ hρ (full_denominators_span_generated d h c hDH hDg hH hcentral hHz
      K hK hprod eL a e model earlier1354 earlier1376 chief)
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,hd⟩ := full_denominators_whole_cover d h c hDH hDg hH
    hcentral hHz K hK hprod eL a e model earlier1354 earlier1376 chief
  let : Nontrivial (Additive (Source.ULsection L H V₃ V)) := by
    apply Module.nontrivial_of_finrank_pos (R := ZMod 2)
    omega
  obtain ⟨hcases,_⟩ := ChapterG.Section05.Structure.marked_pair_comparison
    ρ (MulEquiv.refl _) q hq hgen
  refine ⟨hn,hN,hE,ρ,hρ,?_⟩
  rcases hcases with hnat | hcover
  · obtain ⟨F⟩ := hnat
    have he := F.toLinearEquiv.finrank_eq
    rw [BinaryPermutation.finrank_natural_even (Fin 6) (by decide),hd] at he
    exact ((by decide : (4 : ℕ) ≠ 5) he).elim
  · obtain ⟨f,hf⟩ := hcover
    have hbij := OrzechProperty.bijective_of_surjective_of_finrank_le f.toLinearMap hf
      (by rw [hd,BinaryPermutation.finrank_core (Fin 6)]; decide)
    exact ⟨Representation.Equiv.mk (LinearEquiv.ofBijective f.toLinearMap hbij)
      (fun g => LinearMap.ext (IntertwiningMap.isIntertwining _ _ f g))⟩

theorem full_denominators_span_cubic_length
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
    (A : Subgroup G) (hAP : A ≤ L ⊔ (T : Subgroup G)) (hA : IsPGroup 3 A)
    (f : A →* cubicActor) (hf : Function.Surjective f)
    (hmark : ∀ b : A, Section07.NaturalAction.permutation (localNaturalSetup d)
      (inclusion hAP b) = (cubicActorEquiv (f b) : Equiv.Perm (Fin 6))) :
    sectionCubicLength A V (Source.UL L H V₃) = 1 := by
  obtain ⟨hn,hN,hE,ρ,hρ,⟨E⟩⟩ := full_denominators_whole_original_marking
    d h c hDH hDg hH hcentral hHz K hK hprod eL a e model earlier1354 earlier1376 chief
  let _ := hN
  let _ := hE
  obtain ⟨_,hlt,_,_,_⟩ := full_denominators_whole_permutation
    d h c hDH hDg hH hcentral hHz K hK hprod eL a e model earlier1354 earlier1376 chief
  have heven (b : cubicActor) : Marked.outer b.val ∈ alternatingGroup (Fin 6) := by
    obtain ⟨n,hn⟩ := cubicGenerator_generates b
    rw [← hn]
    change Marked.outer (cubicGenerator.val ^ n) ∈ alternatingGroup (Fin 6)
    rw [map_zpow]
    apply Subgroup.zpow_mem
    change Marked.outer Marked.pairCycle ∈ alternatingGroup (Fin 6)
    rw [outer_pairCycle]
    decide
  let _ := action ModuleShape.augmentation.opposite
  let φ : Source.UL L H V₃ →* Multiplicative (BinaryPermutation.core (Fin 6)) :=
    E.toLinearEquiv.toAddEquiv.toMultiplicative.toMonoidHom.comp
      (MulEquiv.toMultiplicative_toAdditive.symm.toMonoidHom.comp (QuotientGroup.mk' _))
  let s : OppositeSection A V (Source.UL L H V₃) f .augmentation := {
    le := hlt.le
    normalizes := hAP.trans hn
    projection := φ
    onto := E.toLinearEquiv.surjective.comp (QuotientGroup.mk'_surjective _)
    kernel := by
      ext u
      change E (Additive.ofMul (QuotientGroup.mk' _ u)) = 0 ↔ u ∈ V.subgroupOf (Source.UL L H V₃)
      rw [← map_zero E]
      change E.toLinearEquiv _ = E.toLinearEquiv 0 ↔ _
      rw [E.toLinearEquiv.injective.eq_iff]
      exact QuotientGroup.eq_one_iff u
    equivariant := by
      intro b u
      change E (Additive.ofMul (QuotientGroup.mk' (V.subgroupOf (Source.UL L H V₃))
        ⟨(b : G) * (u : G) * (b : G)⁻¹,_⟩)) =
          BinaryPermutation.coreRepresentation (Fin 6) (Marked.outer (f b).val)
            (E (Additive.ofMul (QuotientGroup.mk' _ u)))
      have he := congrArg (fun x => E x) (hρ (inclusion hAP b) u).symm
      refine he.trans ?_
      rw [hmark b]
      exact IntertwiningMap.isIntertwining _ _ E.toIntertwiningMap
        ⟨Marked.outer (f b).val,heven (f b)⟩ _ }
  exact opposite_section_length .augmentation s hA
    ((isPGroup_pCoreIn 2 (L ⊔ (T : Subgroup G))).to_le
      (Section07.span_UH_L_le_core (localNaturalSetup d) h
        (show IsMulCommutative (Source.UH H V₃) from inferInstance))) hf

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
