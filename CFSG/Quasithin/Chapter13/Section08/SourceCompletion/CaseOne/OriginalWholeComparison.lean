module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalWholePermutation
public import CFSG.Quasithin.ChapterG.Section05.Structure.PairQuotients
public import Theory.GroupTheory.Commutator.ConjugateSpan
public import Theory.Representation.BinaryConjugationSection.Coinvariants

/-!
# The marked permutation comparison on the original whole section

The proved equality U₀ = U_L and the local identity U₂ = [U₂,L₂] imply
U_L = [U_L,L]. Hence the actual whole-section action has full movement.
The faithful six-letter marking sends the original L-image exactly onto A₆:
its kernel is the original central core and its image has index two.

Apply the G.5.3 pair-quotient comparison to this literal U_L/V action,
retaining its centralizer kernel, quotient map and conjugation formula.
The natural alternative is a whole-module isomorphism; the cover alternative
is a surjection and does not yet assert whole-module dimension five.
OriginalWholeCover excludes the natural alternative from the source hypotheses.

Source: Aschbacher--Smith, proof of 13.8.33, printed p.967. Earlier 13.5.4
and 13.7.6 inputs retain their independent source producers.
-/

public section
open Subgroup Representation CFSG.Quasithin.ChapterG.Section05.Structure
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open TransvectionRecognition.Component.ModelExtension A6Endgame.IntersectionBalance
open TransvectionQuotients TransvectionQuotients.FourLocalFactors TransvectionParabolic FiveSeed
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

omit [Finite G] in
/-- Generation by group commutators gives full movement on the literal quotient action. -/
theorem section_fully_moved {A : Type*} [Group A]
    (U Z P R : Subgroup G) [(Z.subgroupOf U).Normal]
    [IsElementaryAbelian 2 (U ⧸ Z.subgroupOf U)]
    (hUP : U ≤ P) (hZU : Z ≤ U) (hRP : R ≤ P)
    (π : P →* A) (hn : P ≤ normalizer (U : Set G))
    (ρ : Representation (ZMod 2) A (Additive (U ⧸ Z.subgroupOf U)))
    (hρ : SectionConjugationAlong P U Z π hn ρ)
    (hgen : U = ⁅U,R⁆) : Coinvariants.ker ρ = ⊤ := by
  let d : BinaryConjugationSection P U Z (ρ.comp π) := {
    section_le := hUP
    kernel_le := hZU
    normalized := hn
    coordinates := {
      toFun u := Multiplicative.ofAdd (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) u))
      map_one' := rfl
      map_mul' _ _ := rfl }
    onto := QuotientGroup.mk'_surjective _
    kernel_eq := QuotientGroup.ker_mk' _
    equivariant := fun p u => (hρ p u).symm }
  apply d.coinvariants_eq_top_of_group_generation R hRP ρ (π.comp (inclusion hRP))
    (fun _ _ => rfl)
  rw [commutator_comm, ← hgen, sup_eq_left.mpr hZU]

/-- The original L-image is exactly A₆ under every faithful six-letter
marking of the literal centralizer quotient. -/
theorem original_whole_actor_component
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    [(actorKernel (L ⊔ (T : Subgroup G)) V).Normal]
    (eB : ((L ⊔ (T : Subgroup G) : Subgroup G) ⧸
      actorKernel (L ⊔ (T : Subgroup G)) V) ≃* Equiv.Perm (Fin 6)) :
    (eB.toMonoidHom.comp ((QuotientGroup.mk' (actorKernel (L ⊔ (T : Subgroup G)) V)).comp
      (inclusion (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)))).range =
        alternatingGroup (Fin 6) := by
  let ψ := eB.toMonoidHom.comp ((QuotientGroup.mk' (actorKernel (L ⊔ (T : Subgroup G)) V)).comp
    (inclusion (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)))
  have hk : ψ.ker = centralCore L := by
    ext l
    change eB (QuotientGroup.mk' (actorKernel (L ⊔ (T : Subgroup G)) V)
      (inclusion le_sup_left l)) = 1 ↔ l ∈ centralCore L
    rw [map_eq_one_iff eB eB.injective]
    change ((inclusion le_sup_left l : (L ⊔ (T : Subgroup G) : Subgroup G)) :
      (L ⊔ (T : Subgroup G) : Subgroup G) ⧸ actorKernel (L ⊔ (T : Subgroup G)) V) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, d.centralCore_eq_centralizer]
    rfl
  have hc : Nat.card ψ.range = 360 := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv,
      Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hk).toEquiv,
      Nat.card_congr d.local_quotient.toEquiv]
    exact Theory.SpecificGroups.SymmetricSix.a6_order
  have hi := ψ.range.index_mul_card
  rw [hc,Theory.SpecificGroups.SymmetricSix.s6_order] at hi
  change ψ.range = alternatingGroup (Fin 6)
  exact Equiv.Perm.eq_alternatingGroup_of_index_eq_two (by omega)

variable [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- The constructed local orbit generates the whole span by L-commutators. -/
theorem full_denominators_span_generated
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
    Source.UL L H V₃ = ⁅Source.UL L H V₃,L⁆ := by
  have heq := full_denominators_U0_eq_UL d h c hDH hDg hH hcentral hHz K hK hprod
    eL a e model earlier1354 earlier1376 chief
  obtain ⟨_,F,hF,hp⟩ := full_denominators_abelian_cover d h c hDH hDg hH hcentral hHz
    K hK hprod eL a e model earlier1354 earlier1376 chief
  obtain ⟨hseed,_,_,_,_,hcomm,hU₂⟩ := original_cover_orbit d h c hDH hDg hHz K hK hprod
    eL a e F hF hp earlier1354 earlier1376
  have hL₂ := EarlierCore.localResidual_le L V₂
  have hU₂C : Source.U2 H V V₂ ≤ ⁅Source.UL L H V₃,L⁆ :=
    hcomm.le.trans (commutator_mono hU₂ hL₂)
  have hB₂ : conjugateSpanBy V₃ (Source.K2 H V₂) ≤ Source.U2 H V V₂ :=
    conjugateSpanBy_mono d.seed_le le_rfl
  have hnUL : L ≤ normalizer (Source.UL L H V₃ : Set G) := le_normalizer_conjugateSpanBy _ _
  have hnorm : L ≤ normalizer ((⁅Source.UL L H V₃,L⁆ : Subgroup G) : Set G) := by
    intro l hl
    rw [mem_normalizer_iff_map_conj_eq, map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hnUL hl),
      mem_normalizer_iff_map_conj_eq.mp (L.le_normalizer hl)]
  apply le_antisymm
  · apply heq.symm.le.trans
    exact conjugateSpanBy_le (hseed.trans (hB₂.trans hU₂C)) hnorm
  · exact le_normalizer_iff_commutator_le_left.mp (le_normalizer_conjugateSpanBy _ _)

/-- G.5.3(3) on the literal whole section, with its original actor kernel.
The five-dimensional conclusion here is a quotient, not an assumed whole-module isomorphism. -/
theorem full_denominators_whole_comparison
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
    IsMulCommutative (Source.UL L H V₃) ∧
    Source.UL L H V₃ = ⁅Source.UL L H V₃,L⁆ ∧
    ∃ hUL : L ⊔ (T : Subgroup G) ≤ normalizer (Source.UL L H V₃ : Set G),
      ∃ hN : (V.subgroupOf (Source.UL L H V₃)).Normal,
        let _ := hN
        ∃ hE : IsElementaryAbelian 2 (Source.ULsection L H V₃ V),
          let _ := hE
          ∃ hA : (actorKernel (L ⊔ (T : Subgroup G)) V).Normal,
            let _ := hA
            ∃ eB : ((L ⊔ (T : Subgroup G) : Subgroup G) ⧸
                actorKernel (L ⊔ (T : Subgroup G)) V) ≃* Equiv.Perm (Fin 6),
              (eB.toMonoidHom.comp ((QuotientGroup.mk' (actorKernel (L ⊔ (T : Subgroup G)) V)).comp
                (inclusion (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)))).range =
                  alternatingGroup (Fin 6) ∧
              ∃ ρ : Representation (ZMod 2)
                  ((L ⊔ (T : Subgroup G) : Subgroup G) ⧸ actorKernel (L ⊔ (T : Subgroup G)) V)
                  (Additive (Source.ULsection L H V₃ V)),
                SectionConjugationAlong (L ⊔ (T : Subgroup G)) (Source.UL L H V₃) V
                  (QuotientGroup.mk' (actorKernel (L ⊔ (T : Subgroup G)) V)) hUL ρ ∧
                Coinvariants.ker ρ = ⊤ ∧
                (let σ := ρ.comp (eB.symm.toMonoidHom.comp (alternatingGroup (Fin 6)).subtype)
                 (Nonempty (Representation.Equiv (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)) σ) ∨
                   ∃ q : Representation.IntertwiningMap σ (BinaryPermutation.alternatingCoreRepresentation (Fin 6)),
                     Function.Surjective q)) ∧
                (Module.finrank (ZMod 2) (Additive (Source.ULsection L H V₃ V)) = 4 ∨
                  Module.finrank (ZMod 2) (Additive (Source.ULsection L H V₃ V)) = 5 ∨
                  Module.finrank (ZMod 2) (Additive (Source.ULsection L H V₃ V)) = 9 ∨
                  Module.finrank (ZMod 2) (Additive (Source.ULsection L H V₃ V)) = 10 ∨
                  Module.finrank (ZMod 2) (Additive (Source.ULsection L H V₃ V)) = 14) := by
  obtain ⟨hab,hlt,p,hbij,hwhole⟩ := full_denominators_whole_permutation d h c hDH hDg hH
    hcentral hHz K hK hprod eL a e model earlier1354 earlier1376 chief
  let _ := p.actor_normal
  obtain ⟨hUL,hN,hE,ρ,hρ,f,hf⟩ := hwhole
  let _ := hN
  let _ := hE
  let eB := MulEquiv.ofBijective p.permutation hbij
  have hgen := full_denominators_span_generated d h c hDH hDg hH hcentral hHz
    K hK hprod eL a e model earlier1354 earlier1376 chief
  have hUP : Source.UL L H V₃ ≤ L ⊔ (T : Subgroup G) :=
    (Section07.span_UH_L_le_core (localNaturalSetup d) h
      (show IsMulCommutative (Source.UH H V₃) from inferInstance)).trans (pCoreIn_le 2 _)
  have hg := section_fully_moved (Source.UL L H V₃) V (L ⊔ (T : Subgroup G)) L
    hUP hlt.le le_sup_left (QuotientGroup.mk' (actorKernel (L ⊔ (T : Subgroup G)) V))
    hUL ρ hρ hgen
  let : Nontrivial (Additive (Source.ULsection L H V₃ V)) := by
    obtain ⟨u,hu,hnu⟩ := SetLike.exists_of_lt hlt
    refine ⟨⟨Additive.ofMul (QuotientGroup.mk' (V.subgroupOf (Source.UL L H V₃)) ⟨u,hu⟩),0,?_⟩⟩
    intro he
    exact hnu ((QuotientGroup.eq_one_iff (⟨u,hu⟩ : Source.UL L H V₃)).mp he)
  have hc := marked_pair_comparison ρ eB f hf hg
  exact ⟨hab,hgen,hUL,hN,hE,p.actor_normal,eB,original_whole_actor_component d eB,ρ,hρ,hg,hc⟩

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
