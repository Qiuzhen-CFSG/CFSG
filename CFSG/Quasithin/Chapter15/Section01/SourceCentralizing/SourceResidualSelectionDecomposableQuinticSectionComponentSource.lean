module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSectionStrongSource
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSectionComponent
public import Theory.Representation.BinaryConjugationSection.CommutatorImage
public import Theory.Representation.BinaryConjugationSection.ImageDimensions
public import Theory.Representation.BinaryConjugationSection.ConjugateSpan

/-!
# A small component on the original quintic partner section

The original V-image is a strong offender on the literal F/Uc section outside
O₂(Mc). Its moved space lies in the original E/Uc plane. The actual two-local
Mc supplies the SQTK cover, so strict replacement and B.1.9 select a contained
minimal offender centralizing Fitting and moving an actual component. The
component retains Irr⁺ on its whole moved space and the complete small actor
catalogue. No marked generation, residual control or component premise is used.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

/-- The same original section contains a literal component moved by a
minimal strong offender inside the original V-image. -/
theorem PreparedChosenModule.decomposable_five_core_or_section_component
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      Nat.card (localModule T Mc) = 4 →
      let Uc := localModule T Mc
      let F := conjugateSpanBy (thompsonFixed T V) (centralizer (Uc : Set G))
      V ≤ Mc.pCoreIn 2 ∨
        ∃ he : IsElementaryAbelian 2 F,
          letI := he
          ∃ ρ : Representation (ZMod 2) Mc (Additive (F ⧸ Uc.subgroupOf F)),
            Nonempty (BinaryConjugationSection Mc F Uc ρ) ∧
            Function.Injective (Representation.BinaryOffender.imageRepresentation ρ) ∧
            (Representation.BinaryOffender.actionHom ρ).ker.map Mc.subtype =
              commutatorPreimage Mc F Uc ∧
            Nat.card (actionSubgroup ρ (V.subgroupOf Mc)) =
              (commutatorPreimage Mc F Uc).relIndex V ∧
            pCore 2 (Representation.BinaryOffender.actionImage ρ) = ⊥ ∧
            IsStrongOffender (Representation.BinaryOffender.imageRepresentation ρ)
              (actionSubgroup ρ (V.subgroupOf Mc)) ∧
            ∃ B ≤ actionSubgroup ρ (V.subgroupOf Mc),
              IsMinimalBestOffender (Representation.BinaryOffender.imageRepresentation ρ) B ∧
              IsQuadratic (Representation.BinaryOffender.imageRepresentation ρ) B ∧
              IsStrongOffender (Representation.BinaryOffender.imageRepresentation ρ) B ∧
              Module.finrank (ZMod 2) (subspaceCommutator
                (Representation.BinaryOffender.imageRepresentation ρ) ⊤ B) ≤ 2 ∧
              B ≤ centralizer (fittingSubgroup (Representation.BinaryOffender.actionImage ρ) :
                Set (Representation.BinaryOffender.actionImage ρ)) ∧
              ∃ K, IsComponent (Representation.BinaryOffender.actionImage ρ) K ∧ ⁅K,B⁆ = K ∧
                K ≤ normalClosure (B : Set (Representation.BinaryOffender.actionImage ρ)) ∧
                (K.subgroupOf (normalClosure (B : Set (Representation.BinaryOffender.actionImage ρ)))).Normal ∧
                IsIrrPlus (Representation.BinaryOffender.imageRepresentation ρ) K
                  (ChapterB.QuasisimpleSource.moved (Representation.BinaryOffender.imageRepresentation ρ) K) ∧
                ChapterB.QuasisimpleSource.SmallMoved.ActorList K := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  by_cases hVQ : V ≤ Mc.pCoreIn 2
  · exact Or.inl hVQ
  obtain hcore | ⟨heF,ρ,⟨dF⟩,hfaith,hker,hcard,hcore,hoff⟩ :=
    h.decomposable_five_core_or_section_strong_offender
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  · exact (hVQ hcore).elim
  right
  let Uc := localModule T Mc
  let E := thompsonFixed T V
  let C := centralizer (Uc : Set G)
  let F := conjugateSpanBy E C
  let : IsElementaryAbelian 2 F := heF
  let σ := Representation.BinaryOffender.imageRepresentation ρ
  let A := actionSubgroup ρ (V.subgroupOf Mc)
  have hplane : Module.finrank (ZMod 2) (subspaceCommutator σ ⊤ A) ≤ 2 := by
    have hUE : Uc ≤ E := (h.decomposable_five_partner_control
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).2.2
    have hVC : V ≤ C := V.le_centralizer.trans (centralizer_le (hUE.trans inf_le_left))
    have hVMc : V ≤ Mc := hVC.trans (localModule_centralizer_le_partner T Mc hu)
    have hVF : ⁅V,F⁆ ≤ E := by
      rcases h.decomposable_five_partner_core_alternatives
        hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive with hq | hh
      · exact (hVQ hq).elim
      · exact hh.2.2.2.2.1
    have hdim : Module.finrank (ZMod 2) (dF.imageSpace E) = 2 := by
      apply dF.imageSpace_finrank_of_index E (le_conjugateSpanBy E C) 2
      have hm := (Uc.subgroupOf E).index_mul_card
      rw [Nat.card_congr (subgroupOfEquivOfLe hUE).toEquiv] at hm
      change Uc.relIndex E * Nat.card Uc = Nat.card E at hm
      rw [hcU,s.fixed_card] at hm
      change Uc.relIndex E = 2 ^ 2
      have hm' : Uc.relIndex E * 4 = 16 := hm
      norm_num only [Nat.reducePow]
      omega
    have hmove : subspaceCommutator σ ⊤ A ≤ dF.imageSpace E := by
      change subspaceCommutator σ ⊤ ((V.subgroupOf Mc).map
        (Representation.BinaryOffender.actionHom ρ)) ≤ _
      rw [←subspaceCommutator_comp_map]
      change subspaceCommutator ρ ⊤ (V.subgroupOf Mc) ≤ _
      have he := dF.imageSpace_commutator V F hVMc le_rfl
      rw [dF.imageSpace_self] at he
      rw [←he]
      exact dF.imageSpace_mono hVF
    exact (Submodule.finrank_mono hmove).trans_eq hdim
  have hMc : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
  let cover : ChapterB.SourceInduction.SQTKQuotient KnownSimple.IsKnownSimple
      (Representation.BinaryOffender.actionImage ρ) :=
    ⟨Mc,(Representation.BinaryOffender.actionHom ρ).ker,
      hG.twoLocal_sqtk hMc.1.1,
      QuotientGroup.quotientKerEquivOfSurjective
        (Representation.BinaryOffender.actionHom ρ) ρ.asGroupHom.rangeRestrict_surjective⟩
  refine ⟨heF,ρ,⟨dF⟩,hfaith,hker,hcard,hcore,hoff,?_⟩
  exact DecomposableQuinticControl.component_of_strong_plane_offender σ hfaith hcore cover hoff hplane

end CFSG.Quasithin.Chapter15.Section01
