module
public import CFSG.Quasithin.Chapter13.Section07.ComponentPlaneSource
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.Signalizer
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Components.IntrinsicSource
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Fitting.SupercriticalSource.StarPlacement
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.SmallMoved.OrderExclusions
/-!
# The restricted source catalogue in the fixed-layer contrary case

The original fixed layer U₀ lies in Ω₁Z(O₂(H)). If the selected C-component
moves it, the intrinsic signalizer module is nontrivial; characteristic-two
inheritance therefore puts the actual ambient component in the faithful
local family. The named earlier13.3.2(1--2) hypothesis supplies its five
quotient models. Intersecting their orders with the proved13.7.15 actor
catalogue leaves A5, PSL3(2), or A6, and hence the quoted four-model list.

The final theorem applies this argument to the original selected component,
using the literal action, offender, and quotient maps. It discharges the
restricted catalogue input of13.7.16(2), conditional on the genuine earlier
`Source1332OneTwo`; it does not claim an unconditional proof of13.5.2.

Source: Aschbacher--Smith,13.3.2(1--2),13.5.2(1),13.7.15--16, pp.884--885,943--944.
-/
public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion ChapterF.Section09.Setup ChapterB.QuasisimpleSource
open Section03.Noncentrality Section03.Noncentrality.SupercriticalSource
variable {G : Type*} [Group G] [Finite G]

theorem PlusAction.component_faithful_of_fixedLayer_movement
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    (hE : IsElementaryAbelian 2 D.UH) (K : Subgroup D.H) (hK : K.IsCComponent)
    (hm : ⁅fixedLayer D,K.map D.H.subtype⁆ ≠ ⊥) :
    K.map D.H.subtype ∈ MainForward.faithfulLocalComponents D.T := by
  have hHe : D.H ∈ Chapter1.He G := Chapter1.mem_He_iff.mpr (by
    simpa only [h.characteristic_H] using centralizer_generalizedFitting_le D.H)
  have hH : D.H ∈ Chapter1.H G := by
    intro hz
    have hf : fixedLayer D = ⊥ := le_bot_iff.mp
      ((inf_le_left.trans h.UH_le_QH).trans_eq hz)
    exact hm (by simp [hf])
  have ha := fixedLayer_le_omegaCenter h hE
  have hω : (Stellmacher.omegaOneCenterAmbient (pCore 2 D.H)).map D.H.subtype =
      Stellmacher.omegaOneCenterAmbient (D.H.pCoreIn 2) :=
    (Stellmacher.omegaOneCenterAmbient_map_injective D.H.subtype D.H.subtype_injective _).symm
  have hUH : fixedLayer D ≤ D.H := inf_le_left.trans h.UH_le_H
  have hUi : (fixedLayer D).subgroupOf D.H ≤ Stellmacher.omegaOneCenterAmbient (pCore 2 D.H) := by
    intro u hu
    have hh := ha hu
    change _ ∈ Stellmacher.omegaOneCenterAmbient (D.H.pCoreIn 2) at hh
    rw [← hω] at hh
    obtain ⟨v,hv,he⟩ := hh
    exact (D.H.subtype_injective he) ▸ hv
  have hmi : ⁅(fixedLayer D).subgroupOf D.H,K⁆ ≠ ⊥ := by
    intro he
    have hh := congrArg (fun A : Subgroup D.H => A.map D.H.subtype) he
    rw [map_commutator,map_subgroupOf_eq_of_le hUH,Subgroup.map_bot] at hh
    exact hm hh
  exact (Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff D.T _).mpr
    (source_component_faithful_local D.T D.H h.T_le_H hH hHe K _ hK hUi hmi)


/-- The earlier faithful-local list, restricted by the actual small-offender
catalogue, leaves these three ordinary models. In particular it lies in
13.5.2(1)'s four-model list, which also permits the triple cover of A6. -/
@[expose] def FixedLayerOrdinaryModel (Q : Type*) [Group Q] : Prop :=
  Chapter1.Section02.LocalModels.IsAlternating Q 5 ∨
  ClassicalGroup.IsPSL Q 3 2 ∨ Chapter1.Section02.LocalModels.IsAlternating Q 6

theorem PlusAction.component_model_of_fixedLayer_movement
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    (hE : IsElementaryAbelian 2 D.UH) (h1332 : Source1332OneTwo D.T)
    (K : Subgroup D.H) (hK : K.IsCComponent)
    (hm : ⁅fixedLayer D,K.map D.H.subtype⁆ ≠ ⊥)
    (ha : SmallMoved.ActorList (K.map (QuotientGroup.mk' (pCore 2 D.H)))) :
    FixedLayerOrdinaryModel (K.map (QuotientGroup.mk' (pCore 2 D.H))) := by
  have hf := component_faithful_of_fixedLayer_movement h hE K hK hm
  have hmodels := (h1332 _ hf).2
  let eK := K.equivMapOfInjective D.H.subtype D.H.subtype_injective
  let e : Chapter1.XiQuotient (K.map D.H.subtype) ≃*
      K.map (QuotientGroup.mk' (pCore 2 D.H)) :=
    (QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK)).symm.trans
      (cComponentTwoCoreQuotientEquiv hK)
  have hc := (ha.of_mulEquiv e).card_ne_1080_and_6048
  rcases hmodels with ⟨⟨f⟩⟩ | ⟨F,_,_,hF,⟨f⟩⟩ | ⟨⟨f⟩⟩ | hcover |
    ⟨F,_,_,J,hF,hJ,⟨f⟩⟩
  · exact Or.inl ⟨e.symm.trans f⟩
  · exact Or.inr (Or.inl ⟨F,inferInstance,inferInstance,hF,⟨e.symm.trans f⟩⟩)
  · exact Or.inr (Or.inr ⟨e.symm.trans f⟩)
  · apply False.elim
    apply hc.1
    rcases hcover with ⟨_,⟨z⟩,⟨f⟩⟩
    rw [card_eq_card_quotient_mul_card_subgroup (center (Chapter1.XiQuotient (K.map D.H.subtype))),
      Nat.card_congr f.toEquiv,Nat.card_congr z.toEquiv,nat_card_alternatingGroup]
    norm_num
  · exact (hc.2 ((Nat.card_congr f.toEquiv).trans
      (BenderSuzuki.MatrixGroups.HermitianForm.TernaryPerfectCover.card_projective J hF hJ))).elim


variable {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d
/-- The contrary case of original13.7.16(2) has exactly the four model
possibilities quoted from13.5.2(1), on the selected literal image in H/O₂(H).
The earlier13.3.2(1--2) source remains an explicit genuine premise. -/
theorem source_plus_component_catalogue_of_fixedLayer_movement
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hs : (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) g)^2 = 1)
    (hout : ¬ conjugate V₁ (g : G) ≤ Section08.Source.UH H V₃)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (H ⧸ pCore 2 H) W)
    (s : Representation.BinaryConjugationSection H (Section08.Source.UH H V₃)
      ((Section08.Source.UH H V₃) ⊓ centralizer (H.pCoreIn 2 : Set G))
      (σ.comp (QuotientGroup.mk' (pCore 2 H))))
    (B : Subgroup (H ⧸ pCore 2 H)) (hB : IsMinimalBestOffender σ B)
    (hBA : B ≤ ((conjugate (Section08.Source.VH H V) (g : G) ⊓
      (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2).subgroupOf H).map
        (QuotientGroup.mk' (pCore 2 H)))
    (K : Subgroup H) (hKC : K.IsCComponent) (hK : IsComponent (H ⧸ pCore 2 H)
      (K.map (QuotientGroup.mk' (pCore 2 H))))
    (hk : PlusAction.kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) = H.pCoreIn 2)
    (hcomm : ⁅K.map (QuotientGroup.mk' (pCore 2 H)),B⁆ = K.map (QuotientGroup.mk' (pCore 2 H)))
    (h1332 : Source1332OneTwo T)
    (hm : ⁅PlusAction.fixedLayer (ConjugateIntersections.sourceSetup T L V V₃ V₁ H),
      K.map H.subtype⁆ ≠ ⊥) :
    Chapter1.Section02.LocalModels.IsAlternating (K.map (QuotientGroup.mk' (pCore 2 H))) 5 ∨
    ClassicalGroup.IsPSL (K.map (QuotientGroup.mk' (pCore 2 H))) 3 2 ∨
    Chapter1.Section02.LocalModels.IsAlternating (K.map (QuotientGroup.mk' (pCore 2 H))) 6 ∨
    Chapter1.Section02.LocalModels.IsAlternatingCover (K.map (QuotientGroup.mk' (pCore 2 H))) 6 := by
  have ha := (source_plus_component_irrPlus_and_actor d h hU hV hne g hs hout
    σ s B hB hBA K hK hk hcomm).2
  let : IsElementaryAbelian 2 V := NaturalAction.elementary d
  let : IsElementaryAbelian 2 V₃ := IsElementaryAbelian.of_le d.seed_le
  let : IsMulCommutative (conjugateSpanBy V₃ H) := hU
  have hh := PlusAction.component_model_of_fixedLayer_movement h
    (conjugateSpanBy_elementary_of_commutative V₃ H) h1332 K hKC hm ha
  rcases hh with h5 | h3 | h6
  · exact Or.inl h5
  · exact Or.inr (Or.inl h3)
  · exact Or.inr (Or.inr (Or.inl h6))

end CFSG.Quasithin.Chapter13.Section07
