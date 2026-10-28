module
public import CFSG.Quasithin.Chapter14.Section02.ProperDiagramPlacement
public import CFSG.Quasithin.Chapter14.Section02.ProperDiagramOddRank
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.RankTwoPerfect
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import CFSG.Quasithin.Chapter14.Section02.ProperDiagramOriginalMcActor

/-!
# Original diagram placement in rank-two containing rows

The original diagram model supplies an odd rank-two mark on the actual K.
This mark survives its literal image in Mc/O₂(Mc). In a containing component
whose same quotient image is binary PSL₃ or Sp₄ over a nonbinary field, the
full Sylow overgroup theorem exhausts that image. The source comparison then
identifies the actual K with the containing component D.

The first theorem handles one literal containing D. The subsequent placement
and Mc-action consumers retain the exact remaining model-selection premise;
these theorems do not classify all possible containing components. No
movement of the normal subgroup K or quasisimplicity of its quotient image
is assumed.

Source: Aschbacher--Smith 14.2.9 and 14.2.12--13, printed pp.983--984,
using the rank-two cases of 1.2.8(4), printed pp.506--507.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 ChapterE
open Chapter1 Chapter1.Section02
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]

theorem source_diagram_component_eq_of_rank_two_containing_model
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (_hn : 1 < generationParameter H)
    (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (_hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (_hgen : K ⊔ (T.subtype hH.1.1.2 : Subgroup H) = ⊤) {f : ℕ} (hf : 1 < f)
    (hm : DiagramModel ((H ⊓ M).subgroupOf H) K (T.subtype hH.1.1.2 : Subgroup H) f)
    (D : Subgroup G) (hD : D ∈ Chapter1.cComponentsIn Mc)
    (hKD : K.map H.subtype ≤ D)
    (hmodel : ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (n : ℕ),
        1 < n ∧ Nat.card F = 2^n ∧
        (Nonempty ((D.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc)) ≃* PSL(3,F)) ∨
          Nonempty ((D.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc)) ≃*
            Theory.SpecificGroups.SymplecticFour.Sp F))) : K.map H.subtype = D := by
  have hHMc : H ≤ Mc :=
    ((source_lemma_14_2_3 hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2).2).trans
      (InitialSource.centralizer_le_partner T hu)
  have hTMc : (T : Subgroup G) ≤ Mc := hH.1.1.2.trans hHMc
  have hKMc : K.map H.subtype ≤ Mc := (map_subtype_le K).trans hHMc
  have hlocal : K.map H.subtype ∈ L G (T : Subgroup G) := by
    apply (lemma_1_2_6 T hH.1.1).2
    apply (lemma_1_2_6 T hH.1.1).1
    refine ⟨map_subtype_le K,?_⟩
    simpa only [subgroupOf,comap_map_eq_self_of_injective H.subtype_injective] using hK
  have hKM : (K.map H.subtype).subgroupOf Mc ∈ L Mc (T.subtype hTMc) :=
    (mem_LIn_iff_subgroupOf hTMc hKMc).mp ⟨hKMc,hlocal⟩
  let eK : K ≃* (K.map H.subtype).subgroupOf Mc :=
    (K.equivMapOfInjective H.subtype H.subtype_injective).trans
      (subgroupOfEquivOfLe hKMc).symm
  obtain ⟨p,hp,ho,hr⟩ := diagramModel_odd_prime_rank_two
    ((H ⊓ M).subgroupOf H) K (T.subtype hH.1.1.2 : Subgroup H) hf hm
  let : Fact p.Prime := ⟨hp⟩
  have hrM : 2 ≤ primeRank p ((K.map H.subtype).subgroupOf Mc) := by
    rwa [primeRank_congr p eK] at hr
  have hrQ : 2 ≤ primeRank p
      (((K.map H.subtype).subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) := by
    rw [ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel ho
      (QuotientGroup.mk' (pCore 2 Mc))
      (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)]
    exact hrM
  apply source_outside_component_eq_of_twoCore_images
    hG T hempty hM hu hmany hcard e H hH K hK D hD hKD
  obtain ⟨F,hfield,hfinite,hchar,n,hn,hF,hmD⟩ := hmodel
  rcases hmD with ⟨⟨eD⟩⟩ | ⟨⟨eD⟩⟩
  · exact ChapterA.Section03.SourceEmbeddings.twoCore_images_eq_of_linear_three_containing_component
      (T.subtype hTMc) hKM hD.2 (comap_mono hKD) ho hrQ hn hF eD
  · have h4 : 4 ≤ Nat.card F := by
      rw [hF]
      exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ n)
    exact ChapterA.Section03.SourceEmbeddings.twoCore_images_eq_of_symplectic_four_containing_component
      (T.subtype hTMc) hKM hD.2 (comap_mono hKD) ho hrQ (by omega) eD

theorem source_diagram_component_placement_of_rank_two_containing_models
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hn : 1 < generationParameter H)
    (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T.subtype hH.1.1.2 : Subgroup H) = ⊤) {f : ℕ} (hf : 1 < f)
    (hm : DiagramModel ((H ⊓ M).subgroupOf H) K (T.subtype hH.1.1.2 : Subgroup H) f)
    (hmodels : ∀ D : Subgroup G, D ∈ Chapter1.cComponentsIn Mc →
      K.map H.subtype ≤ D → (D.subgroupOf Mc).Normal →
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (n : ℕ),
        1 < n ∧ Nat.card F = 2^n ∧
        (Nonempty ((D.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc)) ≃* PSL(3,F)) ∨
          Nonempty ((D.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc)) ≃*
            Theory.SpecificGroups.SymplecticFour.Sp F))) :
    K.map H.subtype ∈ Chapter1.cComponentsIn Mc ∧
      ((K.map H.subtype).subgroupOf Mc).Normal := by
  apply source_diagram_component_placement_of_twoCore_images
    hG T hempty hM hu hmany hcard e H hH hn K hK hqK hgen hf hm
  intro D hD hKD hnD
  have he := source_diagram_component_eq_of_rank_two_containing_model
    hG T hempty hM hu hmany hcard e H hH hn K hK hqK hgen hf hm
    D hD hKD (hmodels D hD hKD hnD)
  rw [he]

theorem source_linear_diagram_Mc_action_of_rank_two_containing_models
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hn : 1 < generationParameter H)
    (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T.subtype hH.1.1.2 : Subgroup H) = ⊤)
    {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = 2^f) (hf : 1 < f)
    (mark : sourceImage ((H ⊓ M).subgroupOf H) K ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
    (hmark : (componentOverlap ((H ⊓ M).subgroupOf H) K).map mark.toMonoidHom =
      Matrix.PSL3.LinearThree.borel F)
    (hmove : MovesDiagram ((H ⊓ M).subgroupOf H) K
      (T.subtype hH.1.1.2 : Subgroup H) mark
      (Matrix.PSL3.LinearThree.pointParabolic F) (Matrix.PSL3.LinearThree.lineParabolic F))
    (hmodels : ∀ D : Subgroup G, D ∈ Chapter1.cComponentsIn Mc →
      K.map H.subtype ≤ D → (D.subgroupOf Mc).Normal →
      ∃ (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2) (n : ℕ),
        1 < n ∧ Nat.card E = 2^n ∧
        (Nonempty ((D.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc)) ≃* PSL(3,E)) ∨
          Nonempty ((D.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc)) ≃*
            Theory.SpecificGroups.SymplecticFour.Sp E))) :
    ∃ ρ : Mc →* MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F),
      MulAut.innerSubgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) ≤ ρ.range ∧
      (∃ t : Mc, (t : G) ∈ (T : Subgroup G) ∧
        Matrix.PSL3.LinearThree.OuterExtensions.diagramAction F
          (n := f) (by omega) hF (ρ t) ≠ 1) ∧
      (T : Subgroup G) ⊓
        ((MulAut.innerSubgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)).comap ρ).map Mc.subtype ≤
        (T : Subgroup G) ⊓ normalizer
          ((markedParabolicResidual ((H ⊓ M).subgroupOf H) K mark
            (Matrix.PSL3.LinearThree.pointParabolic F)).map H.subtype : Set G) := by
  have hm : DiagramModel ((H ⊓ M).subgroupOf H) K
      (T.subtype hH.1.1.2 : Subgroup H) f :=
    Or.inl ⟨F,inferInstance,inferInstance,inferInstance,by omega,hF,mark,hmark,hmove⟩
  have hplace := source_diagram_component_placement_of_rank_two_containing_models
    hG T hempty hM hu hmany hcard e H hH hn K hK hqK hgen hf hm hmodels
  exact source_linear_diagram_Mc_action hG T hempty hM hu hmany hcard e H hH hn
    K hK hqK hgen hF hf mark hmark hmove hplace.2

end CFSG.Quasithin.Chapter14.Section02
