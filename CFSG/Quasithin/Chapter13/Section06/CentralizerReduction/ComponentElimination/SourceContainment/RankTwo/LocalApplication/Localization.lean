module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.LocalApplication.IntrinsicPlus
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Quotients
public import Theory.GroupTheory.CComponent.NonquasisimpleAction
public import Theory.GroupTheory.CComponent.QuasisimpleImageRigidity

/-!
# Localizing the C-component to KLᵥ

The genuine 1.2.4 puts K in a C-component D of the plus actor. Its
three-rank is at least two, so A.3.6 makes D/O₂(D) quasisimple.
The nontrivial images of K and D in the plus quotient are comparable
C-components, hence equal. Since O₂(D) lies in the Sylow two-subgroup,
13.6.14 makes it normalize K. Supplement rigidity now gives K = D,
and restriction gives a C-component in the smaller actor KLᵥ.

A.3.6 and A.3.12 remain universal earlier-source inputs. The Sylow
condition before 13.6.4, the normalization in 13.6.14 and the earlier
R₂ consequence O₂(G+)=1 are explicit local source inputs. No local
C-component, intrinsic quasisimplicity, or containment is assumed.
Source: Aschbacher–Smith, combined manuscript, pp.926–931; 1.2.4;
A.3.6 and A.3.12.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.LocalApplication
open ComponentSelection Chapter1.Section02

universe u
/-- Localize the source C-component to the literal A.3.18 actor KLᵥ. -/
theorem source_local_cComponent {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
    (hG : IsSimpleQTKE κ G)
    (hA36 : ∀ (D : Type u) [Group D] [Finite D], IsSQTK κ D → pCore 2 D = ⊥ →
      ∀ B : Subgroup D, B.IsCComponent → A36Conclusion B)
    (hA312 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK κ X → pCore 2 X = ⊥ → ∀ (T : Sylow 2 X) (B : Subgroup X),
      B ∈ ChapterA.Section03.localCComponents T →
      ∃! K : Subgroup X, K.IsCComponent ∧ B ≤ K)
    (K L T : Subgroup G) (z v : G) (hv : orderOf v = 2) (hK : K ∈ Yz L T z v)
    (hr : primeRank 3 K = 2)
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥) :
    (localComponent K L v).IsCComponent := by
  let A := plusActor K L T v
  let B := K.subgroupOf A
  have hKA : K ≤ A := K_le_plusActor K L T v
  have hTA : Tv T v ≤ A := le_sup_right
  have hAG : A ≤ Gv v := plusActor_le_Gv K L T v hK.1.1
  have hsA := hSyl.restrict hTA hAG
  obtain ⟨S, hS⟩ := hsA
  have hSeq : (S : Subgroup A) = (Tv T v).subgroupOf A := by
    apply map_injective A.subtype_injective
    rw [hS, map_subgroupOf_eq_of_le hTA]
  have hB : B ∈ Chapter1.L A (S : Subgroup A) := by
    rw [hSeq]
    exact (Chapter1.mem_LIn_iff_subgroupOf hTA hKA).mp ⟨hKA, hK.1.2⟩
  have hsq : IsSQTK κ A := (IsSQTK.equiv (subgroupOfEquivOfLe hAG)).mp
    ((hG.involution_centralizer_sqtk hv).subgroup (A.subgroupOf (Gv v)))
  have hsqQ : IsSQTK κ (A ⧸ pCore 2 A) := by
    refine ⟨?_, hsq.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 A) pCore_isPGroup).trans
      (hsq.stronglyQuasithin p hp ho)
  obtain ⟨D, ⟨hD, hBD⟩, _⟩ := lemma_1_2_4_containment_of_A_3_12 hA312 hsqQ S hB
  have hrB : 2 ≤ primeRank 3 B := by
    rw [primeRank_equiv 3 (subgroupOfEquivOfLe hKA), hr]
  have hrD : 2 ≤ primeRank 3 D := hrB.trans
    (Theory.GroupTheory.primeRank_le_of_injective 3 (inclusion hBD) (inclusion_injective hBD))
  let := (cComponent_twoCore_quasisimple_of_three_rank hA36 hsq D hD hrD).1
  let f := plusMk K L T z v hL hz
  have hP : (B.map f).IsCComponent := by
    have hc : IsComponent (Gplus K L T z v hL hz) (plusImage K L T z v hL hz K) :=
      ⟨plusImage_K_subnormal K L T z v hL hz hK,
        plusImage_K_quasisimple K L T z v hL hz hK hR⟩
    exact hc.isCComponent
  have hDne : D.map f ≠ ⊥ := fun he => hP.ne_bot
    (bot_unique ((map_mono hBD).trans he.le))
  have hDf : (D.map f).IsCComponent :=
    (NonquasisimpleAction.ccomponent_image_or_bot hD f (QuotientGroup.mk'_surjective _)).resolve_left hDne
  have himage : B.map f = D.map f := hP.eq_of_le hDf (map_mono hBD)
  have hSnormal : (S : Subgroup A) ≤ normalizer (B : Set A) := by
    rw [hSeq, ← subgroupOf_normalizer_eq hKA]
    exact comap_mono hn
  have hcore : (pCore 2 D).map D.subtype ≤ (S : Subgroup A) :=
    (pCoreIn_le_of_subnormal 2 hD.subnormal).trans (pCore_isPGroup.le_sylow_of_normal S)
  have hnorm : pCore 2 D ≤ normalizer (B.subgroupOf D : Set D) := by
    rw [← subgroupOf_normalizer_eq hBD]
    exact (map_le_iff_le_comap.mp hcore).trans (comap_mono hSnormal)
  have hBD_eq : B = D := IsCComponent.eq_of_image_eq_of_twoCore_normalizes f hD hBD himage hDne hnorm
  have hBA : B.IsCComponent := hBD_eq ▸ hD
  exact hBA.subgroupOf_of_le le_sup_left (sup_le hKA (le_sup_right.trans le_sup_left))

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.LocalApplication
