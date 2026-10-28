module

public import CFSG.Quasithin.Chapter3.Section02.SourceSelection
public import CFSG.Quasithin.Chapter3.Section02.ThompsonCommutator
public import CFSG.Quasithin.Chapter3.Section01.Source318Movement
public import CFSG.Quasithin.Chapter3.Section01.StandingGuard
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.OrbitSource
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.SourceKnownSimple

/-!
# Thompson generation for a normalized faithful local component

Choose an actual Fundamental Setup for the component. Its qrc configuration
and the noncentral omega-center implication of 3.1.8 force Thompson movement
on the chosen module, hence full commutator generation. Centralizer containment
in the component normalizer makes every outside minimal local group noncentral.
The choice of the auxiliary module imposes no new premise on the component.

Source: Aschbacher–Smith, Theorem 3.1.8(3), Lemmas 3.2.2(6), 3.2.3,
and the application in 13.3.14(f), printed pp.576,579–580,892.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The noncentral branch of 3.1.8 gives the literal component commutator,
with the source constituent chosen internally. -/
theorem source_component_thompson_generation
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (B : Subgroup G) (hB : B ∈ Chapter1.LStar G (T : Subgroup G))
    (hf : ChapterA.Section04.IsFaithfulSignalizerType B)
    (hq : IsQuasisimple (B ⧸ pCore 2 B))
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hout : HasMaximalOutside T (normalizer (B : Set G)))
    (hC : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤
      normalizer (B : Set G)) :
    ⁅B,elementaryAbelianMaxJ (T : Subgroup G)⁆ = B := by
  obtain ⟨D⟩ := source_exists_fundamentalSetup hG T B hB hf hq
  have h127 := Chapter1.Section02.nonsolvable_uniqueness_knownSimple hG T hB
  have horb : localOrbit T B = B :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer B _ B le_rfl hTB)
      (le_componentOrbit B _)
  have hmax : D.maximalLocal = normalizer (B : Set G) := by
    change normalizer (localOrbit T B : Set G) = _
    rw [horb]
  obtain ⟨Y,hY⟩ := exists_HStar_of_hasMaximalOutside hout
  have hy : Y ∈ HStar (T : Subgroup G) D.maximalLocal := hmax.symm ▸ hY
  have hz : ¬ omegaOneCenterAmbient (T : Subgroup G) ≤ (center Y).map Y.subtype := by
    intro hz
    apply hY.1.2
    apply le_trans ?_ hC
    apply le_centralizer_iff.mp
    rintro z hz' y hy'
    obtain ⟨c,hc,rfl⟩ := hz hz'
    exact congrArg Y.subtype (mem_center_iff.mp hc ⟨y,hy'⟩)
  have hu := D.lemma_3_2_3_uniqueness h127
  have hj := (D.qrcHypotheses h127 hy).thompson_moves_of_noncentral_omega
    hG hu.1 hu.2.2 D.module_ne_bot hz
  have he := D.actor_eq_commutator_of_thompson_not_centralizes h127 hj
  rw [horb] at he
  exact he.symm

end CFSG.Quasithin.Chapter3.Section02
