module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ResidualCentralizers.ComponentExtension.EmbeddingReduction.Placement
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ResidualCentralizers.ComponentExtension.EmbeddingReduction.Transport
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ResidualCentralizers.ComponentExtension.EmbeddingReduction.ModelSeparation
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ResidualCentralizers.ComponentExtension.EmbeddingReduction.MarkedContradiction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ResidualCentralizers.ComponentExtension.EmbeddingReduction.Cases

/-!
# Reduction of the containing component in the fixed-line centralizer

The complete universal A.3.12 and A.3.8 inputs construct a normal containing
C-component of C = C_G(Z₁), keeping the actual subgroup images in C/O₂(C).
The smaller image has intrinsic two-core quotient A₈, identified with PSL₄(2)
by the proved exceptional isomorphism. Equality of the two quotient images
forces equality before quotienting.

For the candidate proper extensions, the transport lemmas preserve the
embedded parabolic residual in L₅(2), the extension kernel in M₂₄, and the
local-component condition for an actual Sylow subgroup in the J₄ quotient.
They apply the completed first two stabilizers and the precise universal
J₄ conclusion as an explicit input. The resulting inner action contradicts
the marked S₈ action, using the original inclusions and intrinsic two-cores.

The full twenty-two-case sieve leaves exactly these three proper extensions.
In particular its equal-order PSL₃(4) branch is excluded by the different
Sylow two-center orders. The assembly below eliminates every proper case,
so L itself is a normal C-component of the fixed-line centralizer. Only the
full universal A.3.12/A.3.8 statements and the specified universal J₄
stabilizer remain external inputs. Source-level assembly must discharge
these inputs; the parent retains the residual equality using `ThreeResidual`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.32(3), printed pp.1132–1133; 1.2.4, p.505; A.3.12, pp.47–48.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ComponentExtension.EmbeddingReduction
open Chapter1 Chapter1.Section02 Chapter1.Terminal Chapter1.Terminal.LinearFourActions
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The containing-component step of 15.3.32(3), with the full earlier
classification statements and the universal J₄ stabilizer as explicit inputs.
Every local-family, quotient, parabolic and Sylow premise of the embedding
exclusions is discharged from the displayed section hypotheses. -/
theorem component_is_normal_fixedLine_component {κ : GroupClass.{u}}
    (hG : IsSimpleQTKE κ G)
    (hA312 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK κ X → pCore 2 X = ⊥ → ∀ (T : Sylow 2 X) (B : Subgroup X),
      B ∈ ChapterA.Section03.localCComponents T → A312Conclusion B)
    (hA38 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK κ X → pCore 2 X = ⊥ → ∀ K : Subgroup X, K.IsCComponent →
      K.Normal ∨ (normalizer (K : Set X)).index = 2 ∧ NonnormalCComponentModel K)
    (hJ4 : ∀ (Q : Type u) [Group Q] [Finite Q],
      ∀ (_eQ : Q ≃* Janko4.Model) (A : Subgroup Q) (T : Sylow 2 Q),
      ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 4 2 →
      A ∈ ChapterA.Section03.localCComponents T → TwoStabilizerActsInner A)
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.Hplus)
    (c : ComponentWitness d I) (hnormal : (c.L.subgroupOf I).Normal)
    (hjoin : I = c.L ⊔ d.S)
    (hfixed : d.ZS ⊓ centralizer (c.L : Set G) = d.ZS ⊓ d.V₁)
    (hcard : Nat.card (d.ZS ⊓ d.V₁ : Subgroup G) = 2)
    (h11 : ∀ J ∈ d.Hplus, Chapter1.IsSylowIn 2 d.S J)
    (hcentralizer : I ⊓ centralizer (d.componentModule I c.L : Set G) = I.pCoreIn 2)
    (e : d.Star I ≃* Equiv.Perm (Fin 8))
    (hmark : (d.starImage I c.L).map e.toMonoidHom = alternatingGroup (Fin 8)) :
    let C := centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G)
    (c.L.subgroupOf C).IsCComponent ∧ (c.L.subgroupOf C).Normal := by
  let C := centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G)
  change (c.L.subgroupOf C).IsCComponent ∧ (c.L.subgroupOf C).Normal
  have hLC : c.L ≤ C := (component_le c).trans
    (overgroup_le_fixedLine_centralizer d c hjoin hfixed)
  obtain ⟨P, hP⟩ := h11 I hI
  obtain ⟨T, hT, K, hK, hKn, hBK, _, hemb⟩ :=
    exists_normal_containing_component hG hA312 hA38 d hI c hnormal hjoin hfixed hcard h11
  have hSC : d.S ≤ C := hT ▸ map_subtype_le (T : Subgroup C)
  have hTeq : (T : Subgroup C) = d.S.subgroupOf C := by
    apply map_injective C.subtype_injective
    rw [map_subgroupOf_eq_of_le hSC]
    exact hT
  have hB : c.L.subgroupOf C ∈ ChapterA.Section03.localCComponents T := by
    rw [hTeq]
    exact ((mem_LIn_iff_subgroupOf hSC hLC).mp
      (component_mem_fixedLine_local_family d hI c hnormal hjoin hfixed h11)).1
  have hSL : d.S ≤ normalizer (c.L : Set G) :=
    (show d.S ≤ I from hjoin ▸ le_sup_right).trans
      ((normal_subgroupOf_iff_le_normalizer (component_le c)).mp hnormal)
  have hTB : (T : Subgroup C) ≤ normalizer (c.L.subgroupOf C : Set C) := by
    rw [hTeq, ← subgroupOf_normalizer_eq hLC]
    exact comap_mono hSL
  let eB := imageCoreEquivEight d c hLC P hP hcentralizer e hmark
  have hsmall : ClassicalGroup.IsPSL
      (twoQuotientImage c.L C ⧸ pCore 2 (twoQuotientImage c.L C)) 4 2 :=
    ⟨ZMod 2, inferInstance, inferInstance, by simp,
      ⟨eB.trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two⟩⟩
  have exclude := contradiction_of_containing_image_inner d c hLC hnormal hjoin
    P hP T hT hcentralizer e hmark K hBK hKn
  rcases Cases.alternatives_of_alt8_section (map_mono hBK) eB hemb with
    heq | ⟨hfive, hparabolic⟩ | ⟨hmathieu, hextension⟩ | hjanko
  · have heq := eq_of_local_core_image_eq T hB hK hBK heq
    rw [heq]
    exact ⟨hK, hKn⟩
  · exact (exclude (inner_of_five hBK hK hsmall hfive hparabolic)).elim
  · exact (exclude (inner_of_fourteen hBK hK hmathieu hextension)).elim
  · exact (exclude (inner_of_seventeen hJ4 T hB hTB hBK hK
      (isPSL_subgroupOf hLC (componentCore_isPSL d c P hP hcentralizer e hmark))
      hjanko)).elim

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ComponentExtension.EmbeddingReduction

end
