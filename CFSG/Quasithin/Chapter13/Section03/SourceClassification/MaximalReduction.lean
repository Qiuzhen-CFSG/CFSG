module

public import CFSG.Quasithin.Chapter13.Section03.SourceComponentRigidity
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Fitting.SupercriticalSource.StarPlacement
public import CFSG.Quasithin.Chapter1.Section02.Adequate.OrbitFaithful
public import CFSG.Quasithin.Chapter14.Section03.Prelim.FaithfulSource.Hypothesis1311

/-!
# From the maximal source catalogue to every faithful local component

Choose a maximal local overgroup I of the original K. Faithfulness ascends
along that inclusion, so 13.1.7 and the earlier maximal-component catalogue
apply to I. The five-model rigidity theorem then proves K = I. Thus the
original K satisfies 12.2.3, without changing its quotient or any chosen
module. The structural 12.2.2 implication supplies its Sylow normalization
and the actual homogeneous choices.

The three earlier inputs are explicit: 13.1.7, the five-model refinement
13.1.2(3), and structural 12.2.2. In particular the seven cases of 12.2.2
alone do not prove the five-model refinement: the exclusions from 12.3.1
and 12.9.1 must also be discharged by the source assembly. The separate
12.7.1 refinement concerns the triple-cover module, not this quotient list.

Source: Aschbacher--Smith, 13.1.2(1,3,5), p.866, and the opening of
13.3.2, pp.884--885 (combined manuscript, 1 March 2004).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.SourceClassification
open Chapter12.Section02 Chapter13.Section01
open Chapter1.Section02.Adequate
open Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

/-- The original faithful member is maximal and has the same literal
five-model quotient as its maximal overgroup. -/
theorem faithful_hypothesis1223_of_maximal_models
    (h : Hypothesis1311 T)
    (quasisimple : ∀ I : Subgroup G, FaithfulMaximalLocal T I →
      IsQuasisimple (I ⧸ pCore 2 I))
    (models : ∀ I : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T I →
      MidSizeModel (Chapter1.XiQuotient I))
    {K : Subgroup G} (hK : K ∈ MainForward.faithfulLocalComponents T) :
    Hypothesis1223 KnownSimple.IsKnownSimple T K ∧
      MidSizeModel (Chapter1.XiQuotient K) := by
  obtain ⟨I, hI, hKI⟩ := Chapter1.exists_mem_LStar_ge
    ((mem_faithfulLocalComponents_iff T K).mp hK).1
  have hf := faithful_local_overgroup T (h.simpleQTKE.evenCharacteristic T)
    hK hI.1 hKI
  have hmax : FaithfulMaximalLocal T I :=
    ⟨hI, ((mem_faithfulLocalComponents_iff T I).mp hf).2⟩
  have hi := h.hypothesis1223 hmax (quasisimple I hmax)
  have hm := models I hi
  have he := local_eq_of_midSize hI.1
    ((mem_faithfulLocalComponents_iff T K).mp hK).1 hKI hm
  subst K
  exact ⟨hi, hm⟩

/-- The literal catalogue and normality input consumed by the Chapter 13
and Chapter 14 centralizer arguments, reduced to earlier maximal sources. -/
theorem source1332OneTwo_of_maximal_models
    (h : Hypothesis1311 T)
    (quasisimple : ∀ I : Subgroup G, FaithfulMaximalLocal T I →
      IsQuasisimple (I ⧸ pCore 2 I))
    (models : ∀ I : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T I →
      MidSizeModel (Chapter1.XiQuotient I))
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) :
    Source1332OneTwo T := by
  intro K hK
  obtain ⟨hk, hm⟩ := faithful_hypothesis1223_of_maximal_models h quasisimple models hK
  exact ⟨(structural G T K hk).1, hm⟩

/-- Existence and invariance of actual Irr⁺ members for every original
faithful component. Each choice keeps its original reduced ambient subgroup. -/
theorem faithful_chosen_setup_of_maximal_models
    (h : Hypothesis1311 T)
    (quasisimple : ∀ I : Subgroup G, FaithfulMaximalLocal T I →
      IsQuasisimple (I ⧸ pCore 2 I))
    (models : ∀ I : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T I →
      MidSizeModel (Chapter1.XiQuotient I))
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    {K : Subgroup G} (hK : K ∈ MainForward.faithfulLocalComponents T) :
    FaithfulMaximalLocal T K ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      (T : Subgroup G) ≤ normalizer (K : Set G) ∧
      Nonempty {V : Subgroup G // Nonempty (ChosenModule T K V)} ∧
      ∀ (V : Subgroup G), ChosenModule T K V →
        (T : Subgroup G) ≤ normalizer (V : Set G) ∧
        IsPReduced 2 (V.subgroupOf (K ⊔ (T : Subgroup G))) ∧
        (∀ g ∈ normalizer (K : Set G),
          V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
            V.map (MulAut.conj g).toMonoidHom = V) ∧
        (normalizer (K : Set G) ≤ normalizer (V : Set G) ∨
          V ⊓ centralizer (K : Set G) = ⊥) := by
  obtain ⟨hk, _⟩ := faithful_hypothesis1223_of_maximal_models h quasisimple models hK
  exact ⟨hk.maximal_faithful, hk.quasisimple, structural G T K hk⟩

end CFSG.Quasithin.Chapter13.Section03.SourceClassification
