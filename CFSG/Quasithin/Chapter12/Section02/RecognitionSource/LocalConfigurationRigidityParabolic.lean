module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityCentralizers
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationSplitting
public import Theory.GroupTheory.RelativeComplementRefinement
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Constructing the complement in the literal source parabolic

Let K=C_{N_L(U)}(P). The normalizer and tensor geometry of12.2.25 gives
N_L(U)=UVK, disjointness of UV and K, and a K-invariant complement W
to U∩V in U. Then WK is disjoint from V and generates N_L(U) together
with V. Relative normality of V gives the actual subgroup complement.
The final application retains the original Sylow T and its containment
in this same parabolic, as required by the existing Gaschütz consumer.

The factorization and invariant-submodule existence are explicit source
inputs here, to be supplied by the two dimension branches. This file does
not assert self-normalization, the core identity, or the dimension bound.

Source: Aschbacher--Smith,12.2.25--26, printed pp.805--806.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
variable {G : Type*} [Group G]

/-- The literal fixed actor C_{N_L(U)}(P). -/
def parabolicFixedActor (L U P : Subgroup G) : Subgroup G :=
  L ⊓ normalizer (U : Set G) ⊓ centralizer (P : Set G)

/-- The subgroup factorization obtained from the normalizer and tensor action
in 12.2.25. No complement to V in the parabolic is included. -/
structure ParabolicFactorization (L V U P : Subgroup G) : Prop where
  generate : U ⊔ V ⊔ parabolicFixedActor L U P = L ⊓ normalizer (U : Set G)
  separate : Disjoint (U ⊔ V) (parabolicFixedActor L U P)
  invariant_complement : ∃ W : Subgroup G, W ≤ U ∧
    (U ⊓ V) ⊔ W = U ∧ Disjoint (U ⊓ V) W ∧
    parabolicFixedActor L U P ≤ normalizer (W : Set G)

variable [Finite G] {T : Sylow 2 G} {L V U P : Subgroup G}

omit [Finite G] in
theorem parabolicSplitting_of_factorization (D : ChosenModule T L V)
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hself : normalizer (L : Set G) = L)
    (F : ParabolicFactorization L V U P) : ParabolicSplitting T L V U := by
  obtain ⟨W, hWU, hUW, hdW, hKW⟩ := F.invariant_complement
  let K := parabolicFixedActor L U P
  let J := L ⊓ normalizer (U : Set G)
  let J' := (normalizer (U : Set G)).subgroupOf L
  have hTL : (T : Subgroup G) ≤ L := hself ▸ D.sylow_normalizes_component
  have hTJ : (T.subtype hTL : Subgroup L) ≤ J' := fun t ht => hTU ht
  have hVL : V ≤ L := D.le_component
  have hUJ : U ≤ J := (le_sup_left.trans le_sup_left).trans F.generate.le
  have hWL : W ≤ L := hWU.trans (hUJ.trans inf_le_left)
  have hKL : K ≤ L := inf_le_left.trans inf_le_left
  have hVW : V ⊔ W = U ⊔ V := by
    apply le_antisymm (sup_le le_sup_right (hWU.trans le_sup_left))
    refine sup_le ?_ le_sup_left
    rw [← hUW]
    exact sup_le (inf_le_right.trans le_sup_left) le_sup_right
  have hgen : V ⊔ W ⊔ K = J := by rw [hVW]; exact F.generate
  have hdVW : Disjoint V W := by
    apply disjoint_def.mpr
    intro x hxV hxW
    exact disjoint_def.mp hdW ⟨hWU hxW, hxV⟩ hxW
  have hdVK : Disjoint (V ⊔ W) K := by rw [hVW]; exact F.separate
  have hd : Disjoint V (W ⊔ K) :=
    disjoint_sup_of_normalizes_right_factor V W K hKW hdVW hdVK
  have hS : W ⊔ K ≤ L := sup_le hWL hKL
  have hVJ : V.subgroupOf L ≤ J' := fun v hv => hTU (D.le_sylow hv)
  have hSJ : (W ⊔ K).subgroupOf L ≤ J' := by
    intro s hs
    exact ((sup_le (le_sup_right.trans le_sup_left) le_sup_right : W ⊔ K ≤ (V ⊔ W) ⊔ K).trans hgen.le hs).2
  let : (V.subgroupOf L).Normal :=
    (normal_subgroupOf_iff_le_normalizer hVL).mpr D.normalizes
  have hg : V.subgroupOf L ⊔ (W ⊔ K).subgroupOf L = J' := by
    rw [← subgroupOf_sup hVL hS, ← sup_assoc, hgen]
    exact inf_subgroupOf_left (normalizer (U : Set G)) L
  have hds : Disjoint (V.subgroupOf L) ((W ⊔ K).subgroupOf L) := by
    apply disjoint_def.mpr
    intro x hxV hxS
    exact Subtype.ext (disjoint_def.mp hd hxV hxS)
  exact ⟨hTL, hTJ, ((W ⊔ K).subgroupOf L).subgroupOf J',
    (relative_isComplement hVJ hSJ hg hds).symm⟩

omit [Finite G] in
/-- The application to the unchanged cyclic source pair supplies T-normalization
of U internally, before the already proved Gaschütz promotion. -/
theorem parabolicSplitting_of_cyclic_factorization (D : ChosenModule T L V)
    {d : ℕ} {H : Subgroup G} (C : CyclicLocalAnalysis T L V d H P U)
    (hself : normalizer (L : Set G) = L)
    (F : ParabolicFactorization L V U P) : ParabolicSplitting T L V U :=
  parabolicSplitting_of_factorization D C.sylow_normalizes_core hself F

/-- Actual consumer for the final local rigidity boundary. The dimension branches
must still supply the displayed rigidity conclusions and factorization. -/
theorem splitLinearConfiguration_of_cyclic_factorization (D : ChosenModule T L V)
    {d : ℕ} {H : Subgroup G} (A : NaturalLocalAnalysis T L V d)
    (C : CyclicLocalAnalysis T L V d H P U)
    (hd : d = 3 ∨ d = 4) (hself : normalizer (L : Set G) = L)
    (hcore : L.pCoreIn 2 = V) (F : ParabolicFactorization L V U P) :
    SplitLinearConfiguration L V d :=
  splitLinearConfiguration_of_parabolic_split D hd C.block A.natural hself hcore
    (parabolicSplitting_of_cyclic_factorization D C hself F)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
