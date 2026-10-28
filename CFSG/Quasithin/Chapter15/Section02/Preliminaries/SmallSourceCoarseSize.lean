module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SmallMixedRecognition
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.MarkedFiveFinalQuotient

/-!
# The mixed Sylow estimate sufficient for the original small-source quotients

The two original faithful chief factors force a single-S₅ H-star branch
to have Sylow order at least 2048. Thus the mixed A₅/S₃ source estimate
at most 1024 already excludes it. This applies to both the cubic and
Omega rows; the independent marked-five theorem completes all H-star
quotients. The sharper mixed bound at most 256, needed by Chapter 10,
is not required for this Chapter 15 application.

The source estimate and original prior remain explicit in this consumer.
The mixed numerical source owner constructs that estimate, and the
original source assembly retains discharge of the prior.
Source: Aschbacher--Smith 15.2.6--8, printed pp.1109--1110.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource ChapterF.Source
variable {G : Type*} [Group G] [Finite G]

variable (hsize : ∀ (K A S : Subgroup G), HypothesisF11 ![K,A] S →
  IsQuasithin (generated ![K,A] S) → Chapter1.IsSylowIn 2 S (generated ![K,A] S) →
  Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) →
  Nonempty ((A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3)) →
  borel A S ≤ normalizer (S : Set G) → Nat.card S ≤ 1024)
include hsize

/-- The actual source lower bound needs only the mixed upper bound 1024. -/
theorem SmallResidualWitness.not_symmetricFive_of_cubic_of_coarse_mixed_size
    {T : Sylow 2 G} {M Mc V Y₁ H : Subgroup G} {h : ChosenSmallSource T M Mc V}
    (hw : SmallResidualWitness h Y₁) (hprior : SmallSourcePrior T M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hfirst : Nonempty (((Y₁ ⊔ (M ⊓ Mc).pCoreIn 2 : Subgroup G) ⧸
      pCore 2 (Y₁ ⊔ (M ⊓ Mc).pCoreIn 2 : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    ¬ Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5)) := by
  intro he
  obtain ⟨hf,hqt,hsyl,hk,hb,_,_⟩ := hw.symmetricFive_mixed_inputs hH he
  have hu := hsize _ _ _ hf hqt hsyl hk hfirst hb
  have hl := h.symmetricFive_sylow_card hprior hH he
  omega

/-- All original small-source H-star quotients follow from the mixed
bound sufficient for Chapter 15, with the marked-five branch discharged. -/
theorem ChosenSmallSource.HStar_wreath_of_coarse_mixed_size
    {T : Sylow 2 G} {M Mc V : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hprior : SmallSourcePrior T M V) :
    ∀ H ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((H ⧸ pCore 2 H) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))) := by
  let := h.prepared.elementary
  intro H hH
  rcases h.small with ⟨l,p,m,hpm,hd⟩ | ho
  · have hm : m = 2 := h.marking_dimension l p m hd
    subst m
    rcases (primeDimensionOptions_iff p 2).mp hpm with ⟨rfl,_⟩ | ⟨rfl,_⟩
    · have hw := (h.smallResidualWitness_of_marked_cubic ⟨l,hd⟩).1
      have hq := (h.marked_cubic_residual_selection ⟨l,hd⟩).2.2.1
      exact (h.HStar_quotient_cubic_reduced hprior ⟨l,hd⟩ hH).resolve_right
        (hw.not_symmetricFive_of_cubic_of_coarse_mixed_size hsize hprior hH hq)
    · exact h.HStar_wreath_of_marked_five ⟨l,hd⟩ hH
  · obtain ⟨Y₁,hle,hp,hne,hn,hm,hcentral,hquot⟩ := h.omega_rank_one_selection ho
    have hw := (h.smallResidualWitness_of_moved_selection (h.maximal_overgroups_of_omega ho)
      hle hp hne hn hm (Or.inl hquot) hcentral).1
    exact (h.HStar_quotient_omega_reduced hprior ho hH).resolve_right
      (hw.not_symmetricFive_of_cubic_of_coarse_mixed_size hsize hprior hH hquot)

end CFSG.Quasithin.Chapter15.Section02
