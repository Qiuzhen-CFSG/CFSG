module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OuterAction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Basic
public import Theory.GroupTheory.GeneralizedFitting.SimpleTwoQuotient
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.SpecificGroups.PSL3Two.Automorphisms

/-!
# Source quotient actions in the linear parabolic reduction

The literal image K* is identified with K/O₂(K) through its component
kernel. Relative normality and H = KT make H*/K* a two-group; the trivial
two-core of H* then kills the centralizer of the simple perfect K*.
The intrinsic invariant-node theorem therefore applies faithfully to the
original source component, without an assumed faithful action.

A single invariant flag gives inner action or the middle node in degree
four. The latter constructs a compatible S₈ equivalence on original K
representatives and retains the actual flag. In degree three, inner action
contradicts the full automorphism-group conclusion of 13.8.21(3).
Two distinct flags individually normalized by T* force T* ≤ K*, using
the actual image of a Sylow subgroup of H. The whole H* marking then
extends the original component marking on every representative.

Source: Aschbacher–Smith 13.8.25, printed pp.959–960 (PDF pp.976–977),
combined manuscript of 1 March 2004. These deductions still require source
identification of the marked flags; they do not assume or claim that
identification, the two cases of 13.8.8, or the complete reduction.
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics

variable {G : Type*} [Group G] [Finite G]

/-- The given intrinsic component model, transported through its actual kernel. -/
noncomputable def starLinearEquiv (H K : Subgroup G) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) {n : ℕ}
    (e : (K ⧸ pCore 2 K) ≃* PSL n) : Source.starImage H K ≃* PSL n :=
  (Components.componentStarEquiv H K hKH hK).symm.trans e

theorem starLinearEquiv_mk (H K : Subgroup G) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) {n : ℕ}
    (e : (K ⧸ pCore 2 K) ≃* PSL n) (k : K) :
    starLinearEquiv H K hKH hK e
      (Components.componentStarEquiv H K hKH hK (QuotientGroup.mk' _ k)) =
      e (QuotientGroup.mk' _ k) := by
  simp only [starLinearEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

/-- The earlier H = KT conclusion and the trivial two-core make the actual
simple component image self-centralizing. -/
theorem starComponent_centralizer_eq_bot (H K T : Subgroup G)
    (hKH : K ≤ H) (hTH : T ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hKn : (K.subgroupOf H).Normal) (hT : IsPGroup 2 T) (hKT : K ⊔ T = H)
    (hsimple : IsSimpleGroup (K ⧸ pCore 2 K)) :
    centralizer (Source.starImage H K : Set (Source.Hstar H)) = ⊥ := by
  let := hKn
  let : (Source.starImage H K).Normal :=
    Subgroup.Normal.map hKn _ (QuotientGroup.mk'_surjective _)
  let := hsimple
  let : IsSimpleGroup (Source.starImage H K) :=
    (Components.componentStarEquiv H K hKH hK).symm.isSimpleGroup
  let : Group.IsPerfect (Source.starImage H K) :=
    (Components.starImage_isCComponent H K hK).perfect
  have hs : Source.starImage H K ⊔ Source.starImage H T = ⊤ := by
    rw [Source.starImage, Source.starImage, ← Subgroup.map_sup, ← subgroupOf_sup hKH hTH,
      hKT, subgroupOf_self, map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have ht : IsPGroup 2 (Source.starImage H T) := hT.comap_subtype.map _
  exact Theory.GroupTheory.centralizer_eq_bot_of_simple_two_quotient _
    (Group.IsPerfect.not_isMulCommutative _)
    (isPGroup_quotient_of_sup_eq_top _ _ ht hs) (pCore_quotient_pCore_eq_bot 2)

/-- The invariant-node restriction in the literal source quotient. Relative
normality, the actual component kernel, and faithfulness are all discharged. -/
theorem source_deletedFlag_alternative (H K T : Subgroup G)
    (hKH : K ≤ H) (hTH : T ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hKn : (K.subgroupOf H).Normal) (hT : IsPGroup 2 T) (hKT : K ⊔ T = H)
    {m : ℕ} (hm₀ : 2 ≤ m) (hm₁ : m ≤ 4)
    (e : (K ⧸ pCore 2 K) ≃* PSL (m + 1))
    (b : Basis m) (i : Fin m) (P : Subgroup (Source.Hstar H))
    (hP : P = ambientFlagStabilizer (starLinearEquiv H K hKH hK e) (deletedFlag hm₀ b i))
    (hn : Source.starImage H T ≤ normalizer (P : Set (Source.Hstar H))) :
    Source.starImage H T ≤ Source.starImage H K ∨ (m = 3 ∧ i.val + 1 = 2) := by
  let : (Source.starImage H K).Normal := by
    let := hKn
    exact Subgroup.Normal.map hKn _ (QuotientGroup.mk'_surjective _)
  let : IsSimpleGroup (PSL (m + 1)) :=
    Atlas.psl_simple_high_rank (F := ZMod 2) (m + 1) (by omega)
  exact OuterAction.normalizing_deletedFlag_alternative hm₀ hm₁
    (starLinearEquiv H K hKH hK e) b i P (Source.starImage H T) hP
    (starComponent_centralizer_eq_bot H K T hKH hTH hK hKn hT hKT e.isSimpleGroup) hn

/-- In dimension three the invariant flag forces H* = K*, of order 168,
contrary to the complete 13.8.21(3) conclusion H* ≃ Aut(PSL₃(2)), of order 336. -/
theorem exclude_three_source_deletedFlag (H K T : Subgroup G)
    (hKH : K ≤ H) (hTH : T ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hKn : (K.subgroupOf H).Normal) (hT : IsPGroup 2 T) (hKT : K ⊔ T = H)
    (e : (K ⧸ pCore 2 K) ≃* PSL 3)
    (hAut : Nonempty (Source.Hstar H ≃* MulAut Matrix.PSL3Two.PSL))
    (b : Basis 2) (i : Fin 2) (P : Subgroup (Source.Hstar H))
    (hP : P = ambientFlagStabilizer (starLinearEquiv H K hKH hK e)
      (deletedFlag (by decide : 2 ≤ 2) b i))
    (hn : Source.starImage H T ≤ normalizer (P : Set (Source.Hstar H))) : False := by
  have hs : Source.starImage H T ≤ Source.starImage H K := by
    rcases source_deletedFlag_alternative H K T hKH hTH hK hKn hT hKT
      (by decide : 2 ≤ 2) (by decide : 2 ≤ 4) e b i P hP hn with h | h
    · exact h
    · omega
  have ht : Source.starImage H K = ⊤ := by
    have hh : Source.starImage H K ⊔ Source.starImage H T = ⊤ := by
      rw [Source.starImage, Source.starImage, ← Subgroup.map_sup, ← subgroupOf_sup hKH hTH,
        hKT, subgroupOf_self, map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    rwa [sup_eq_left.mpr hs] at hh
  let a := Subgroup.topEquiv.symm.trans
    ((MulEquiv.subgroupCongr ht.symm).trans (starLinearEquiv H K hKH hK e))
  have hc : Nat.card (Source.Hstar H) = 168 :=
    (Nat.card_congr a.toEquiv).trans Matrix.PSL3Two.card_PSL
  obtain ⟨u⟩ := hAut
  have hc' : Nat.card (Source.Hstar H) = 336 :=
    (Nat.card_congr u.toEquiv).trans Matrix.PSL3Two.Automorphisms.card_aut
  omega

omit [Finite G] in
/-- When the supplement lies in the starred component, that component is H*. -/
theorem starComponent_eq_top (H K T : Subgroup G) (hKH : K ≤ H) (hTH : T ≤ H)
    (hKT : K ⊔ T = H) (hs : Source.starImage H T ≤ Source.starImage H K) :
    Source.starImage H K = ⊤ := by
  have hh : Source.starImage H K ⊔ Source.starImage H T = ⊤ := by
    rw [Source.starImage, Source.starImage, ← Subgroup.map_sup, ← subgroupOf_sup hKH hTH,
      hKT, subgroupOf_self, map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  rwa [sup_eq_left.mpr hs] at hh

/-- Extend the original component marking to H* after proving T* ≤ K*. -/
noncomputable def wholeStarLinearEquiv (H K T : Subgroup G)
    (hKH : K ≤ H) (hTH : T ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hKT : K ⊔ T = H) (hs : Source.starImage H T ≤ Source.starImage H K)
    {n : ℕ} (e : (K ⧸ pCore 2 K) ≃* PSL n) : Source.Hstar H ≃* PSL n :=
  Subgroup.topEquiv.symm.trans
    ((MulEquiv.subgroupCongr (starComponent_eq_top H K T hKH hTH hKT hs).symm).trans
      (starLinearEquiv H K hKH hK e))

theorem wholeStarLinearEquiv_mk (H K T : Subgroup G)
    (hKH : K ≤ H) (hTH : T ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hKT : K ⊔ T = H) (hs : Source.starImage H T ≤ Source.starImage H K)
    {n : ℕ} (e : (K ⧸ pCore 2 K) ≃* PSL n) (k : K) :
    wholeStarLinearEquiv H K T hKH hTH hK hKT hs e
      (QuotientGroup.mk' (pCore 2 H) ⟨k, hKH k.property⟩) =
      e (QuotientGroup.mk' (pCore 2 K) k) := by
  rw [← Components.componentStarEquiv_mk H K hKH hK k]
  exact starLinearEquiv_mk H K hKH hK e k

/-- The outer degree-four alternative has the actual middle node and an S₈
equivalence compatible with the original K/O₂(K) marking on representatives. -/
theorem source_middleNode_marking (H K T : Subgroup G)
    (hKH : K ≤ H) (hTH : T ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hKn : (K.subgroupOf H).Normal) (hT : IsPGroup 2 T) (hKT : K ⊔ T = H)
    (e : (K ⧸ pCore 2 K) ≃* PSL 4)
    (b : Basis 3) (i : Fin 3) (P : Subgroup (Source.Hstar H))
    (hP : P = ambientFlagStabilizer (starLinearEquiv H K hKH hK e)
      (deletedFlag (by decide : 2 ≤ 3) b i))
    (hn : Source.starImage H T ≤ normalizer (P : Set (Source.Hstar H)))
    (hs : ¬ Source.starImage H T ≤ Source.starImage H K) :
    i.val + 1 = 2 ∧ Source.starImage H T ⊓ Source.starImage H K < Source.starImage H T ∧
      ∃ E : Source.Hstar H ≃* Equiv.Perm (Fin 8),
        (∀ k : K, E (QuotientGroup.mk' (pCore 2 H) ⟨k, hKH k.property⟩) =
          (Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8
            (e (QuotientGroup.mk' (pCore 2 K) k)) : Equiv.Perm (Fin 8))) ∧
        (Source.starImage H K).map E.toMonoidHom = alternatingGroup (Fin 8) ∧
        P.map E.toMonoidHom =
          (flagStabilizer (starLinearEquiv H K hKH hK e) (deletedFlag (by decide) b i)).map
            ((alternatingGroup (Fin 8)).subtype.comp
              ((starLinearEquiv H K hKH hK e).trans
                Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8).toMonoidHom) := by
  have hi := ((source_deletedFlag_alternative H K T hKH hTH hK hKn hT hKT
    (by decide) (by decide) e b i P hP hn).resolve_left hs).2
  let : (Source.starImage H K).Normal := by
    let := hKn
    exact Subgroup.Normal.map hKn _ (QuotientGroup.mk'_surjective _)
  let : IsSimpleGroup (PSL 4) := Atlas.psl_simple_high_rank (F := ZMod 2) 4 (by decide)
  obtain ⟨E, hE, hKimage, hPimage⟩ := OuterAction.exists_marked_symmetric_extension
    (starLinearEquiv H K hKH hK e) P (Source.starImage H T)
    (deletedFlag (by decide) b i) hP
    (starComponent_centralizer_eq_bot H K T hKH hTH hK hKn hT hKT e.isSimpleGroup) hs
  refine ⟨hi, inf_lt_left.mpr hs, E, ?_, hKimage, hPimage⟩
  intro k
  rw [← Components.componentStarEquiv_mk H K hKH hK k, hE,
    starLinearEquiv_mk H K hKH hK e k]

/-- Two distinct source flags, each individually normalized by T*, force
T* ≤ K*. The Sylow image is formed from the actual Sylow subgroup of H. -/
theorem source_two_deletedFlags_le_component (H K T : Subgroup G)
    (hKH : K ≤ H) (hTH : T ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hKn : (K.subgroupOf H).Normal) (hT : IsPGroup 2 T) (hKT : K ⊔ T = H)
    (S : Sylow 2 H) (hS : (S : Subgroup H) = T.subgroupOf H)
    {m : ℕ} (hm₀ : 2 ≤ m) (hm₁ : m ≤ 4)
    (e : (K ⧸ pCore 2 K) ≃* PSL (m + 1))
    (b c : Basis m) (i j : Fin m) (P Q : Subgroup (Source.Hstar H))
    (hP : P = ambientFlagStabilizer (starLinearEquiv H K hKH hK e) (deletedFlag hm₀ b i))
    (hQ : Q = ambientFlagStabilizer (starLinearEquiv H K hKH hK e) (deletedFlag hm₀ c j))
    (hSP : Source.starImage H T ⊓ Source.starImage H K ≤ P)
    (hSQ : Source.starImage H T ⊓ Source.starImage H K ≤ Q) (hne : P ≠ Q)
    (hnP : Source.starImage H T ≤ normalizer (P : Set (Source.Hstar H)))
    (hnQ : Source.starImage H T ≤ normalizer (Q : Set (Source.Hstar H))) :
    Source.starImage H T ≤ Source.starImage H K := by
  let : (Source.starImage H K).Normal := by
    let := hKn
    exact Subgroup.Normal.map hKn _ (QuotientGroup.mk'_surjective _)
  let : IsSimpleGroup (PSL (m + 1)) :=
    Atlas.psl_simple_high_rank (F := ZMod 2) (m + 1) (by omega)
  let S' : Sylow 2 (Source.Hstar H) := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  have hS' : (S' : Subgroup (Source.Hstar H)) = Source.starImage H T := by
    change (S : Subgroup H).map (QuotientGroup.mk' (pCore 2 H)) = _
    rw [hS]
    rfl
  have hc := starComponent_centralizer_eq_bot H K T hKH hTH hK hKn hT hKT e.isSimpleGroup
  have h := OuterAction.le_component_of_normalizing_two_deletedFlags hm₀ hm₁
    (starLinearEquiv H K hKH hK e) b c i j P Q S' hP hQ hc
    (hS'.symm ▸ hSP) (hS'.symm ▸ hSQ) hne (hS'.symm ▸ hnP) (hS'.symm ▸ hnQ)
  rwa [hS'] at h

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics

end
