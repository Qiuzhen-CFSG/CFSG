module

public import CFSG.Quasithin.ChapterF.Section06.Amalgams.LocalStructure
public import CFSG.Quasithin.ChapterF.Section01.SourceDefs
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Theory.SpecificGroups.PSL2.AutomorphismModel

/-!
# The source weak-BN hypotheses for a Goldschmidt amalgam

The common Sylow subgroup is self-normalizing in each vertex, so both
source Borels equal the literal intersection and both source parabolics
are the original vertices. Transport S₃ through the actual SL₂(2) and
PSL₂(2) equivalences. With O₂(G) trivial and both vertices of characteristic
two, these constructions establish all six clauses of Source.HypothesisF11.

This proves the input assertion of Aschbacher–Smith Remark F.6.4,
printed p.305. F.1.9 and the six-case specialization of F.1.12 remain
separate recognition results; the legacy WeakBNPair is not used.
-/

public section

open Subgroup

namespace CFSG.Quasithin.ChapterF
open Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

 theorem IsGoldschmidtTriple.left_borel_eq_intersection (h : IsGoldschmidtTriple G₁ G₂) :
    Source.borel G₁ (G₁ ⊓ G₂) = G₁ ⊓ G₂ := by
  obtain ⟨S, hS⟩ := h.intersection_sylow
  have hle : (S : Subgroup G) ≤ G₁ := hS.symm.le.trans inf_le_left
  have hn := SymmetricThreeTwoCore.sylow_self_normalizing h.quotient_left.some (S.subtype hle)
  change normalizer (((S : Subgroup G).subgroupOf G₁) : Set G₁) =
    (S : Subgroup G).subgroupOf G₁ at hn
  rw [← subgroupOf_normalizer_eq hle] at hn
  change G₁ ⊓ normalizer (((G₁ ⊓ G₂) ⊓ G₁ : Subgroup G) : Set G) = G₁ ⊓ G₂
  rw [inf_eq_left.mpr inf_le_left, hS]
  apply le_antisymm
  · rintro x ⟨hx, hnX⟩
    exact show (⟨x, hx⟩ : G₁) ∈ (S : Subgroup G).subgroupOf G₁ from
      hn ▸ (show (⟨x, hx⟩ : G₁) ∈ (normalizer (S : Set G)).subgroupOf G₁ from hnX)
  · exact le_inf hle (S : Subgroup G).le_normalizer

 theorem IsGoldschmidtTriple.right_borel_eq_intersection (h : IsGoldschmidtTriple G₁ G₂) :
    Source.borel G₂ (G₁ ⊓ G₂) = G₁ ⊓ G₂ := by
  simpa only [inf_comm G₂ G₁] using h.symm.left_borel_eq_intersection

 @[expose] def goldschmidtVertices (G₁ G₂ : Subgroup G) (i : Fin 2) : Subgroup G :=
  if i = 0 then G₁ else G₂

 private theorem rank_one_model_of_perm_three {H : Type*} [Group H]
    (e : H ≃* Equiv.Perm (Fin 3)) : Source.IsRankOneModel H := by
  apply Source.IsRankOneModel.linear 1 (by decide)
  refine ⟨ZMod 2, inferInstance, inferInstance, by simp, ?_⟩
  exact ⟨e.trans (SLTwoPermThree.sl2Two_equiv_perm_three.some.symm.trans
    (Theory.PSL2.sl2QuotientEquiv (ZMod 2)))⟩

 theorem IsGoldschmidtTriple.source_hypothesis_of_characteristic_two
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (h₁ : generalizedFitting G₁ = pCore 2 G₁)
    (h₂ : generalizedFitting G₂ = pCore 2 G₂) :
    Source.HypothesisF11 (goldschmidtVertices G₁ G₂) (G₁ ⊓ G₂) := by
  classical
  let L := goldschmidtVertices G₁ G₂
  let T := G₁ ⊓ G₂
  have hLi (i : Fin 2) : T ≤ L i := by
    fin_cases i
    · exact inf_le_left
    · exact inf_le_right
  have hB (i : Fin 2) : Source.borel (L i) T = T := by
    fin_cases i
    · exact h.left_borel_eq_intersection
    · exact h.right_borel_eq_intersection
  have hP (i : Fin 2) : Source.parabolic L T i = L i := by
    change L i ⊔ T ⊔ Source.borel (L (Source.other i)) T = L i
    rw [hB, sup_eq_left.mpr (hLi i), sup_eq_left.mpr (hLi i)]
  have hgen : Source.generated L T = ⊤ := by
    change G₁ ⊔ G₂ ⊔ T = ⊤
    rw [h.generated, top_sup_eq]
  obtain ⟨S, hS⟩ := h.intersection_sylow
  refine ⟨inferInstance, hS ▸ S.isPGroup', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (hLi i).trans (L i).le_normalizer
  · intro i
    have hSL : (S : Subgroup G) ≤ L i := hS.symm.le.trans (hLi i)
    refine ⟨S.subtype hSL, ?_⟩
    change ((S : Subgroup G).subgroupOf (L i)).map (L i).subtype = T ⊓ L i
    rw [map_subgroupOf_eq_of_le hSL, ← hS, inf_eq_left.mpr (hLi i)]
  · intro i
    fin_cases i
    · exact rank_one_model_of_perm_three h.quotient_left.some
    · exact rank_one_model_of_perm_three h.quotient_right.some
  · intro i
    rw [hB]
    exact (hLi i).trans (L i).le_normalizer
  · rw [hgen]
    have he := pCore_map_iso (p := 2) (f := (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G))
    rw [hcore] at he
    apply le_bot_iff.mp
    have hk : (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom.ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff _).mpr Subgroup.topEquiv.injective
    exact hk ▸ (Subgroup.map_eq_bot_iff _).mp he
  · intro i
    rw [hP]
    fin_cases i
    · exact h₁
    · exact h₂
end CFSG.Quasithin.ChapterF
