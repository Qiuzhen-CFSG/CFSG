module

public import CFSG.Quasithin.ChapterF.Section01.SourceDefs
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Theory.SpecificGroups.PSL2.AutomorphismModel

/-!
# Cubic F.1.1 from local Sylow subgroups

The common two-subgroup is required to be Sylow in each of the two
parabolics. No Sylow assertion about their join is used. The S₃ quotient
makes its local normalizer equal to itself, so the two source Borels are
the original common subgroup and the source parabolics are the original
groups. This verifies all six clauses of corrected Hypothesis F.1.1.

The numerical input is the cubic specialization of F.1.12, on that
corrected hypothesis. It is kept explicit: the later Goldschmidt-triple
interface assumes an ambient Sylow subgroup and cannot supply this input.
Source: Aschbacher–Smith, F.1.1, pp.259–264, and the zero-core branch of
14.6.6(6), printed p.1024 of refs/quasithin.pdf.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Source
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The S₃ quotient identifies the local source Borel using only a local Sylow. -/
theorem borel_eq_of_cubic_local_sylow (P S : Subgroup G)
    (hS : Chapter1.IsSylowIn 2 S P)
    (e : (P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) : borel P S = S := by
  have hSP := (Chapter1.isSylowIn_iff.mp hS).2.1
  obtain ⟨R,hR⟩ := hS
  have hRS : (R : Subgroup P) = S.subgroupOf P := by
    apply map_injective P.subtype_injective
    rw [hR,map_subgroupOf_eq_of_le hSP]
  have hn := SymmetricThreeTwoCore.sylow_self_normalizing e R
  change normalizer ((R : Subgroup P) : Set P) = (R : Subgroup P) at hn
  rw [hRS,←subgroupOf_normalizer_eq hSP] at hn
  change P ⊓ normalizer ((S ⊓ P : Subgroup G) : Set G) = S
  rw [inf_eq_left.mpr hSP]
  apply le_antisymm
  · rintro x ⟨hx,hxn⟩
    exact show (⟨x,hx⟩ : P) ∈ S.subgroupOf P from hn ▸ hxn
  · exact le_inf hSP S.le_normalizer

private theorem rank_one_model_of_perm_three {H : Type u} [Group H]
    (e : H ≃* Equiv.Perm (Fin 3)) : IsRankOneModel H := by
  apply IsRankOneModel.linear 1 (by decide)
  refine ⟨ZMod 2,inferInstance,inferInstance,by simp,?_⟩
  exact ⟨e.trans (SLTwoPermThree.sl2Two_equiv_perm_three.some.symm.trans
    (Theory.PSL2.sl2QuotientEquiv (ZMod 2)))⟩

/-- All original F.1.1 clauses from the two local Sylows and local structure.
The ambient generated group is not required to have S as a Sylow subgroup. -/
theorem hypothesisF11_of_cubic_local_sylows (L : Fin 2 → Subgroup G) (S : Subgroup G)
    (hS : ∀ i, Chapter1.IsSylowIn 2 S (L i))
    (hq : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* Equiv.Perm (Fin 3)))
    (hchar : ∀ i, generalizedFitting (L i) = pCore 2 (L i))
    (hcore : pCore 2 (L 0 ⊔ L 1 : Subgroup G) = ⊥) :
    HypothesisF11 L S := by
  have hSL (i) := (Chapter1.isSylowIn_iff.mp (hS i)).2.1
  have hB (i) : borel (L i) S = S := borel_eq_of_cubic_local_sylow _ _ (hS i) (hq i).some
  have hP (i) : parabolic L S i = L i := by
    change L i ⊔ S ⊔ borel (L (other i)) S = L i
    rw [hB,sup_eq_left.mpr (hSL i),sup_eq_left.mpr (hSL i)]
  refine ⟨inferInstance,(Chapter1.isSylowIn_iff.mp (hS 0)).1,?_,?_,?_,?_,?_,?_⟩
  · exact fun i => (hSL i).trans (L i).le_normalizer
  · intro i
    rw [inf_eq_left.mpr (hSL i)]
    exact hS i
  · exact fun i => rank_one_model_of_perm_three (hq i).some
  · intro i
    rw [hB]
    exact (hSL i).trans (L i).le_normalizer
  · change pCore 2 (L 0 ⊔ L 1 ⊔ S : Subgroup G) = ⊥
    rwa [sup_eq_left.mpr ((hSL 0).trans le_sup_left)]
  · intro i
    rw [hP]
    exact hchar i

/-- The common-Sylow size consequence of genuine F.1.12 in its cubic
specialization. This input concerns corrected F.1.1 and local Sylows only. -/
def CubicF112SizeInput : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (L : Fin 2 → Subgroup G) (S : Subgroup G),
    HypothesisF11 L S → (∀ i, S ≤ L i) →
    (∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* Equiv.Perm (Fin 3))) → Nat.card S ≤ 128

/-- The final contradiction in original 14.6.6(6), without an ambient
Sylow assumption on the generated group. -/
theorem generated_twoCore_ne_bot_of_cubic_size
    (recognition : CubicF112SizeInput.{u}) (T : Subgroup G)
    (L : Fin 2 → Subgroup G) (S : Subgroup G)
    (hST : S ≤ T) (hindex : S.relIndex T ≤ 4) (hlarge : 512 < Nat.card T)
    (hS : ∀ i, Chapter1.IsSylowIn 2 S (L i))
    (hq : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* Equiv.Perm (Fin 3)))
    (hchar : ∀ i, generalizedFitting (L i) = pCore 2 (L i)) :
    (L 0 ⊔ L 1 : Subgroup G).pCoreIn 2 ≠ ⊥ := by
  intro hbot
  have hcore : pCore 2 (L 0 ⊔ L 1 : Subgroup G) = ⊥ :=
    (map_eq_bot_iff_of_injective _ (L 0 ⊔ L 1).subtype_injective).mp hbot
  have hF := hypothesisF11_of_cubic_local_sylows L S hS hq hchar hcore
  have hbound := recognition G L S hF
    (fun i => (Chapter1.isSylowIn_iff.mp (hS i)).2.1) hq
  have hc : Nat.card S * S.relIndex T = Nat.card T := by
    simpa only [relIndex_bot_left] using
      relIndex_mul_relIndex (⊥ : Subgroup G) S T bot_le hST
  have hm := Nat.mul_le_mul hbound hindex
  rw [hc] at hm
  omega

end CFSG.Quasithin.ChapterF.Source
