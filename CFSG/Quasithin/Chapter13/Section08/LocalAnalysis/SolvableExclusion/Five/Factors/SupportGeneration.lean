module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.FactorData
public import Theory.GroupAction.SupportTransport
public import Mathlib.Order.SupIndep
public import Mathlib.Tactic

/-!
# Generation by the actual moved supports

The generated five-factors in `Factorization` generate the actor image,
and action commutators preserve this join. Thus the full P-displacement
is the join of precisely the recorded supports. Together with the one-or-two
factor bound and their disjointness, this supplies the source's direct sum;
no extra support-generation premise is required by the factor construction.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.13,
printed p.951, the decomposition [P,Ũ_H] = Ũ₁ ⊕ ··· ⊕ Ũ_s.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
variable {G : Type*} [Group G]
variable {H UH V₁ : Subgroup G} [(V₁.subgroupOf UH).Normal]

private theorem subgroupOf_iSup_of_le {ι : Sort*} (F : ι → Subgroup G)
    (hF : ∀ i, F i ≤ H) : (⨆ i, F i).subgroupOf H = ⨆ i, (F i).subgroupOf H := by
  apply Subgroup.map_injective H.subtype_injective
  rw [map_subgroupOf_eq_of_le (iSup_le hF), Subgroup.map_iSup]
  simp_rw [map_subgroupOf_eq_of_le (hF _)]

theorem StarAction.actors_iSup (a : StarAction H UH V₁)
    {ι : Sort*} (F : ι → Subgroup G) (hF : ∀ i, F i ≤ H) :
    a.actors (⨆ i, F i) = ⨆ i, a.actors (F i) := by
  simp only [StarAction.actors, Source.starImage,
    subgroupOf_iSup_of_le F hF, Subgroup.map_iSup]

theorem Factorization.support_generated {a : StarAction H UH V₁} {P : Subgroup G}
    (f : Factorization a P) (hPH : P ≤ H) :
    commutatorAction (a.actors P) (UH ⧸ V₁.subgroupOf UH) = ⨆ i, f.support i := by
  apply ActionSupport.commutatorAction_eq_iSup_of_eq_iSup
  calc
    a.actors P = a.actors (⨆ i, f.factor i) := congrArg a.actors f.generated
    _ = ⨆ i, a.actors (f.factor i) := a.actors_iSup _ (fun i => (f.factor_le i).trans hPH)

private theorem independent_of_at_most_two {α : Type*} [CompleteLattice α]
    {n : ℕ} (hn : n ≤ 2) (F : Fin n → α)
    (hd : ∀ i j, i ≠ j → Disjoint (F i) (F j)) : iSupIndep F := by
  intro i
  by_cases hi : i.val = 0
  · by_cases hn1 : n = 1
    · subst n
      exact iSupIndep_subsingleton F i
    · have hn2 : n = 2 := by have := i.isLt; omega
      subst n
      have he : i = 0 := Fin.ext hi
      subst i
      apply (hd 0 1 (by decide)).mono_right
      apply iSup_le
      intro j
      apply iSup_le
      intro hj
      have he : j = 1 := by apply Fin.ext; have := j.isLt; omega
      subst j
      exact le_rfl
  · have hn2 : n = 2 := by have := i.isLt; omega
    subst n
    have he : i = 1 := by apply Fin.ext; have := i.isLt; omega
    subst i
    apply (hd 1 0 (by decide)).mono_right
    apply iSup_le
    intro j
    apply iSup_le
    intro hj
    have he : j = 0 := by apply Fin.ext; have := j.isLt; omega
    subst j
    exact le_rfl

theorem Factorization.support_independent {a : StarAction H UH V₁} {P : Subgroup G}
    (f : Factorization a P) : iSupIndep f.support :=
  independent_of_at_most_two f.count_le_two f.support f.support_disjoint

theorem Factorization.factor_independent {a : StarAction H UH V₁} {P : Subgroup G}
    (f : Factorization a P) : iSupIndep f.factor :=
  independent_of_at_most_two f.count_le_two f.factor f.disjoint

theorem Factorization.factor_cyclic {a : StarAction H UH V₁} {P : Subgroup G}
    (f : Factorization a P) (i : Fin f.count) : IsCyclic (f.factor i) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact isCyclic_of_prime_card (f.factor_card i)

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
end
