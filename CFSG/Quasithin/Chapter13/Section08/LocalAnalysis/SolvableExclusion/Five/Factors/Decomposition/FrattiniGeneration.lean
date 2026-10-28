module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Factors.Lift
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Theory.GroupTheory.CoprimeCentralizerDecomposition

/-!
# Frattini generation of the supplied five-group

A normal subgroup of P* with nonzero image on P*/Φ(P*) is all of P*:
use the irreducibility in `ReducedFive`, then Frattini nongeneration.
If it contains [P*,A] for a two-group A moving P*, coprime action ensures
that its Frattini image is nonzero. Indeed P*=[P*,A] C_P*(A), so a
commutator contained in Φ(P*) would force A to centralize P*.

This uses neither a small-order shape for P nor the desired factorization.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.13,
printed p.951, the minimality/Frattini irreducibility step.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion
variable {G : Type*} [Group G] [Finite G]
variable {H P L₁ T M Vα : Subgroup G}

theorem star_eq_of_sup_starFrattini_eq {N : Subgroup (Source.Hstar H)}
    (hN : N ≤ Source.starImage H P)
    (h : N ⊔ starFrattini H P = Source.starImage H P) :
    N = Source.starImage H P := by
  let F := Source.starImage H P
  have htop : N.subgroupOf F ⊔ frattini F = ⊤ := by
    apply map_injective F.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hN]
    change N ⊔ starFrattini H P = (⊤ : Subgroup F).map F.subtype
    rw [h, ← MonoidHom.range_eq_map, F.range_subtype]
  have ht := frattini_nongenerating htop
  have hm := congrArg (map F.subtype) ht
  rwa [map_subgroupOf_eq_of_le hN, ← MonoidHom.range_eq_map, F.range_subtype] at hm

omit [Finite G] in
theorem ReducedFive.star_ne_bot (r : ReducedFive H L₁ T M Vα) :
    Source.starImage H r.P ≠ ⊥ := by
  intro he
  exact r.moved (by simp [he])

theorem ReducedFive.normal_eq_of_not_le_starFrattini
    (r : ReducedFive H L₁ T M Vα)
    (N : Subgroup (Source.Hstar H)) [N.Normal]
    (hN : N ≤ Source.starImage H r.P) (hphi : ¬ N ≤ starFrattini H r.P) :
    N = Source.starImage H r.P := by
  let := r.Pstar_normal
  have hPhiN : (starFrattini H r.P).Normal := by
    dsimp [starFrattini]
    infer_instance
  let := hPhiN
  have hn : Source.starImage H (L₁ ⊔ T) ≤ normalizer ((N ⊔ starFrattini H r.P : Subgroup (Source.Hstar H)) : Set (Source.Hstar H)) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  rcases r.irreducible (N ⊔ starFrattini H r.P) le_sup_right
    (sup_le hN (map_subtype_le _)) hn with he | he
  · exact False.elim (hphi (he ▸ (le_sup_left : N ≤ N ⊔ starFrattini H r.P)))
  · exact star_eq_of_sup_starFrattini_eq hN he

theorem ReducedFive.normal_eq_of_contains_commutator
    (r : ReducedFive H L₁ T M Vα)
    (N A : Subgroup (Source.Hstar H)) [N.Normal]
    (hN : N ≤ Source.starImage H r.P) (hA : IsPGroup 2 A)
    (hmoved : ⁅Source.starImage H r.P, A⁆ ≠ ⊥)
    (hcomm : ⁅Source.starImage H r.P, A⁆ ≤ N) :
    N = Source.starImage H r.P := by
  apply r.normal_eq_of_not_le_starFrattini N hN
  intro hphi
  let F := Source.starImage H r.P
  let C := F ⊓ centralizer (A : Set (Source.Hstar H))
  let := r.Pstar_normal
  have hp : IsPGroup 5 F := r.P_isPGroup.of_surjective
    (Five.fiveStarEquiv r.P_le r.P_isPGroup).toMonoidHom
    (Five.fiveStarEquiv r.P_le r.P_isPGroup).surjective
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Group.IsNilpotent F := hp.isNilpotent
  have hcop : Nat.Coprime (Nat.card A) (Nat.card F) :=
    IsPGroup.coprime_card_of_ne 2 5 (by decide) A F hA hp
  have hd := eq_commutator_sup_centralizer_of_solvable_coprime F A
    le_normalizer_of_normal inferInstance hcop
  have hsup : C ⊔ starFrattini H r.P = F := by
    apply le_antisymm (sup_le inf_le_left (map_subtype_le _))
    exact hd.le.trans (sup_le ((hcomm.trans hphi).trans le_sup_right) le_sup_left)
  have hC : C = F := star_eq_of_sup_starFrattini_eq inf_le_left hsup
  apply hmoved
  apply commutator_eq_bot_iff_le_centralizer.mpr
  exact hC.ge.trans inf_le_right

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion
end
