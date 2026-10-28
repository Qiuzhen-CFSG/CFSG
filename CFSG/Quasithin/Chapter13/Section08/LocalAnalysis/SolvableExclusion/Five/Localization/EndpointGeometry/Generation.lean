module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Localization.Data
public import Theory.Frattini.PGroup
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# Normal generation from the five-primary irreducibility

The actual commuting cyclic-five factors make P elementary abelian and
therefore make the Frattini subgroup of P* trivial. Intersecting P* with
the normal closure of the given actor yields a nonzero invariant subgroup.
Irreducibility forces that intersection to be P*. Lifting through O₂(H),
which lies in L₁T, proves H = ⟨B^H⟩(L₁T) in join form.

For the supplied rank-one factor data, the first moved factor supplies the
nonzero commutator. Applying the corresponding argument at the reversed
critical pair, and transporting its edge, remains a separate geometry step;
base generation alone is not endpoint generation.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.13,
printed p.951, the paragraph beginning “Therefore”.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter13.Section08
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.Localization.EndpointGeometry
variable {G : Type*} [Group G]
variable {H U Z P : Subgroup G} [(Z.subgroupOf U).Normal]

theorem factors_elementary (a : StarAction H U Z) (f : Factorization a P) :
    IsElementaryAbelian 5 P := by
  have hc (i : Fin f.count) : IsMulCommutative (f.factor i) := by
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    let : IsCyclic (f.factor i) := isCyclic_of_prime_card (f.factor_card i)
    infer_instance
  have hp (i : Fin f.count) (x : f.factor i) : x ^ 5 = 1 := by
    rw [← f.factor_card i]
    exact pow_card_eq_one' (x := x)
  rw [f.generated, iSup_eq_closure]
  let s : Set G := ⋃ i, (f.factor i : Set G)
  have hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy
    by_cases hij : i = j
    · subst j
      let := hc i
      exact congrArg Subtype.val (mul_comm (⟨x, hi⟩ : f.factor i) ⟨y, hj⟩)
    · exact (commutator_eq_bot_iff_le_centralizer.mp (f.commute i j hij) hi y hj).symm
  let : IsMulCommutative (closure s) := isMulCommutative_closure hcomm
  apply IsElementaryAbelian.closure_of_isMulCommutative s
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  exact congrArg Subtype.val (hp i ⟨x, hi⟩)

theorem factors_starFrattini_eq_bot [Finite G] (a : StarAction H U Z)
    (f : Factorization a P) (hPH : P ≤ H) : starFrattini H P = ⊥ := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : IsElementaryAbelian 5 P := factors_elementary a f
  let : IsElementaryAbelian 5 (P.subgroupOf H) := IsElementaryAbelian.subgroupOf hPH
  let : IsElementaryAbelian 5 (Source.starImage H P) :=
    IsElementaryAbelian.map (QuotientGroup.mk' (pCore 2 H))
  let : Fact (IsPGroup 5 (Source.starImage H P)) :=
    ⟨IsElementaryAbelian.isPGroup 5 _⟩
  unfold starFrattini
  rw [frattini_eq_bot_of_isElementaryAbelian (p := 5), Subgroup.map_bot]

theorem normal_contains_irreducible_of_commutator
    (P E B N : Subgroup G) [P.Normal] [N.Normal]
    (hirr : ∀ D : Subgroup G, D ≤ P → E ≤ normalizer (D : Set G) → D = ⊥ ∨ D = P)
    (hBN : B ≤ N) (hmoved : ⁅P, B⁆ ≠ ⊥) : P ≤ N := by
  have hi := hirr (P ⊓ N) inf_le_left le_normalizer_of_normal
  rcases hi with hzero | hfull
  · exfalso
    apply hmoved
    apply le_bot_iff.mp
    rw [← hzero]
    exact le_inf (commutator_le_left P B)
      ((commutator_mono le_rfl hBN).trans (commutator_le_right P N))
  · exact hfull.symm.le.trans inf_le_right

theorem base_generation_of_moves [Finite G]
    {L₁ T M Vα B : Subgroup G}
    (a : StarAction H U Z) (reduced : ReducedFive H L₁ T M Vα)
    (f : Factorization a reduced.P)
    (hBH : B ≤ H) (hcore : Source.QH H ≤ L₁ ⊔ T)
    (hmoved : ⁅Source.starImage H reduced.P, Source.starImage H B⁆ ≠ ⊥) :
    H = conjugateSpanBy B H ⊔ (L₁ ⊔ T) := by
  let N := conjugateSpanBy B H
  have hNH : N ≤ H := conjugateSpanBy_le_self hBH
  have hHN : H ≤ normalizer (N : Set G) := le_normalizer_conjugateSpanBy B H
  let : (N.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hHN
  let : (Source.starImage H N).Normal := Subgroup.Normal.map inferInstance
    (QuotientGroup.mk' (pCore 2 H)) (QuotientGroup.mk'_surjective _)
  let := reduced.Pstar_normal
  have hPhi := factors_starFrattini_eq_bot a f reduced.P_le
  have hirr : ∀ D : Subgroup (Source.Hstar H), D ≤ Source.starImage H reduced.P →
      Source.starImage H (L₁ ⊔ T) ≤ normalizer (D : Set (Source.Hstar H)) →
      D = ⊥ ∨ D = Source.starImage H reduced.P := by
    intro D hDP hED
    simpa only [hPhi] using reduced.irreducible D (hPhi ▸ bot_le) hDP hED
  have hBN : Source.starImage H B ≤ Source.starImage H N :=
    map_mono (fun _ hx => le_conjugateSpanBy B H hx)
  have hPN : Source.starImage H reduced.P ≤ Source.starImage H N :=
    normal_contains_irreducible_of_commutator _ _ _ _ hirr hBN hmoved
  have hPL : reduced.P ≤ N ⊔ Source.QH H := by
    intro p hp
    let pH : H := ⟨p, reduced.P_le hp⟩
    have hi := hPN (mem_map_of_mem (QuotientGroup.mk' (pCore 2 H))
      (show pH ∈ reduced.P.subgroupOf H from hp))
    have hc : pH ∈ (N.subgroupOf H) ⊔ pCore 2 H := by
      have hh : pH ∈ ((N.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))).comap
        (QuotientGroup.mk' (pCore 2 H)) := hi
      simpa only [comap_map_eq, QuotientGroup.ker_mk'] using hh
    have hm := mem_map_of_mem H.subtype hc
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hNH] at hm
    exact hm
  apply le_antisymm
  · apply reduced.generated.le.trans
    exact sup_le (hPL.trans (sup_le_sup_left hcore N)) le_sup_right
  · exact sup_le hNH (reduced.generated ▸ le_sup_right)
/-- The moved first factor supplies normal generation for the original actor. -/
theorem base_generation [Finite G]
    {L₁ T M Vα B : Subgroup G}
    (a : StarAction H U Z) (reduced : ReducedFive H L₁ T M Vα)
    (f : RankOneFactors a reduced.P B)
    (hBH : B ≤ H) (hcore : Source.QH H ≤ L₁ ⊔ T) :
    H = conjugateSpanBy B H ⊔ (L₁ ⊔ T) := by
  apply base_generation_of_moves a reduced f.factors hBH hcore
  intro hh
  apply f.first_moved
  apply le_bot_iff.mp
  rw [commutator_comm] at hh
  apply le_trans _ hh.le
  exact commutator_mono le_rfl (map_mono (fun _ hx =>
    f.factors.factor_le ⟨0, f.factors.count_pos⟩ hx))

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.Localization.EndpointGeometry

end
