module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.Models
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.Residual
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.A318
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.LocalApplication
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.ExceptionalModels
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.Complete

/-!
# The rank-two branch of source 13.6.20

The actual reduced catalogue gives the complete rank split: either
m₃(K) = 2, or m₃(K) = 1 and K+ is isomorphic to PSL₃(2).
The genuine earlier local conclusions construct the application of
A.3.18 in H = KLᵥ. The comparison of its component image with K+ excludes
the signed cases (2) and (3b). Case (1) gives the exact theta identity
by intrinsic cubic generation, while (3a) gives it directly. The earlier
cubic quotient of Lᵥ then gives Lᵥ ≤ K.

The original conditional API retains the universal A.3.18 component clauses.
The separate `source_rank_two_without_A318` proves the required theta
identity on the seven surviving models using A.3.6 and the intrinsic
simple and triple-cover results. Only the genuine earlier A.3.6 and
A.3.12 inputs remain in that specialization.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
p.931, with A.3.18 on pp.51–53.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo
open ComponentSelection LocalApplication Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem cubic_closure_eq_of_local_theta (K L : Subgroup G) (v : G)
    (h : localComponent K L v = closure {x : localActor K L v | orderOf x = 3}) :
    closure {x : G | x ∈ K ⊔ Lv L v ∧ orderOf x = 3} = K := by
  have hm := congrArg (map (localActor K L v).subtype) h
  rw [map_subgroupOf_eq_of_le le_sup_left, MonoidHom.map_closure] at hm
  have he : (localActor K L v).subtype '' {x : localActor K L v | orderOf x = 3} =
      {x : G | x ∈ K ⊔ Lv L v ∧ orderOf x = 3} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, ((localActor K L v).orderOf_coe y).trans hy⟩
    · rintro ⟨hx, ho⟩
      exact ⟨⟨x, hx⟩, ((localActor K L v).orderOf_coe ⟨x, hx⟩).symm.trans ho, rfl⟩
  rw [he] at hm
  exact hm.symm

/-- The complete conditional rank-two branch of source 13.6.20.
All hypotheses for the literal A.3.18 application and all model exclusions
are constructed. Its two successful cases give θ(KLᵥ) = K and Lᵥ ≤ K. -/
theorem source_rank_two
    (hA36 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK KnownSimple.IsKnownSimple D → pCore 2 D = ⊥ →
        ∀ B : Subgroup D, B.IsCComponent → A36Conclusion B)
    (hA312 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK KnownSimple.IsKnownSimple X → pCore 2 X = ⊥ →
        ∀ (S : Sylow 2 X) (B : Subgroup X), B ∈ ChapterA.Section03.localCComponents S →
          ∃! D : Subgroup X, D.IsCComponent ∧ B ≤ D)
    (hA318 : EarlierA318ComponentCases.{u} KnownSimple.IsKnownSimple)
    {T : Sylow 2 G} {K L : Subgroup G} {z v : G} (d : SourceInputs T K L z v) :
    closure {x : G | x ∈ K ⊔ Lv L v ∧ orderOf x = 3} = K ∧ Lv L v ≤ K := by
  let a := source_application hA36 hA312 d
  have hcore := plus_twoCore_eq_bot_of_reduced K L (T : Subgroup G) z v
    d.normalizes_residual d.centralizes_z d.reduced_module
  have hex := source_signed_exclusions K L (T : Subgroup G) z v
    d.normalizes_residual d.centralizes_z d.selected hcore d.reduced_model
  have ha := hA318 (localActor K L v) a.actor_sqtk (localComponent K L v)
    a.component a.local_quasisimple 3 Nat.prime_three (by decide)
    (by rw [a.component_rank]; decide)
  cases ha with
  | residual hres =>
    exact source_residual_case K L (T : Subgroup G) z v d.selected d.rank_two
      a.intrinsic_quasisimple a.intrinsic_center_rank hres d.cubic_quotient
  | projective _ unitary q hmod hmodel =>
    exact (hex unitary q hmod a.image_quasisimple a.comparison (Or.inl hmodel)).elim
  | cover _ _ hcases =>
    rcases hcases with htheta | ⟨unitary, q, hmod, hmodel⟩
    · have h := cubic_closure_eq_of_local_theta K L v htheta
      exact ⟨h, (Lv_le_cubic_closure_sup K L v d.cubic_quotient).trans_eq h⟩
    · exact (hex unitary q hmod a.image_quasisimple a.comparison (Or.inr hmodel)).elim

/-- The source rank split with the ambient rank bound discharged by
Hypothesis 13.3.1. The rank-one conclusion identifies the literal K+. -/
theorem source_rank_split_of_source {T : Sylow 2 G} {K L : Subgroup G} {z v : G}
    (h : SourceHypothesis T L) (hv : orderOf v = 2)
    (hL : Tv (T : Subgroup G) v ≤ normalizer (Lv L v : Set G))
    (hz : Tv (T : Subgroup G) v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L (T : Subgroup G) z v)
    (hmodel : ReducedModel (plusImage K L (T : Subgroup G) z v hL hz K)) :
    primeRank 3 K = 2 ∨ primeRank 3 K = 1 ∧
      Nonempty (plusImage K L (T : Subgroup G) z v hL hz K ≃* Matrix.PSL3Two.PSL) :=
  source_rank_split K L (T : Subgroup G) z v hL hz hK
    ((h.qtke.involution_centralizer_sqtk hv).stronglyQuasithin 3 Nat.prime_three (by decide))
    hmodel

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo
