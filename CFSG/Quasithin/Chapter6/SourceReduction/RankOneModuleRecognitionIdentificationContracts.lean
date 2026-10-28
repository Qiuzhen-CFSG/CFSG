module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentification

/-!
# Shared local analysis for the two intersection branches

This is a specification of the common earlier mathematics in 6.2.1--12,
not a proof of those lemmas. The source producer must construct it from the
original Chapter 12 setup and the natural reduction. The equality and strict
intersection arguments can use this same interface while that producer runs.
No recognition conclusion, symmetric-five quotient, extraspecial core of the
whole involution centralizer, or intersection equality is a field here.

The action kernel is stated elementwise: an element centralizes U/⟨z⟩
exactly when all its commutators with U lie in ⟨z⟩. This keeps the literal
subgroups and avoids any ambient-normality assumption on ⟨z⟩ in G.
The pair assertion retains only the non-two-group alternative of 6.2.6,
with its actual two-core and actual quotient. It does not assert splitting.

Source: Aschbacher--Smith, 6.2.1--12, printed pp.680--686.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Earlier local analysis on the actual chosen involution centralizer.
Every field is an obligation of the earlier-source producer. -/
structure LocalAnalysis (T L M R : Subgroup G) (z : G) : Prop where
  central_omega : centralOmega T = zpowers z
  normalizer_plane : normalizer (ZS T L R : Set G) ≤ normalizer (layer L R : Set G)
  normalizer_layer : normalizer (layer L R : Set G) ≤ M
  plane_unique : ∀ g : G, ZS T L R ≤ (layer L R).map (MulAut.conj g).toMonoidHom →
    (layer L R).map (MulAut.conj g).toMonoidHom = layer L R
  hyperplane_unique : ∀ g : G,
    8 ≤ Nat.card (layer L R ⊓ (layer L R).map (MulAut.conj g).toMonoidHom : Subgroup G) →
    (layer L R).map (MulAut.conj g).toMonoidHom = layer L R
  commuting_normalized : ∀ g : G,
    layer L R ≤ normalizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G) →
    (layer L R).map (MulAut.conj g).toMonoidHom ≤ normalizer (layer L R : Set G) →
    ⁅layer L R, (layer L R).map (MulAut.conj g).toMonoidHom⁆ = ⊥
  commuting_noncyclic : ∀ g : G,
    4 ≤ Nat.card (layer L R ⊓ (layer L R).map (MulAut.conj g).toMonoidHom : Subgroup G) →
    ⁅layer L R, (layer L R).map (MulAut.conj g).toMonoidHom⁆ = ⊥
  non_two_pair : ∀ g : G,
    (layer L R ⊓ normalizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G)).relIndex
      (layer L R) = 2 →
    ((layer L R).map (MulAut.conj g).toMonoidHom ⊓ normalizer (layer L R : Set G)).relIndex
      ((layer L R).map (MulAut.conj g).toMonoidHom) = 2 →
    let J := layer L R ⊔ (layer L R).map (MulAut.conj g).toMonoidHom
    ¬ IsPGroup 2 J →
      Nonempty (QuaternionCentralProductData (pCore 2 J)) ∧
      Nonempty ((J ⧸ pCore 2 J) ≃* Equiv.Perm (Fin 3)) ∧
      pCore 2 J ≤ pResidual 2 J ∧
      layer L R ⊓ (layer L R).map (MulAut.conj g).toMonoidHom =
        ((center (pCore 2 J)).map (pCore 2 J).subtype).map J.subtype
  layer_normalizer : centralizer ({z} : Set G) ⊓ normalizer (layer L R : Set G) =
    centralizer ({z} : Set G) ⊓ M
  plane_normalizer : centralizer ({z} : Set G) ⊓ normalizer (ZS T L R : Set G) =
    centralizer ({z} : Set G) ⊓ M
  fitting_core : generalizedFitting (centralizer ({z} : Set G)) =
    pCore 2 (centralizer ({z} : Set G))
  closure_le_core : sourceClosure T L R z ≤ (centralizer ({z} : Set G)).pCoreIn 2
  closure_core_commutator : ⁅sourceClosure T L R z, (centralizer ({z} : Set G)).pCoreIn 2⁆ ≤
    zpowers z
  action_kernel : ∀ x ∈ centralizer ({z} : Set G),
    (∀ u ∈ sourceClosure T L R z, ⁅x, u⁆ ∈ zpowers z) ↔
      x ∈ (centralizer ({z} : Set G)).pCoreIn 2
  layer_core_card : Nat.card
    (layer L R ⊓ (centralizer ({z} : Set G)).pCoreIn 2 : Subgroup G) = 8
  layer_closure_commutator : ⁅layer L R, sourceClosure T L R z⁆ ≤
    layer L R ⊓ sourceClosure T L R z
  residual_centralizes :
    (pResidual 2 (centralizer ({z} : Set G) ⊓ M : Subgroup G)).map
      (centralizer ({z} : Set G) ⊓ M).subtype ≤ centralizer (layer L R : Set G)

variable {z : G} {κ : GroupClass.{u}} {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}

/-- Source 6.2.14: strict intersection is exactly the order-eight intersection
with the actual two-core. Only the earlier local analysis is used. -/
theorem LocalAnalysis.strict_intersection_eq_core
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R) :
    sourceClosure (T : Subgroup G) L R z ⊓ layer L R =
      layer L R ⊓ (centralizer ({z} : Set G)).pCoreIn 2 ∧
    Nat.card (sourceClosure (T : Subgroup G) L R z ⊓ layer L R : Subgroup G) = 8 := by
  let I := sourceClosure (T : Subgroup G) L R z ⊓ layer L R
  have hle : I ≤ layer L R ⊓ (centralizer ({z} : Set G)).pCoreIn 2 :=
    le_inf inf_le_right (inf_le_left.trans A.closure_le_core)
  have hZcard := (h611.natural_ZS_geometry hnatural).2.1
  have hgt : 4 < Nat.card I := by
    have hlo := card_le_of_le hstrict.le
    have hne : Nat.card I ≠ 4 := by
      intro he
      exact hstrict.ne (eq_of_le_of_card_ge hstrict.le (by rw [hZcard]; exact he.le))
    rw [hZcard] at hlo
    change 4 ≤ Nat.card I at hlo
    omega
  have hdvd : Nat.card I ∣ 2 ^ 3 := by
    simpa only [A.layer_core_card, Nat.reducePow] using card_dvd_of_le hle
  obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hcard : Nat.card I = 8 := by
    interval_cases k <;> norm_num only [Nat.reducePow] at he <;> omega
  exact ⟨eq_of_le_of_card_ge hle (by rw [A.layer_core_card, hcard]), hcard⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
