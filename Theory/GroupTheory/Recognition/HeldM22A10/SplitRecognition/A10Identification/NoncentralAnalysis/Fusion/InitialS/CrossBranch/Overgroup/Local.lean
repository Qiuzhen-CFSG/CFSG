module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.AmbientGeometry

/-!
# Local normalization for Held's cross branch

The common local centralizer of mu normalizes each of the four elementary
sixteens. Six generator checks prove this uniformly. The centralizer of
tau*lambda*xi in H is exactly L2, of order sixteen.

These are the concrete local inputs to the order-64 overgroup in Held's
Lemma 2.9, printed p.230, Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756.
-/
open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
open Coordinates

private theorem local_normalizer_test (k : Fin 4) (x : H) :
    x ∈ normalizer (elementary k : Set H) ↔
      ∀ i j, elementaryGenerators k j * (x * elementaryGenerators k i * x⁻¹) =
        (x * elementaryGenerators k i * x⁻¹) * elementaryGenerators k j := by
  have hm (y : H) : y ∈ elementary k ↔ ∀ j,
      elementaryGenerators k j * y = y * elementaryGenerators k j := by
    rw [← elementary_selfCentralizing k, elementary_eq_closure k,
      centralizer_closure]
    simp only [mem_centralizer_iff, Set.forall_mem_range]
  constructor
  · intro hx i
    exact (hm _).mp ((mem_normalizer_iff.mp hx _).mp (elementaryGenerators_mem k i))
  · intro hx
    rw [mem_normalizer_iff_map_conj_eq]
    apply eq_of_le_of_card_ge
    · rw [elementary_eq_closure k, MonoidHom.map_closure, closure_le]
      rintro y ⟨_, ⟨i, rfl⟩, rfl⟩
      rw [← elementary_eq_closure k]
      exact (hm _).mpr (hx i)
    · rw [card_map_of_injective (MulAut.conj x).injective]

private def crossNormalizingGenerator : Fin 6 → H := ![pi, mu, mup, xi, tau, lam]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem cross_generators_normalize (k : Fin 4) (i : Fin 6) :
    crossNormalizingGenerator i ∈ normalizer (elementary k : Set H) := by
  apply (local_normalizer_test k _).mpr
  have ht : ∀ (k : Fin 4) (i : Fin 6) (j l : Fin 4),
      elementaryGenerators k l * (crossNormalizingGenerator i * elementaryGenerators k j *
        (crossNormalizingGenerator i)⁻¹) =
      (crossNormalizingGenerator i * elementaryGenerators k j * (crossNormalizingGenerator i)⁻¹) *
        elementaryGenerators k l := by decide +kernel
  exact ht k i

public theorem cross_model_mu_normalizes (k : Fin 4) :
    centralizer ({mu} : Set H) ≤ normalizer (elementary k : Set H) := by
  intro x hx
  obtain ⟨a, rfl⟩ := word_bijective.surjective x
  have hbase : baseWord a.1 ∈ centralizer ({mu} : Set H) := by
    apply elementary_le_centralizer_mu 0
    exact (mem_elementary 0 _).mpr ⟨a.1, rfl⟩
  have hactor : actorWord a.2 ∈ centralizer ({mu} : Set H) :=
    (mul_mem_cancel_left hbase).mp hx
  have ht : ∀ b : ActorCode, actorWord b * mu = mu * actorWord b →
      b.2.1 = 0 ∧ b.2.2.1 = 0 := by decide +kernel
  obtain ⟨htaup, hrho⟩ := ht a.2 (mem_centralizer_singleton_iff.mp hactor)
  simp only [word, baseWord, actorWord, htaup, hrho, Fin.val_zero, pow_zero, mul_one]
  repeat' first | apply mul_mem | apply pow_mem
  · exact cross_generators_normalize k 0
  · exact cross_generators_normalize k 1
  · exact cross_generators_normalize k 2
  · exact cross_generators_normalize k 3
  · exact cross_generators_normalize k 4
  · exact cross_generators_normalize k 5

public theorem cross_model_centralizer_eq :
    centralizer ({tau * lam * xi} : Set H) = elementary 3 := by
  have hcross : tau * lam * xi ∈ elementary 3 :=
    (elementary 3).mul_mem (elementaryGenerators_mem 3 2) (elementaryGenerators_mem 3 3)
  have hle : elementary 3 ≤ centralizer ({tau * lam * xi} : Set H) := by
    let := elementary_isElementaryAbelian 3
    intro y hy
    exact mem_centralizer_singleton_iff.mpr (setLike_mul_comm hy hcross)
  apply (eq_of_le_of_card_ge hle ?_).symm
  rw [elementary_card, involution_centralizer_cards.2.2.2.2.2.2.2]

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
