module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.Geometry

/-!
# The displayed Sylow subgroup and elementary normalizers

The four normalizers in the whole concrete centralizer have orders
384, 128, 64 and 64. The normalizer of S is exactly the displayed subgroup D.
A finite calculation only on the twenty-four pair-permutation coordinates
suffices, because every pair-flip normalizes each elementary subgroup.
Transport identifies the displayed D as an ambient Sylow two-subgroup,
without requiring the supplied marking to identify it with the original Sylow.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Section 1, p.225 and Lemma 2.1.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
open Coordinates

private theorem normalizer_test (k : Fin 4) (x : H) :
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

private theorem base_generators_normalize : ∀ (k : Fin 4) (i : Fin 4),
    elementaryGenerators 0 i ∈ normalizer (elementary k : Set H) := by
  intro k i
  rw [normalizer_test]
  have hc : ∀ (k i j l : Fin 4), elementaryGenerators k l *
      (elementaryGenerators 0 i * elementaryGenerators k j * (elementaryGenerators 0 i)⁻¹) =
      (elementaryGenerators 0 i * elementaryGenerators k j * (elementaryGenerators 0 i)⁻¹) *
        elementaryGenerators k l := by decide +kernel
  exact hc k i

private theorem baseWord_normalizes (k : Fin 4) (a : BaseCode) :
    baseWord a ∈ normalizer (elementary k : Set H) := by
  unfold baseWord
  repeat' first | apply mul_mem | apply pow_mem
  · exact base_generators_normalize k 0
  · exact base_generators_normalize k 1
  · exact base_generators_normalize k 2
  · exact base_generators_normalize k 3

private def normalizingActor (k : Fin 4) (a : ActorCode) : Prop :=
  k = 0 ∨ (a.2.2.1 = 0 ∧ (k = 1 ∨ a.2.1 = 0))

local instance (k : Fin 4) (a : ActorCode) : Decidable (normalizingActor k a) := by
  unfold normalizingActor
  infer_instance

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem actor_normalizer_test : ∀ (k : Fin 4) (a : ActorCode),
    (∀ i j, elementaryGenerators k j * (actorWord a * elementaryGenerators k i * (actorWord a)⁻¹) =
      (actorWord a * elementaryGenerators k i * (actorWord a)⁻¹) * elementaryGenerators k j) ↔
      normalizingActor k a := by decide +kernel

private theorem word_normalizer_test (k : Fin 4) (a : Code) :
    word a ∈ normalizer (elementary k : Set H) ↔ normalizingActor k a.2 := by
  rw [word, (normalizer (elementary k : Set H)).mul_mem_cancel_left (baseWord_normalizes k a.1),
    normalizer_test, actor_normalizer_test]

/-- M is normal in the whole model centralizer. -/
public theorem modelM_normalizer : normalizer (modelM : Set H) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨a, rfl⟩ := word_bijective.surjective x
  exact (word_normalizer_test 0 a).mpr (Or.inl rfl)

/-- The source D equals the local normalizer of S. -/
public theorem modelS_normalizer : normalizer (modelS : Set H) = modelD := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a, rfl⟩ := word_bijective.surjective x
    have ha : a.2.2.2.1 = 0 := by
      simpa [normalizingActor] using (word_normalizer_test 1 a).mp hx
    have hm : ∀ i : Fin 7, (![pi, mu, mup, tau, taup, lam, xi] : Fin 7 → H) i ∈ modelD :=
      fun i => subset_closure ⟨i, rfl⟩
    unfold word baseWord actorWord
    rw [ha]
    simp only [Fin.val_zero, pow_zero, mul_one]
    repeat' first | apply modelD.mul_mem | apply modelD.pow_mem
    all_goals first
      | exact hm 0
      | exact hm 1
      | exact hm 2
      | exact hm 3
      | exact hm 4
      | exact hm 5
      | exact hm 6
  · rw [modelD, closure_le]
    rintro x ⟨i, rfl⟩
    apply (normalizer_test 1 _).mpr
    have hc : ∀ (i : Fin 7) (j l : Fin 4), elementaryGenerators 1 l *
        ((![pi, mu, mup, tau, taup, lam, xi] : Fin 7 → H) i * elementaryGenerators 1 j *
          ((![pi, mu, mup, tau, taup, lam, xi] : Fin 7 → H) i)⁻¹) =
        ((![pi, mu, mup, tau, taup, lam, xi] : Fin 7 → H) i * elementaryGenerators 1 j *
          ((![pi, mu, mup, tau, taup, lam, xi] : Fin 7 → H) i)⁻¹) * elementaryGenerators 1 l := by
      decide +kernel
    exact hc i

public theorem word_mem_modelD (a : Code) : word a ∈ modelD ↔ a.2.2.2.1 = 0 := by
  rw [← modelS_normalizer, word_normalizer_test]
  simp [normalizingActor]

/-- Orders of the four local normalizers: 384, 128, 64, 64. -/
public theorem elementary_normalizer_card (k : Fin 4) :
    Nat.card (normalizer (elementary k : Set H)) = (![384, 128, 64, 64] : Fin 4 → ℕ) k := by
  rw [← Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective word word_bijective)
    (fun a => (word_normalizer_test k a).symm))]
  rw [Nat.card_eq_fintype_card]
  revert k
  decide +kernel

public theorem modelD_card : Nat.card modelD = 128 := by
  rw [← modelS_normalizer]
  exact elementary_normalizer_card 1

universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

omit [Finite G] in
public theorem ambientD_card : Nat.card (ambientD D e) = 128 := by
  rw [ambientD, card_map_of_injective (D.a10ModelEmbedding_injective e), modelD_card]

/-- The displayed D is an ambient Sylow subgroup for every supplied marking. -/
@[expose] public noncomputable def ambientSylow : Sylow 2 G := Sylow.ofCard (ambientD D e) (by
  rw [ambientD_card]
  exact D.sylow_card.symm.trans D.sylow.card_eq_multiplicity)

public theorem ambientElementary_le_ambientSylow (k : Fin 4) :
    ambientElementary D e k ≤ ambientSylow D e := map_mono (elementary_le_modelD k)

public theorem ambientSylow_le_normalizer_S :
    (ambientSylow D e : Subgroup G) ≤ normalizer (ambientElementary D e 1 : Set G) := by
  change modelD.map (D.a10ModelEmbedding e) ≤
    normalizer (((elementary 1).map (D.a10ModelEmbedding e) : Subgroup G) : Set G)
  rw [← modelS_normalizer]
  exact le_normalizer_map _

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
