module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.Catalogue

/-!
# Ambient elementary subgroups in Held's displayed Sylow group

The exact catalogue in the model transports along the supplied centralizer
isomorphism. Every elementary subgroup of order sixteen in the displayed
ambient Sylow subgroup is one of the four specified images and centralizes mu.
The local normalizer calculation also gives the exact intersections of the
four ambient normalizers with C_G(pi); it does not determine the full ambient
normalizers.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Section 1, p.225 and Lemmas 2.4--2.6.
-/

open Subgroup Equiv
open scoped IsMulCommutative
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
open Coordinates

public theorem mu_mem_elementary (k : Fin 4) : mu ∈ elementary k := by
  have h := elementaryGenerators_mem k 1
  have he : elementaryGenerators k 1 = mu := by fin_cases k <;> rfl
  rwa [he] at h

public theorem elementary_le_centralizer_mu (k : Fin 4) :
    elementary k ≤ centralizer ({mu} : Set H) := by
  intro x hx
  let := elementary_isElementaryAbelian k
  exact mem_centralizer_singleton_iff.mpr (setLike_mul_comm hx (mu_mem_elementary k))

universe u
variable {G : Type u} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

public theorem ambient_normalizer_inf_centralizer (k : Fin 4) :
    normalizer (ambientElementary D e k : Set G) ⊓ D.centralizer =
      (normalizer (elementary k : Set H)).map (D.a10ModelEmbedding e) := by
  have h := comap_normalizer_eq_of_le_range
    (show ambientElementary D e k ≤ (D.a10ModelEmbedding e).range from map_le_range _ _)
  rw [ambientElementary, comap_map_eq_self_of_injective (D.a10ModelEmbedding_injective e)] at h
  have hm := congrArg (Subgroup.map (D.a10ModelEmbedding e)) h
  rw [map_comap_eq, D.a10ModelEmbedding_range e] at hm
  simpa only [ambientElementary, inf_comm] using hm

public theorem ambient_normalizer_intersection_card (k : Fin 4) :
    Nat.card (normalizer (ambientElementary D e k : Set G) ⊓ D.centralizer : Subgroup G) =
      (![384, 128, 64, 64] : Fin 4 → ℕ) k := by
  rw [ambient_normalizer_inf_centralizer,
    card_map_of_injective (D.a10ModelEmbedding_injective e), elementary_normalizer_card]

public theorem centralizer_le_normalizer_M :
    D.centralizer ≤ normalizer (ambientElementary D e 0 : Set G) := by
  have h := ambient_normalizer_inf_centralizer D e 0
  rw [show elementary 0 = modelM from rfl, modelM_normalizer,
    ← MonoidHom.range_eq_map, D.a10ModelEmbedding_range e] at h
  exact inf_eq_right.mp h

public theorem normalizer_S_inf_centralizer :
    normalizer (ambientElementary D e 1 : Set G) ⊓ D.centralizer = ambientD D e := by
  rw [ambient_normalizer_inf_centralizer, show elementary 1 = modelS from rfl, modelS_normalizer]
  rfl

public theorem ambientElementary_le_centralizer_mu (k : Fin 4) :
    ambientElementary D e k ≤ centralizer ({D.a10NoncentralInvolution e} : Set G) := by
  have h := map_mono (f := D.a10ModelEmbedding e) (elementary_le_centralizer_mu k)
  rw [ambient_centralizer_mu_map] at h
  exact h.trans inf_le_right

/-- The four images exhaust the elementary subgroups of order sixteen in the displayed Sylow. -/
public theorem ambient_elementary_sixteen [Finite G] (A : Subgroup G)
    (hAT : A ≤ ambientSylow D e) (hA : IsElementaryAbelian 2 A)
    (hcard : Nat.card A = 16) : ∃ k : Fin 4, A = ambientElementary D e k := by
  let f := D.a10ModelEmbedding e
  let B := A.comap f
  have hf : Function.Injective f := D.a10ModelEmbedding_injective e
  have hArange : A ≤ f.range := hAT.trans (map_le_range _ _)
  have hmap : B.map f = A := map_comap_eq_self hArange
  have hBT : B ≤ modelD := by
    have h := comap_mono (f := f) hAT
    change B ≤ (modelD.map f).comap f at h
    rwa [comap_map_eq_self_of_injective hf] at h
  have hBc : Nat.card B = 16 := by
    rw [Nat.card_congr (B.equivMapOfInjective f hf).toEquiv, hmap, hcard]
  have hBe : IsElementaryAbelian 2 B := by
    have hs (x : B) : x ^ 2 = 1 := by
      apply Subtype.ext
      apply hf
      let := hA
      simpa only [Subgroup.coe_pow, Subgroup.coe_one, map_pow, map_one] using
        elemPow_eq_one_of_isElementaryAbelian (p := 2) (f x) x.property
    refine
      { is_comm := ?_
        exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }
    exact ⟨fun x y => (Commute.of_orderOf_dvd_two
      (fun x => orderOf_dvd_of_pow_eq_one (hs x)) x y).eq⟩
  obtain ⟨k, hk⟩ := model_elementary_sixteen B hBT hBe hBc
  exact ⟨k, hmap.symm.trans (congrArg (Subgroup.map f) hk)⟩

/-- Every elementary sixteen in the displayed Sylow lies in its index-two mu-centralizer. -/
public theorem ambient_elementary_sixteen_le_centralizer_mu [Finite G] (A : Subgroup G)
    (hAT : A ≤ ambientSylow D e) (hA : IsElementaryAbelian 2 A)
    (hcard : Nat.card A = 16) :
    A ≤ centralizer ({D.a10NoncentralInvolution e} : Set G) := by
  obtain ⟨k,rfl⟩ := ambient_elementary_sixteen D e A hAT hA hcard
  exact ambientElementary_le_centralizer_mu D e k

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
