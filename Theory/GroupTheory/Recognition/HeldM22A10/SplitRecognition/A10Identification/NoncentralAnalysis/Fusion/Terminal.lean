module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.SourceChecks
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Coordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.AmbientGeometry
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.Bounds
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.Terminal.Twelve
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.Terminal.MuSylow
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.Terminal.Overgroup
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.Terminal.Orbit

/-!
# The terminal pi--mu contradiction in Held's Lemma 2.6

Under the terminal fusion assumptions, choose a Sylow two-subgroup of the
actual C_G(mu) containing S<mu',xi>. Its join with the displayed Sylow D has
order 384 and normalizes S by the four-group action and elementary-subgroup
fusion counts. The order-three exclusion then gives a twelve-element lambda
orbit in this join.

A twelve-element lambda orbit in an overgroup of order 384 makes its relative
centralizer have order 32. If tau belongs to that orbit, its centralizer is
conjugate to lambda's. Both already contain the explicitly computed local
centralizers of order 32, so equality forces their centers to have the same
order. Their computed center orders, 8 and 4, contradict this. The final theorem
constructs the overgroup and discharges its order, normalization and orbit-size
premises; only the terminal fusion assumptions remain as inputs.
Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemma 2.6, printed p.229.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
open Coordinates

universe u
variable {G : Type u} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

public theorem terminalRepresentative_mem_modelD (i : Fin 2) : terminalRepresentative i ∈ modelD := by
  fin_cases i
  · exact elementary_le_modelD 1 (elementaryGenerators_mem 1 3)
  · exact elementary_le_modelD 1 (elementaryGenerators_mem 1 2)

public theorem terminalRepresentative_mem_ambientD (i : Fin 2) :
    D.a10ModelEmbedding e (terminalRepresentative i) ∈ ambientD D e :=
  ⟨_, terminalRepresentative_mem_modelD i, rfl⟩

public theorem terminal_mappedCentralizer_card (i : Fin 2) :
    Nat.card ((terminalLocalCentralizer i).map (D.a10ModelEmbedding e)) = 32 := by
  rw [card_map_of_injective (D.a10ModelEmbedding_injective e), terminalLocalCentralizer_card]

public theorem terminal_mappedCentralizer_center_card (i : Fin 2) :
    Nat.card (center ((terminalLocalCentralizer i).map (D.a10ModelEmbedding e))) =
      (![8, 4] : Fin 2 → ℕ) i := by
  rw [← Nat.card_congr (centerCongr ((terminalLocalCentralizer i).equivMapOfInjective
    (D.a10ModelEmbedding e) (D.a10ModelEmbedding_injective e))).toEquiv]
  exact terminalLocalCentralizer_center_card i

public theorem terminal_centralizer_eq_map [Finite G] (K : Subgroup G)
    (hDK : ambientD D e ≤ K) (i : Fin 2)
    (hc : Nat.card (K ⊓ centralizer ({D.a10ModelEmbedding e (terminalRepresentative i)} : Set G) :
      Subgroup G) = 32) :
    K ⊓ centralizer ({D.a10ModelEmbedding e (terminalRepresentative i)} : Set G) =
      (terminalLocalCentralizer i).map (D.a10ModelEmbedding e) := by
  symm
  apply eq_of_le_of_card_ge
  · rintro x ⟨y, hy, rfl⟩
    refine ⟨hDK ⟨y, terminalLocalCentralizer_le_modelD i hy, rfl⟩,
      mem_centralizer_singleton_iff.mpr ?_⟩
    simpa only [map_mul] using congrArg (D.a10ModelEmbedding e)
      (mem_centralizer_singleton_iff.mp hy)
  · rw [hc, terminal_mappedCentralizer_card]

public theorem terminal_contradiction_of_twelve [Finite G] (K : Subgroup G)
    (hDK : ambientD D e ≤ K) (hK : Nat.card K = 384)
    (hlam : Nat.card (terminalOrbit K (D.a10ModelEmbedding e lam)) = 12)
    (htau : D.a10ModelEmbedding e tau ∈ terminalOrbit K (D.a10ModelEmbedding e lam)) :
    False := by
  have hx : D.a10ModelEmbedding e lam ∈ K :=
    hDK (terminalRepresentative_mem_ambientD D e 0)
  have hcount := terminalOrbit_card_mul K (D.a10ModelEmbedding e lam) hx
  rw [hlam, hK] at hcount
  have hcl : Nat.card (K ⊓ centralizer ({D.a10ModelEmbedding e lam} : Set G) : Subgroup G) = 32 := by
    omega
  have hct : Nat.card (K ⊓ centralizer ({D.a10ModelEmbedding e tau} : Set G) : Subgroup G) = 32 :=
    (terminalCentralizer_card_eq K htau).symm.trans hcl
  have hcent := terminalCentralizer_center_card_eq K htau
  have hl := terminal_centralizer_eq_map D e K hDK 0 hcl
  have ht := terminal_centralizer_eq_map D e K hDK 1 hct
  change K ⊓ centralizer ({D.a10ModelEmbedding e lam} : Set G) = _ at hl
  change K ⊓ centralizer ({D.a10ModelEmbedding e tau} : Set G) = _ at ht
  rw [hl, ht, terminal_mappedCentralizer_center_card, terminal_mappedCentralizer_center_card] at hcent
  norm_num at hcent

/-- The terminal comparison with tau membership derived from normalization of S.
The order of K and the twelve-element orbit remain explicit obligations. -/
public theorem terminal_contradiction_of_normalizes_of_twelve [Finite G] (K : Subgroup G)
    (hDK : ambientD D e ≤ K) (hK : Nat.card K = 384)
    (hKN : K ≤ normalizer (ambientElementary D e 1 : Set G))
    (hmu : IsConj D.z (D.a10NoncentralInvolution e))
    (hlam : ¬ IsConj D.z (D.a10ModelEmbedding e lam))
    (hsize : Nat.card (terminalOrbit K (D.a10ModelEmbedding e lam)) = 12) : False :=
  terminal_contradiction_of_twelve D e K hDK hK hsize
    (terminal_tau_mem_of_twelve D e K hKN hmu hlam hsize)

/-- Held's terminal contradiction in Lemma 2.6, printed p.229. The Sylow subgroup
at mu, the order and normalization of its join with D, and the twelve-element
lambda orbit are all constructed from the displayed fusion assumptions. -/
public theorem terminal_mu_contradiction [Finite G] [IsSimpleGroup G]
    (hmu : IsConj D.z (D.a10NoncentralInvolution e))
    (hlam : ¬ IsConj D.z (D.a10ModelEmbedding e lam))
    (htau : ¬ IsConj D.z (D.a10ModelEmbedding e tau))
    (hpilam : ¬ IsConj D.z (D.a10ModelEmbedding e (pi * lam)))
    (hxi : IsConj D.z (D.a10ModelEmbedding e xi) ∨
      IsConj D.z (D.a10ModelEmbedding e (pi * xi)) ∨
      IsConj D.z (D.a10ModelEmbedding e (tau * lam * xi))) : False := by
  obtain ⟨P, hP⟩ := terminal_exists_mu_sylow D e
  obtain ⟨hK, hKN⟩ := terminalJoin_card_and_normalizes D e hmu hlam htau hpilam hxi P hP
  have hDK : ambientD D e ≤ terminalJoin D e P := le_sup_left
  have hsize := terminal_lambda_orbit_card D e (terminalJoin D e P) hDK hK hKN
    hmu hlam htau hpilam hxi
  exact terminal_contradiction_of_normalizes_of_twelve D e (terminalJoin D e P)
    hDK hK hKN hmu hlam hsize

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
