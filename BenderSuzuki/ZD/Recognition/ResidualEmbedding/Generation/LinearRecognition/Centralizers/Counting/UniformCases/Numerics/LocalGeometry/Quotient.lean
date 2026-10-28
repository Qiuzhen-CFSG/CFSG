module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.UniformCases.Numerics.Inputs
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.FixedPoints
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.UniformCases.Numerics.LocalGeometry.BorelDegree

/-!
# The marked centralizer quotient and its literal fixed cosets

The odd core is central by Lemma 12.4(c), so local strong embedding puts it
inside the base stabilizer. Strong embedding descends to the actual quotient;
Theorem SE identifies the image of that stabilizer as its Borel. Consequently
the quotient preserves its index. Fusion and Lemma 12.4(e) identify this
index with the number of fixed cosets in the original ambient action.

Source: GLS4, Chapter 2, Corollary 7.13 and Lemmas 12.4(c,e), 12.8.
-/

noncomputable section
namespace BenderSuzuki.ZD.LocalGeometry
open Subgroup Theory.GroupTheory PFAppendixIII
universe u
variable {G : Type u} [Group G] [Finite G]

/-- In a simple local group, strong embedding marks the actual Borel. -/
public theorem borel_of_stronglyEmbedded_simple
    {B : Subgroup G} (hs : IsStronglyEmbedded B) (hsi : IsSimpleGroup G) :
    IsBorelSubgroup B := by
  have hgen := hs.involutionCore_eq_top_of_isSimple hsi
  have hr := simpleStronglyEmbeddedRankTwo B hsi hs
  let e : G ≃* involutionCore G :=
    Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hgen).symm
  have hr' := hr.map_of_injective e.toMonoidHom e.injective
  exact (recognition_borel_of_simple_theoremSEBenderConclusion B hs hsi
    ((theorem_SE B hs).resolve_left (not_not.mpr hr'))).2

variable {Z : Set G} {M : Subgroup G}

/-- Orbit-stabilizer for the literal ambient fixed-coset set. -/
public theorem fixed_cosets_card_eq_local_index
    (r : SimpleReduction Z M) {z t v : G}
    (hlocal : ResidualCentralizerLocalData Z M z t)
    (hvD : v ∈ residualPairStabilizer M t) (hv : PFAppendixIII.IsInvolution v) :
    Nat.card {beta : G ⧸ M // v • beta = beta} =
      (M.comap (centralizerClosure Z v).subtype).index := by
  let F := centralizerClosure Z v
  let a : G ⧸ M := QuotientGroup.mk 1
  have hstab : MulAction.stabilizer F a = M.comap F.subtype := by
    ext x
    change (x : G) ∈ MulAction.stabilizer G (QuotientGroup.mk 1 : G ⧸ M) ↔ (x : G) ∈ M
    rw [baseCoset_stabilizer]
  calc
    _ = Nat.card (MulAction.orbit F a) := Nat.card_congr (Equiv.setCongr
      (pair_involution_fixedPoints_eq_centralizerClosure_orbit r hlocal hvD hv))
    _ = (MulAction.stabilizer F a).index :=
      Nat.card_congr (MulAction.orbitEquivQuotientStabilizer F a)
    _ = _ := congrArg Subgroup.index hstab

/-- The odd-core projection preserves the index of the actual marked Borel. -/
public theorem centralizer_quotient_borel
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M) {z t v : G}
    (htM : t ∉ M) (hlocal : ResidualCentralizerLocalData Z M z t)
    (hvD : v ∈ residualPairStabilizer M t) (hv : PFAppendixIII.IsInvolution v) :
    let F := centralizerClosure Z v
    let N := pPrimeCore 2 F
    let B := M.comap F.subtype
    N ≤ B ∧ IsBorelSubgroup (B.map (QuotientGroup.mk' N)) ∧
      Nat.card {beta : G ⧸ M // v • beta = beta} =
        (B.map (QuotientGroup.mk' N)).index := by
  let F := centralizerClosure Z v
  let N := pPrimeCore 2 F
  let B := M.comap F.subtype
  have hs : IsStronglyEmbedded B :=
    (pair_involution_centralizerClosure_local h r htM hvD hv).2.2
  obtain ⟨hc, k, hk, _, hm⟩ := hlocal.quotient_models v hvD hv
  have hNB : N ≤ B := by
    obtain ⟨x, hxB, hx⟩ := hs.exists_involution
    intro y hy
    have hyc : y ∈ center F := hc ▸ hy
    exact hs.centralizer_le hxB hx (mem_centralizer_singleton_iff.mpr
      (mem_center_iff.mp hyc x).symm)
  have hsQ := hs.map_quotient_of_odd_kernel hNB
    (Nat.coprime_two_left.mp (pPrimeCore_coprime_card (G := F) (p := 2)))
  refine ⟨hNB, borel_of_stronglyEmbedded_simple hsQ (hm.isSimple hk), ?_⟩
  rw [B.index_map_eq (QuotientGroup.mk'_surjective N)
    (by rwa [QuotientGroup.ker_mk'])]
  exact fixed_cosets_card_eq_local_index r hlocal hvD hv

/-- The local model supplies the fixed subgroup order and fixed-coset degree,
without assuming that the involution centralizes the residual group. -/
public theorem fixed_cosets_geometry_parameters
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M) {z t v : G}
    (htM : t ∉ M) (hlocal : ResidualCentralizerLocalData Z M z t)
    (hvD : v ∈ residualPairStabilizer M t) (hv : PFAppendixIII.IsInvolution v) :
    ∃ k i : ℕ, 2 ≤ k ∧ (i = 1 ∨ i = 2 ∨ i = 3) ∧ (i = 2 → Odd k) ∧
      Nat.card (closure (Z ∩ (M : Set G)) ⊓ centralizer ({v} : Set G) : Subgroup G) = 2 ^ k ∧
      Nat.card {beta : G ⧸ M // v • beta = beta} = (2 ^ k) ^ i + 1 := by
  obtain ⟨_, k, hk, hcard, hm⟩ := hlocal.quotient_models v hvD hv
  obtain ⟨_, hb, hind⟩ := centralizer_quotient_borel h r htM hlocal hvD hv
  obtain ⟨i, hi, ho, hc⟩ := bender_borel_index_atExponent hk hm hb
  exact ⟨k, i, hk, hi, ho, hcard, hind.trans hc⟩

end BenderSuzuki.ZD.LocalGeometry
