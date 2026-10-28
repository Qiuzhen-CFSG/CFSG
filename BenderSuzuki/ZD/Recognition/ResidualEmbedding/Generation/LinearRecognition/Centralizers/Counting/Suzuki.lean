module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.FixedPoints
public import Theory.SpecificGroups.Suzuki.LinearSeparation

/-!
# Specializing the residual centralizer analysis to an actual Suzuki model

An actual Suzuki isomorphism excludes every PSL₂ alternative by divisibility
of the group order by three. Thus the local Lemmas 12.3--12.4 already imply
centralization and centralizer-closure collapse in the Suzuki case, before
shearing or ambient counting. The concrete Suzuki Borel identifies the
distinguished subgroup order with the field order of the supplied model.
Fusion and the local factorization identify all fixed cosets with the local
Suzuki orbit; orbit-stabilizer gives its size without ambient counting.

The final theorem specializes the uniform counting alternatives using this
identification. Its counting-data hypothesis remains explicit: it is the
output of the separate Lemmas 12.7--12.11 argument, not a proof of those
lemmas. No disjointness or parameter-matching premise is assumed.

Source: `refs/KGroup/GLS4/Chapter2.tex`, Lemmas 12.3--12.4 and 12.10.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
open _root_.BenderSuzuki.MatrixGroups
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- In the actual Suzuki case, the local recognition alternatives themselves
give centralization and collapse for every involution of the pair stabilizer. -/
public theorem proper_residualGenerated_suzuki_centralizers_of_local
    {z t : G} (hlocal : ResidualCentralizerLocalData Z M z t)
    {m : ℕ} (hm : 1 ≤ m)
    (e : residualGenerated M z t ≃* SuzukiMatrixGroup m) :
    ∀ v ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution v →
      v ∈ centralizer (residualGenerated M z t : Set G) ∧
        centralizerClosure Z v = residualGenerated M z t := by
  have hsep (n : ℕ) : ¬ Nonempty (residualGenerated M z t ≃* PSL2BinaryMatrixGroup n) := by
    rintro ⟨f⟩
    exact not_nonempty_psl2_char_two_equiv_suzuki (BinaryGaloisField n)
      (by omega : 0 < m) ⟨f.symm.trans e⟩
  intro v hvD hv
  have hc : v ∈ centralizer (residualGenerated M z t : Set G) := by
    rcases hlocal.involution_action v hvD hv with hc | ⟨k, _, _, hk, _⟩
    · exact hc
    · exact (hsep (2 * k) hk).elim
  refine ⟨hc, ?_⟩
  rcases hlocal.centralizing_extension v hc hv.ne_one with he | ⟨n, _, _, hn, _⟩
  · exact he
  · exact (hsep n hn).elim

/-- The local residual orbit has the degree of the actual Suzuki ovoid.
This calculation uses only the marked Borel and the concrete group order. -/
public theorem proper_residualGenerated_suzuki_baseOrbit_card
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {m : ℕ} (hm : 1 ≤ m)
    (e : residualGenerated M z t ≃* SuzukiMatrixGroup m) :
    Nat.card (MulAction.orbit (residualGenerated M z t)
      (QuotientGroup.mk 1 : G ⧸ M)) = (2 ^ (2 * m + 1)) ^ 2 + 1 := by
  let L := residualGenerated M z t
  let alpha : G ⧸ M := QuotientGroup.mk 1
  have hstab : MulAction.stabilizer L alpha = M.comap L.subtype := by
    ext l
    change (l : G) ∈ MulAction.stabilizer G (QuotientGroup.mk 1 : G ⧸ M) ↔ (l : G) ∈ M
    rw [baseCoset_stabilizer]
  obtain ⟨f, hf⟩ := residualGenerated_suzuki_borel_marking h r hz hzM ht htM hL
    (by omega : 0 < m) e
  have hf' : (SuzukiBorelSubgroup m).map f.toMonoidHom = M.comap L.subtype := by
    apply map_injective L.subtype_injective
    rw [map_map, hf]
    ext x
    constructor
    · rintro ⟨hxM, hxL⟩
      exact ⟨⟨x, hxL⟩, hxM, rfl⟩
    · rintro ⟨x, hxM, rfl⟩
      exact ⟨hxM, x.property⟩
  have hcard : Nat.card (MulAction.stabilizer L alpha) =
      (2 ^ (2 * m + 1)) ^ 2 * (2 ^ (2 * m + 1) - 1) := by
    rw [hstab, ← hf', card_map_of_injective f.injective,
      suzukiBorelSubgroup_card m (by omega)]
  have hc := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup L alpha)
  rw [Nat.card_prod, hcard, Nat.card_congr e.toEquiv,
    suzukiMatrixGroup_card m (by omega)] at hc
  apply Nat.mul_right_cancel (show 0 < (2 ^ (2 * m + 1)) ^ 2 *
    (2 ^ (2 * m + 1) - 1) from hcard ▸ Nat.card_pos)
  simpa only [Nat.mul_assoc] using hc

/-- Every involution of the pair stabilizer has exactly `q²+1` fixed cosets
in the Suzuki case. No ambient degree or counting-data premise is used. -/
public theorem proper_residualGenerated_suzuki_fixed_counts_of_local
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (hlocal : ResidualCentralizerLocalData Z M z t)
    {m : ℕ} (hm : 1 ≤ m)
    (e : residualGenerated M z t ≃* SuzukiMatrixGroup m) :
    ∀ v ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution v →
      Nat.card {beta : G ⧸ M // v • beta = beta} = (2 ^ (2 * m + 1)) ^ 2 + 1 := by
  intro v hvD hv
  have horbit := pair_involution_fixedPoints_eq_centralizerClosure_orbit r hlocal hvD hv
  rw [(proper_residualGenerated_suzuki_centralizers_of_local hlocal hm e v hvD hv).2]
    at horbit
  calc
    _ = Nat.card (MulAction.orbit (residualGenerated M z t)
        (QuotientGroup.mk 1 : G ⧸ M)) := Nat.card_congr (Equiv.setCongr horbit)
    _ = _ := proper_residualGenerated_suzuki_baseOrbit_card h r hz hzM ht htM hL hm e

/-- The numerical Suzuki specialization, with its exponent recovered from
the actual model. The general counting-data producer is still required. -/
public theorem ResidualCentralizerCountingData.suzuki_counts
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (hcount : ResidualCentralizerCountingData Z M z t)
    {m : ℕ} (hm : 1 ≤ m)
    (e : residualGenerated M z t ≃* SuzukiMatrixGroup m) :
    let q := 2 ^ (2 * m + 1)
    Nat.card (G ⧸ M) = (q ^ 2 + 1) * (q ^ 2 * (q - 1) + 1) ∧
      ∀ v ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution v →
        Nat.card {beta : G ⧸ M // v • beta = beta} = q ^ 2 + 1 := by
  have hAL := proper_residualGenerated_contains_distinguishedClosure
    h r ha hz hzM ht htM hL heven
  have hA := (residualGenerated_suzuki_distinguishedClosure h.disconnected r
    hz hzM ht htM hL hAL (by omega : 0 < m) e).2
  obtain ⟨n, _, hn, hcases⟩ := hcount.cases
  have hn' : n = 2 * m + 1 := Nat.pow_right_injective (by decide : 2 ≤ 2) (hn.symm.trans hA)
  subst n
  have hsep : ¬ Nonempty (residualGenerated M z t ≃* PSL2BinaryMatrixGroup (2 * m + 1)) := by
    rintro ⟨f⟩
    exact not_nonempty_psl2_char_two_equiv_suzuki (BinaryGaloisField (2 * m + 1))
      (by omega : 0 < m) ⟨f.symm.trans e⟩
  rcases hcases with hlinear | hsuzuki | hunitary
  · exact (hsep hlinear.1).elim
  · obtain ⟨_, _, _, _, hdegree, hfixed⟩ := hsuzuki
    exact ⟨hdegree, fun v hvD hv => (hfixed v hvD hv).2⟩
  · exact (hsep hunitary.1).elim

end BenderSuzuki.ZD
