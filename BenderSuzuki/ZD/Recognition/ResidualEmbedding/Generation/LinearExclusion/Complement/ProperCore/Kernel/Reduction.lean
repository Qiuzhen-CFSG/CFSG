module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.Algebra
public import Theory.GroupTheory.NoninvolutionBase

/-!
# Algebraic reductions for the proper-core commutator kernel

Write `R = ⟨Jᴹ⟩`, `V = O₂(M)` and `K = D ∩ L`, all inside `M`.
Coprime action gives `R = [R,K] J`. The literal kernel `[R,K]` is normalized
by `R` and by `D`, but these facts alone do not prove normality in `M`.

The later reductions take an independently constructed abelian index-two
base `B` whose complement in `R` consists of involutions and whose intersection
with `J` is trivial. Its noninvolutions characterize `B`, proving normality.
The index-two section and coprime action then identify `B` with the actual
`linearCommutatorKernel`, rather than replacing that definition by a witness.
Nonsquareness in `R ∖ B` and the torus action on `V/R` imply that `V/B` is
abelian, yielding precisely the three kernel properties required by the
proper-core complement construction.

The local construction of `B` and the nonsquare/torus inputs remain explicit
source obligations. This module does not assert the complete Lemma 15.7.
Source: GLS, Volume 4, Chapter 2, end of Lemma 15.6 and first two paragraphs
of Lemma 15.7, `refs/KGroup/GLS4/Chapter2.tex`, lines 2703–2750.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory

private theorem linear_kernel_coprime
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (B : Subgroup M) (hB : B ≤ pCore 2 M) :
    Nat.Coprime
      (Nat.card ((residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M))
      (Nat.card B) := by
  have hK : Odd (Nat.card
      ((residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M)) := by
    have hc : Nat.card ((residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M) =
        Nat.card (residualPairStabilizer M t ⊓ residualGenerated M z t : Subgroup G) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans inf_le_left)).toEquiv
    rw [hc]
    exact pair_inf_proper_residualGenerated_odd h r hz hzM ht htM hL
  have hp : IsPGroup 2 B := (pCore_isPGroup (p := 2) (G := M)).of_injective
    (Subgroup.inclusion hB) (Subgroup.inclusion_injective hB)
  obtain ⟨m, hm⟩ := hp.exists_card_eq
  rw [hm]
  exact hK.coprime_two_right.pow_right m

/-- The source fixed-point equality restricts to the actual normal closure. -/
public theorem linearCentralizerClosure_inf_centralizer
    {G : Type*} [Group G] {M : Subgroup G} {z t : G} {n : ℕ}
    (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2)
    (hfixed : pCore 2 M ⊓
      centralizer (((residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M) : Set M) =
      (centralizer (residualGenerated M z t : Set G)).subgroupOf M) :
    linearCentralizerClosure M z t ⊓
      centralizer (((residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M) : Set M) =
      (centralizer (residualGenerated M z t : Set G)).subgroupOf M := by
  apply le_antisymm
  · exact (inf_le_inf_right _ (linearCentralizerClosure_le_twoCore hR)).trans hfixed.le
  · exact le_inf subset_normalClosure (hfixed.symm.le.trans inf_le_right)

/-- Coprime action gives `R = [R,K] J` for the literal commutator kernel.
This does not yet assert that the two factors intersect trivially. -/
public theorem linearCentralizerClosure_eq_kernel_sup_centralizer
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ}
    (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2)
    (hfixed : pCore 2 M ⊓
      centralizer (((residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M) : Set M) =
      (centralizer (residualGenerated M z t : Set G)).subgroupOf M) :
    linearCentralizerClosure M z t = linearCommutatorKernel M z t ⊔
      (centralizer (residualGenerated M z t : Set G)).subgroupOf M := by
  let R := linearCentralizerClosure M z t
  let K := (residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M
  let : R.Normal := Subgroup.normalClosure_normal
  have hp : IsPGroup 2 R := (pCore_isPGroup (p := 2) (G := M)).of_injective
    (Subgroup.inclusion (linearCentralizerClosure_le_twoCore hR))
    (Subgroup.inclusion_injective _)
  let : Group.IsNilpotent R := hp.isNilpotent
  have hd := Subgroup.eq_commutator_sup_centralizer_of_solvable_coprime R K
    (le_trans le_top le_normalizer_of_normal) inferInstance
    (linear_kernel_coprime h r hz hzM ht htM hL R (linearCentralizerClosure_le_twoCore hR))
  change R = ⁅R, K⁆ ⊔ _
  have hc : R ⊓ centralizer (K : Set M) =
      (centralizer (residualGenerated M z t : Set G)).subgroupOf M :=
    linearCentralizerClosure_inf_centralizer hR hfixed
  exact hd.trans (congrArg (fun C => ⁅R,K⁆ ⊔ C) hc)

/-- The actual kernel is normal in `R`; this is weaker than the required
normality in `M`. -/
public theorem linearCommutatorKernel_normal_in_closure
    {G : Type*} [Group G] {M : Subgroup G} {z t : G} :
    ((linearCommutatorKernel M z t).subgroupOf
      (linearCentralizerClosure M z t)).Normal := by
  exact normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_left _ _)

/-- The pair stabilizer normalizes the actual kernel once it normalizes `L`.
The remaining source normality argument concerns conjugation by `V`. -/
public theorem linear_pair_le_normalizer_commutatorKernel
    {G : Type*} [Group G] {M : Subgroup G} {z t : G}
    (hDN : residualPairStabilizer M t ≤ normalizer (residualGenerated M z t : Set G)) :
    (residualPairStabilizer M t).subgroupOf M ≤
      normalizer (linearCommutatorKernel M z t : Set M) := by
  let : (linearCentralizerClosure M z t).Normal := Subgroup.normalClosure_normal
  intro d hd
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [linearCommutatorKernel, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp
      (show d ∈ normalizer (linearCentralizerClosure M z t : Set M) from
        le_normalizer_of_normal (mem_top d)),
    mem_normalizer_iff_map_conj_eq.mp (linear_pair_le_normalizer_inter_of_normalizes hDN hd)]


/-- Identify an independently constructed normal base with the literal
kernel. Index two makes `[R,K] ≤ B`, while coprime action and `B ∩ J = 1`
give `B = [B,K]`. This lemma does not construct the source base. -/
public theorem linearCommutatorKernel_eq_of_normal_base
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ}
    (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2)
    (hfixed : pCore 2 M ⊓
      centralizer (((residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M) : Set M) =
      (centralizer (residualGenerated M z t : Set G)).subgroupOf M)
    (B : Subgroup M) [B.Normal]
    (hBR : B ≤ linearCentralizerClosure M z t)
    (hindex : B.relIndex (linearCentralizerClosure M z t) = 2)
    (hdis : Disjoint B ((centralizer (residualGenerated M z t : Set G)).subgroupOf M)) :
    linearCommutatorKernel M z t = B := by
  let R := linearCentralizerClosure M z t
  let K := (residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M
  let : R.Normal := Subgroup.normalClosure_normal
  have hBV := hBR.trans (linearCentralizerClosure_le_twoCore hR)
  have hp : IsPGroup 2 B := (pCore_isPGroup (p := 2) (G := M)).of_injective
    (Subgroup.inclusion hBV) (Subgroup.inclusion_injective hBV)
  let : Group.IsNilpotent B := hp.isNilpotent
  have hBC : B ⊓ centralizer (K : Set M) = ⊥ := by
    apply le_bot_iff.mp
    apply le_trans _ hdis.le_bot
    apply le_inf inf_le_left
    exact (inf_le_inf_right _ hBV).trans hfixed.le
  have hB := Subgroup.eq_commutator_sup_centralizer_of_solvable_coprime B K
    (le_trans le_top le_normalizer_of_normal) inferInstance
    (linear_kernel_coprime h r hz hzM ht htM hL B hBV)
  rw [hBC, sup_bot_eq] at hB
  apply le_antisymm
  · exact commutator_le_of_normalized_index_two R B K hBR hindex
      (le_trans le_top le_normalizer_of_normal) (le_trans le_top le_normalizer_of_normal)
  · exact hB.le.trans (commutator_mono hBR le_rfl)

/-- Algebraic assembly for the actual source kernel from a constructed
abelian base and square information. The noninvolutions characterize `B`
intrinsically, proving its normality in `M`; coprime action identifies it
with `[R,K]`. The source involution analysis must supply `B` and its profile,
and the nonsquare/torus argument must supply `hsq`. -/
public theorem linearCommutatorKernel_properties_of_square_profile
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ}
    (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2)
    (hfixed : pCore 2 M ⊓
      centralizer (((residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M) : Set M) =
      (centralizer (residualGenerated M z t : Set G)).subgroupOf M)
    (B : Subgroup M) (hBR : B ≤ linearCentralizerClosure M z t)
    (hindex : B.relIndex (linearCentralizerClosure M z t) = 2)
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, Commute x y)
    (hnon : ∃ b ∈ B, b ^ 2 ≠ 1)
    (hout : ∀ x ∈ linearCentralizerClosure M z t, x ∉ B → x ^ 2 = 1)
    (hdis : Disjoint B ((centralizer (residualGenerated M z t : Set G)).subgroupOf M))
    (hsq : ∀ v ∈ pCore 2 M, v ^ 2 ∈ B) :
    (linearCommutatorKernel M z t).Normal ∧
      ⁅pCore 2 M, pCore 2 M⁆ ≤ linearCommutatorKernel M z t ∧
      Disjoint (linearCommutatorKernel M z t)
        ((centralizer (residualGenerated M z t : Set G)).subgroupOf M) := by
  let : (linearCentralizerClosure M z t).Normal := Subgroup.normalClosure_normal
  let : B.Normal := normal_of_noninvolution_profile _ B hBR hcomm hnon hout
  rw [linearCommutatorKernel_eq_of_normal_base h r hz hzM ht htM hL hR hfixed
    B hBR hindex hdis]
  exact ⟨inferInstance, commutator_le_of_squares _ B hsq, hdis⟩


/-- The two remaining source branches suffice for the kernel contract.
The first constructs the abelian index-two base with its involution profile.
The second proves that no element of `R ∖ B` is a square in `V` and that the
literal torus is transitive on the nonidentity cosets of `R` in `V`.
Cauchy's theorem and the central section `R/B` then give all squares in `B`.
Neither source branch is asserted by this conditional assembly. -/
public theorem linearCommutatorKernel_properties_of_torus_and_nonsquares
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ}
    (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2)
    (hproper : linearCentralizerClosure M z t < pCore 2 M)
    (hfixed : pCore 2 M ⊓
      centralizer (((residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M) : Set M) =
      (centralizer (residualGenerated M z t : Set G)).subgroupOf M)
    (B : Subgroup M) (hBR : B ≤ linearCentralizerClosure M z t)
    (hindex : B.relIndex (linearCentralizerClosure M z t) = 2)
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, Commute x y)
    (hnon : ∃ b ∈ B, b ^ 2 ≠ 1)
    (hout : ∀ x ∈ linearCentralizerClosure M z t, x ∉ B → x ^ 2 = 1)
    (hdis : Disjoint B ((centralizer (residualGenerated M z t : Set G)).subgroupOf M))
    (hno : ∀ v ∈ pCore 2 M, v ^ 2 ∈ linearCentralizerClosure M z t → v ^ 2 ∈ B)
    (htrans : ∀ v ∈ pCore 2 M, v ∉ linearCentralizerClosure M z t →
      ∀ w ∈ pCore 2 M, w ∉ linearCentralizerClosure M z t →
      ∃ k ∈ (residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M,
        ∃ a ∈ linearCentralizerClosure M z t, w = k * v * k⁻¹ * a) :
    (linearCommutatorKernel M z t).Normal ∧
      ⁅pCore 2 M, pCore 2 M⁆ ≤ linearCommutatorKernel M z t ∧
      Disjoint (linearCommutatorKernel M z t)
        ((centralizer (residualGenerated M z t : Set G)).subgroupOf M) := by
  let : (linearCentralizerClosure M z t).Normal := Subgroup.normalClosure_normal
  let : B.Normal := normal_of_noninvolution_profile _ B hBR hcomm hnon hout
  apply linearCommutatorKernel_properties_of_square_profile h r hz hzM ht htM hL hR hfixed
    B hBR hindex hcomm hnon hout hdis
  exact squares_le_of_transitive_cosets_of_no_squares _ _ B _ pCore_isPGroup hproper
    hBR hindex hno htrans

end BenderSuzuki.ZD
