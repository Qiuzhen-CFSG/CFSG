module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.KernelOrders.Candidates
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.KernelOrbits
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.AdequateLocal.Marking
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.Max1RelativeRigidity.PairOrbit

/-!
# The small kernel closure contains no 2B involution

The checked two local kernel orbits and their distinct ambient conjugacy
classes imply that fusion to the 2B seed inside the kernel is local fusion.
The full seed centralizer lies in max1, so every ambient transporter of that
seed into the kernel lies in max1. This extends the argument in
`Mathieu.Normalizer.ActionRealization` from kernel normalizers to transporters.

Consequently the normalizer of any kernel subgroup containing a 2B element
lies in max1. Under the exact maximal-normalizer assumption, the subgroup
would be normal in max1. A nontrivial normal subgroup of its kernel has at
least 1771 elements by the checked pair orbit. A binary elementary subgroup
of order below 2048 has at most 1024 elements, giving the contradiction.

Source: Aschbacher--Smith A.3.12 and its sporadic Sylow-overgroup argument,
printed pp.47--48; GLS3 Table 5.3i for the two involution centralizers. All
fusion and centralizer inputs concern the literal ATLAS matrix carrier.
No ambient simplicity or maximal-subgroup classification is used.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.KernelOrders
open Janko4 Janko4.Cardinality Janko4.LocalStructure
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel localKernelSeed
local notation "M" => max1Subgroup matrixA_mul_self matrixB_pow_four
local notation "K" => localKernel matrixA_mul_self matrixB_pow_four

private theorem classSeed_ne_one : classSeed ≠ 1 := by
  intro h
  have ho := InvolutionCentralizers.Second.seed_order
  change orderOf classSeed = 2 at ho
  rw [h, orderOf_one] at ho
  omega

/-- Ambient fusion to the seed inside the kernel is already fusion inside max1. -/
theorem kernel_seed_fusion (z : M) (hz : z ∈ K)
    (hc : IsConj (z : Model) classSeed) :
    ∃ m : M, localKernelSeed matrixA_mul_self matrixB_pow_four = m * z * m⁻¹ := by
  have hne : z ≠ 1 := by
    intro h
    obtain ⟨g, hg⟩ := isConj_iff.mp hc
    rw [h, Subgroup.coe_one, mul_one, mul_inv_cancel] at hg
    exact classSeed_ne_one hg.symm
  obtain ⟨m, hm | hm⟩ := Simplicity.Max1Fusion.kernel_nonidentity_orbits
    matrixA_mul_self matrixB_pow_four z hz hne
  · exact ⟨m, hm⟩
  · have hp : IsConj (z : Model)
        (Simplicity.Max1Fusion.kernelPair matrixA_mul_self matrixB_pow_four : Model) :=
      isConj_iff.mpr ⟨(m : Model), (congrArg (M).subtype hm).symm⟩
    exact (AdequateLocal.seed_not_isConj_pair (hc.symm.trans hp)).elim

/-- A transporter sending the literal 2B seed into the kernel belongs to max1. -/
theorem seed_transporter_mem_max1 (g : Model)
    (hg : g * classSeed * g⁻¹ ∈ orderSpectrumKernel) : g ∈ M := by
  obtain ⟨z, hz, hzu⟩ := hg
  have hc : IsConj (z : Model) classSeed :=
    (isConj_iff.mpr ⟨g, hzu.symm⟩).symm
  obtain ⟨m, hm⟩ := kernel_seed_fusion z hz hc
  have he := congrArg (M).subtype hm
  change classSeed = (m : Model) * (z : Model) * (m : Model)⁻¹ at he
  change (z : Model) = g * classSeed * g⁻¹ at hzu
  rw [hzu] at he
  have hc : (m : Model) * g ∈ InvolutionCentralizers.Second.ambientCentralizer := by
    apply mem_centralizer_singleton_iff.mpr
    have he' : classSeed = ((m : Model) * g) * classSeed * ((m : Model) * g)⁻¹ := by
      simpa only [mul_inv_rev, mul_assoc] using he
    exact mul_inv_eq_iff_eq_mul.mp he'.symm
  have hmg := InvolutionCentralizers.Second.ambient_le_max1 hc
  have hh := (M).mul_mem ((M).inv_mem m.property) hmg
  simpa only [inv_mul_cancel_left] using hh

/-- A kernel subgroup containing a 2B element has its full ambient normalizer in max1. -/
theorem normalizer_le_max1_of_seed_conjugate (A : Subgroup Model)
    (hAK : A ≤ orderSpectrumKernel) (u : Model) (hu : u ∈ A)
    (hc : IsConj u classSeed) : normalizer (A : Set Model) ≤ M := by
  obtain ⟨z, hz, rfl⟩ := hAK hu
  obtain ⟨m, hm⟩ := kernel_seed_fusion z hz hc
  have he := congrArg (M).subtype hm
  change classSeed = (m : Model) * (z : Model) * (m : Model)⁻¹ at he
  intro g hg
  have hgm : g * (m : Model)⁻¹ ∈ M := by
    apply seed_transporter_mem_max1
    rw [he]
    have hzA := hAK ((mem_normalizer_iff.mp hg (z : Model)).mp hu)
    simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left] using hzA
  have hh := (M).mul_mem hgm m.property
  simpa only [inv_mul_cancel_right] using hh

/-- Max1 is proper, witnessed by the existing element of order 37. -/
theorem max1_ne_top : M ≠ (⊤ : Subgroup Model) := by
  intro ht
  have hab : Janko4.a * Janko4.b ∈ M := ht ▸ mem_top _
  have hd := (M).orderOf_dvd_natCard hab
  rw [Janko4.orderOf_a_mul_b, max1Subgroup_card] at hd
  norm_num at hd

private theorem normal_kernel_card_lower (V : Subgroup M) [V.Normal]
    (hVK : V ≤ K) (hne : V ≠ ⊥) : 1771 ≤ Nat.card V := by
  obtain ⟨z, hz⟩ := ne_bot_iff_exists_ne_one.mp hne
  have hz' : (z : M) ≠ 1 := fun he => hz (Subtype.ext he)
  obtain ⟨g, hg | hg⟩ := Simplicity.Max1Fusion.kernel_nonidentity_orbits
    matrixA_mul_self matrixB_pow_four z (hVK z.property) hz'
  · have hs : localKernelSeed matrixA_mul_self matrixB_pow_four ∈ V := by
      rw [hg]
      exact Normal.conj_mem inferInstance (z : M) z.property g
    have hKV : K ≤ V := by
      unfold localKernel
      exact normalClosure_le_normal (Set.singleton_subset_iff.mpr hs)
    have hh := card_le_of_le hKV
    rw [localKernel_card] at hh
    omega
  · have hs : Max1RelativeRigidity.v ∈ V := by
      rw [show Max1RelativeRigidity.v = g * z * g⁻¹ from hg]
      exact Normal.conj_mem inferInstance (z : M) z.property g
    have hsub : MulAction.orbit (ConjAct Max1RelativeRigidity.M)
        Max1RelativeRigidity.v ⊆ (V : Set Max1RelativeRigidity.M) := by
      rintro w ⟨a, rfl⟩
      exact Normal.conj_mem inferInstance _ hs a.ofConjAct
    have hh := Nat.card_le_card_of_injective _ (Set.inclusion_injective hsub)
    change Nat.card (MulAction.orbit (ConjAct Max1RelativeRigidity.M)
      Max1RelativeRigidity.v) ≤ Nat.card V at hh
    rwa [Max1RelativeRigidity.pair_orbit_card] at hh

/-- A nonzero small elementary kernel subgroup cannot be normal in all of max1. -/
theorem small_kernel_not_normalized_by_max1 (A : Subgroup Model)
    (hAK : A ≤ orderSpectrumKernel) (hne : A ≠ ⊥)
    (helem : IsElementaryAbelian 2 A) (hsmall : Nat.card A < 2048) :
    ¬ M ≤ normalizer (A : Set Model) := by
  intro hM
  have hAM : A ≤ M := hAK.trans (map_subtype_le _)
  let V := A.subgroupOf M
  have hVnormal : V.Normal := (normal_subgroupOf_iff_le_normalizer hAM).mpr hM
  let := hVnormal
  have hVK : V ≤ K := by
    intro x hx
    obtain ⟨y, hy, he⟩ := hAK hx
    exact ((M).subtype_injective he) ▸ hy
  have hcard : Nat.card V = Nat.card A :=
    Nat.card_congr (subgroupOfEquivOfLe hAM).toEquiv
  have hVne : V ≠ ⊥ := by
    intro h
    apply hne
    rw [← map_subgroupOf_eq_of_le hAM]
    change V.map (M).subtype = ⊥
    rw [h, Subgroup.map_bot]
  have hlower := normal_kernel_card_lower V hVK hVne
  rw [hcard] at hlower
  let := helem
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  have hlt : 2 ^ n < 2 ^ 11 := hn ▸ hsmall
  have hnlt : n < 11 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hlt
  have hle : 2 ^ n ≤ 2 ^ 10 := Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-- The exact small-closure hypotheses exclude every 2B element of the kernel. -/
theorem fixedSylowClosure_no_seed_conjugate (A : Subgroup Model)
    (hA : FixedSylowClosure A) (hAK : A ≤ orderSpectrumKernel)
    (hsmall : Nat.card A < 2048) : ∀ u ∈ A, ¬ IsConj u classSeed := by
  intro u hu hc
  have hNM := normalizer_le_max1_of_seed_conjugate A hAK u hu hc
  have he := (hA.maximal_normalizer.le_iff_eq max1_ne_top).mp hNM
  exact small_kernel_not_normalized_by_max1 A hAK hA.nontrivial hA.elementary hsmall he.le

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.KernelOrders
