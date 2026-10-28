module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.PairedFields
public import Theory.GroupTheory.PGroup.InvolutionFour

/-!
# A marked four containing the maximal-trace involution

An elementary four can be conjugated into any Sylow two-subgroup; the
central-involution argument then places every involution of that Sylow in
a four. Apply this to the selected maximal-trace involution in D. The
simultaneous marking theorem chooses z and a D-conjugate of t centralized
by the entire four. That conjugation preserves D, and hence preserves the
maximal-trace property needed by Lemma 16.4(a).

Source: GLS IV, Chapter 2, Proposition 16.5, its first sentence.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

private theorem rank_two_four_containing
    (hrank : TwoRankAtLeastTwo G) {u : G} (hu : PFAppendixIII.IsInvolution u) :
    ∃ W : Subgroup G, IsElementaryAbelian 2 W ∧ Nat.card W = 4 ∧ u ∈ W := by
  obtain ⟨E,hE,hE2⟩ := hrank
  let : IsElementaryAbelian 2 E := {
    toIsMulCommutative := isMulCommutative_of_forall_sq_one hE2
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hE2 }
  obtain ⟨T,hT⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_le_sylow
  obtain ⟨S,hS⟩ := (isPGroup_zpowers_of_involution hu).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G T S
  let A := E.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hAS : A ≤ S := by
    rintro x ⟨e,he,rfl⟩
    rw [← hg,Sylow.coe_subgroup_smul]
    exact Set.mem_smul_set.mpr ⟨e,hT he,rfl⟩
  let Aₛ := A.subgroupOf S
  let : IsElementaryAbelian 2 Aₛ := IsElementaryAbelian.subgroupOf hAS
  have hAₛ : Nat.card Aₛ = 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAS).toEquiv,
      card_map_of_injective (MulAut.conj g).injective]
    exact hE
  have huS : u ∈ S := hS (mem_zpowers u)
  let uS : S := ⟨u,huS⟩
  have huord : orderOf uS = 2 := by
    rw [← Subgroup.orderOf_coe uS]
    exact orderOf_eq_prime hu.sq_eq_one hu.ne_one
  obtain ⟨V,hVe,hV,huV⟩ := S.isPGroup'.exists_elementary_four_mem_of_four_le
    Aₛ hAₛ.ge uS huord
  let := hVe
  refine ⟨V.map (S : Subgroup G).subtype,IsElementaryAbelian.map _,?_,?_⟩
  · rw [card_map_of_injective (S : Subgroup G).subtype_injective]
    exact hV
  · exact mem_map_of_mem (S : Subgroup G).subtype huV

/-- The maximal involution can be placed in a four with simultaneous marks;
the swapping mark changes by an element of D and leaves D unchanged. -/
public theorem source16_marked_four_of_rank_two
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {t u : G} (ht : t ∈ Z) (htM : t ∉ M)
    (hu : PFAppendixIII.IsInvolution u) (huD : u ∈ residualPairStabilizer M t)
    (hrank : TwoRankAtLeastTwo (residualPairStabilizer M t)) :
    ∃ z t₁ : G, z ∈ Z ∧ z ∈ M ∧ t₁ ∈ Z ∧ t₁ ∉ M ∧
      residualPairStabilizer M t₁ = residualPairStabilizer M t ∧
      ∃ W : Subgroup G, IsElementaryAbelian 2 W ∧ Nat.card W = 4 ∧
        W ≤ residualPairStabilizer M t₁ ∧ W ≤ centralizer ({z} : Set G) ∧
        W ≤ centralizer ({t₁} : Set G) ∧ u ∈ W := by
  let D := residualPairStabilizer M t
  obtain ⟨V,hVe,hV,huV⟩ := rank_two_four_containing hrank (IsInvolution.subtype hu huD)
  let := hVe
  let W := V.map D.subtype
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hW : Nat.card W = 4 := by rw [card_map_of_injective D.subtype_injective]; exact hV
  have hWD : W ≤ D := map_subtype_le V
  obtain ⟨z,hz,hzM,d,hdt,hdtM,hWC⟩ := residualTwoSubgroup_exists_marked_pair h r ht htM
    W (IsElementaryAbelian.isPGroup 2 W) hWD
  have hpair := residualPairStabilizer_conj_swapping_eq d
  exact ⟨z,MulAut.conj (d : G) t,hz,hzM,hdt,hdtM,hpair,W,inferInstance,hW,
    hpair.symm ▸ hWD,hWC.trans inf_le_left,hWC.trans inf_le_right,mem_map_of_mem D.subtype huV⟩

/-- The original residual rank-two assumption supplies all four and marking
inputs to the paired-model producer; no selected four is assumed. -/
public theorem source16_exists_maximal_marked_four
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M) (ha : ResidualAction Z M)
    (hn : ¬ IsStronglyEmbedded M) {t : G} (ht : t ∈ Z) (htM : t ∉ M)
    (hrank : TwoRankAtLeastTwo (residualPairStabilizer M t)) :
    ∃ u z t₁ : G, PFAppendixIII.IsInvolution u ∧ z ∈ Z ∧ z ∈ M ∧ t₁ ∈ Z ∧ t₁ ∉ M ∧
      residualPairStabilizer M t₁ = residualPairStabilizer M t ∧
      (∀ v ∈ residualPairStabilizer M t₁, PFAppendixIII.IsInvolution v →
        (residualCentralizerTrace Z M v).ncard ≤ (residualCentralizerTrace Z M u).ncard) ∧
      ∃ W : Subgroup G, IsElementaryAbelian 2 W ∧ Nat.card W = 4 ∧
        W ≤ residualPairStabilizer M t₁ ∧ W ≤ centralizer ({z} : Set G) ∧
        W ≤ centralizer ({t₁} : Set G) ∧ u ∈ W := by
  obtain ⟨u,huD,hu,_,hmax⟩ := exists_residualCentralizerTrace_maximal h ha hn htM
  obtain ⟨z,t₁,hz,hzM,ht₁,ht₁M,hpair,hW⟩ := source16_marked_four_of_rank_two
    h r ht htM hu huD hrank
  exact ⟨u,z,t₁,hu,hz,hzM,ht₁,ht₁M,hpair,hpair.symm ▸ hmax,hW⟩

end BenderSuzuki.ZD
