module

public import ABG.ChapterII.Section1.CyclicFocalQuotient
public import ABG.ChapterII.Section1.FusionPatterns
public import GorensteinWalter.GWLemma21
public import BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# The normal subgroup associated with a cyclic focal quotient

For a finite group with cyclic Sylow-two focal quotient, the focal transfer
kernel K has the prescribed index and Sylow intersection and has no normal
subgroup of index two. The theorem also provides an actual Sylow subgroup
of K isomorphic to the focal subgroup. These are the normal-subgroup clauses
in the Q and D cases of ABG Chapter II Section 1 Proposition 2, article p.13.

Surjectivity of transfer on the Sylow subgroup gives the index, while the
focal theorem gives the intersection. If L had index two in K, its ambient
image H would have twice K's index. A uniform two-power of every group
element lies in H, hence in its normal core. The quotient by that core is
a two-group and is cyclic by the cyclic focal quotient theorem. Therefore
H contains the ambient commutator subgroup and the focal subgroup. This
forces H and K to have the same Sylow intersection and index, a contradiction.
Finally restrict the original Sylow subgroup to the normal kernel and
transport its actual subtype image to the focal subgroup.
-/

namespace ABG

private theorem kernel_no_normal_index_two
    {G : Type*} [Group G] [Finite G] (P : Sylow 2 G)
    [IsCyclic (P ⧸ (P : Subgroup G).focalSubgroupOf)]
    (K : Subgroup G) [K.Normal] (hK : IsPGroup 2 (G ⧸ K))
    (hKP : K ⊓ (P : Subgroup G) = (P : Subgroup G).focalSubgroup) :
    ∀ L : Subgroup K, L.Normal → L.index ≠ 2 := by
  intro L hL hLi
  let := hL
  let H := L.map K.subtype
  obtain ⟨n, hn⟩ := hK.exists_card_eq
  have hKi : K.index = 2 ^ n := hn
  have hHi : H.index = 2 * K.index := by rw [Subgroup.index_map_subtype, hLi]
  have hpow (x : G) : x ^ (2 ^ (n+1)) ∈ H := by
    let y : K := ⟨x ^ (2 ^ n), by rw [← hKi]; exact K.pow_index_mem x⟩
    have hy := L.sq_mem_of_index_two hLi y
    have hh := Subgroup.mem_map_of_mem K.subtype hy
    change (x ^ (2 ^ n)) ^ 2 ∈ H at hh
    rw [← pow_mul] at hh
    simpa only [show n+1 = Nat.succ n from rfl, pow_succ (2 : ℕ) n] using hh
  let N := H.normalCore
  have hNpow (x : G) : x ^ (2 ^ (n+1)) ∈ N := by
    intro g
    change (MulAut.conj g) (x ^ (2 ^ (n+1))) ∈ H
    rw [map_pow]
    exact hpow _
  have hQ : IsPGroup 2 (G ⧸ N) := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
    refine ⟨n+1, ?_⟩
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (hNpow g)
  let : IsCyclic (G ⧸ N) := isCyclic_quotient_of_cyclic_focal_quotient P N hQ
  have hcomm : commutator G ≤ N :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  have hcommH : commutator G ≤ H := hcomm.trans H.normalCore_le
  have hHN : H.Normal := by
    constructor
    intro x hx g
    have hd : g * x * g⁻¹ * x⁻¹ ∈ H := by
      simpa only [commutatorElement_def] using
        hcommH (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top x))
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using H.mul_mem hd hx
  let := hHN
  have hHQ : IsPGroup 2 (G ⧸ H) := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H x
    refine ⟨n+1, ?_⟩
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (hpow g)
  have hHP : H ⊓ (P : Subgroup G) = K ⊓ (P : Subgroup G) := by
    apply le_antisymm (inf_le_inf_right _ (Subgroup.map_subtype_le L))
    rw [hKP]
    exact le_inf ((P : Subgroup G).focalSubgroup_le_commutator.trans hcommH)
      (P : Subgroup G).focalSubgroup_le
  have heq : H.index = K.index := by
    rw [← GorensteinWalter.normal_relIndex_sylow_eq_index_of_quotient_isPGroup P H hHN hHQ,
      ← GorensteinWalter.normal_relIndex_sylow_eq_index_of_quotient_isPGroup P K inferInstance hK,
      ← Subgroup.inf_relIndex_right H (P : Subgroup G),
      ← Subgroup.inf_relIndex_right K (P : Subgroup G), hHP]
  have hpos : 0 < K.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  omega

/-- The cyclic focal quotient supplies the normal subgroup and its actual Sylow model. -/
public theorem exists_normal_sylow_of_cyclic_focal_quotient
    {G : Type*} [Group G] [Finite G] (P : Sylow 2 G)
    [IsCyclic (P ⧸ (P : Subgroup G).focalSubgroupOf)] :
    ∃ K : Subgroup G, K.Normal ∧ K.index = (P : Subgroup G).focalSubgroupOf.index ∧
      HasNoNormalIndexTwoSubgroup K ∧
      K ⊓ (P : Subgroup G) = (P : Subgroup G).focalSubgroup ∧
      ∃ R : Sylow 2 K,
        (R : Subgroup K).map K.subtype = (P : Subgroup G).focalSubgroup ∧
        Nonempty (R ≃* (P : Subgroup G).focalSubgroupOf) := by
  let f := (P : Subgroup G).transferFocal
  let K := f.ker
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨y, hy⟩ := BenderSuzuki.External.hkt_transferFocal_restrict_surjective P x
    exact ⟨y, hy⟩
  have hKi : K.index = (P : Subgroup G).focalSubgroupOf.index := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top,
      Subgroup.index_eq_card]
  have hKP : K ⊓ (P : Subgroup G) = (P : Subgroup G).focalSubgroup :=
    Subgroup.ker_transferFocal_inf_eq_focalSubgroup P
  have hK : IsPGroup 2 (G ⧸ K) :=
    ((P.isPGroup'.to_quotient _).to_subgroup f.range).of_equiv
      (QuotientGroup.quotientKerEquivRange f).symm
  obtain ⟨R, hR⟩ := P.exists_subgroupOf_eq_of_normal K
  have hmap : (R : Subgroup K).map K.subtype = (P : Subgroup G).focalSubgroup := by
    rw [hR, Subgroup.subgroupOf_map_subtype, inf_comm, hKP]
  refine ⟨K, inferInstance, hKi, kernel_no_normal_index_two P K hK hKP, hKP, R, hmap, ?_⟩
  refine ⟨((R : Subgroup K).equivMapOfInjective K.subtype K.subtype_injective).trans ?_⟩
  exact (MulEquiv.subgroupCongr (hmap.trans (Subgroup.map_focalSubgroupOf _).symm)).trans
    (((P : Subgroup G).focalSubgroupOf).equivMapOfInjective (P : Subgroup G).subtype
      (P : Subgroup G).subtype_injective).symm

end ABG
