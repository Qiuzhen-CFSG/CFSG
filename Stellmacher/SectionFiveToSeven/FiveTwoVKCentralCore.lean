module

public import Stellmacher.SectionFiveToSeven.Defs
public import Theory.PGroupCore

/-!
# The central two-core commutator in Stellmacher (5.2)

Let `V` be a normal two-subgroup of the minimal bad subgroup `M`.  If
`B K≤M`, assertion (1) of Stellmacher (5.2) makes `V` normalize `K`.
Consequently `[V,K]≤V∩K`; this intersection is a normal two-subgroup of `K`
and hence lies in `O₂(K)`.  If `O₂(K)≤C_M(V)`, the commutator lies in the
ambient image of `Z(O₂(K))`.

This is the first implication in the proof of assertion (7) of Stellmacher
(5.2), Journal of Algebra 190 (1997), p. 29.  The following (3.5)
contradiction is kept separate.
-/

namespace Stellmacher.SectionsFiveToSeven

universe u

private theorem normal_twoSubgroup_le_twoCoreIn_vk
    {G : Type u} [Group G]
    (Q K : Subgroup G) (hQK : Q ≤ K) (hQp : IsPGroup 2 Q)
    (hQnormal : (Q.subgroupOf K).Normal) :
    Q ≤ twoCoreIn K := by
  have hQpK : IsPGroup 2 (Q.subgroupOf K) :=
    hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQK).symm
  have hle : Q.subgroupOf K ≤ pCore 2 K := le_sSup ⟨hQnormal, hQpK⟩
  calc
    Q = (Q.subgroupOf K).map K.subtype :=
      (Subgroup.map_subgroupOf_eq_of_le hQK).symm
    _ ≤ (pCore 2 K).map K.subtype := Subgroup.map_mono hle
    _ = twoCoreIn K := rfl

/-- Under assertion (1), if `O₂(K)` centralizes the normal two-subgroup `V`,
then `[V,K]` lies in `Z(O₂(K))`. -/
public theorem five_two_commutator_le_twoCore_center
    {G : Type u} [Group G] [Finite G]
    (B K M V C0 : Subgroup G)
    (hBKM : B ⊔ K ≤ M)
    (hVM : V ≤ M) (hVnormal : (V.subgroupOf M).Normal)
    (hVp : IsPGroup 2 V)
    (hC0 : C0 = Subgroup.centralizer (V : Set G))
    (hcoreC0 : twoCoreIn K ≤ C0)
    (hnorm : ∀ D : Subgroup G, IsPGroup 2 D →
      B ⊔ K ≤ Subgroup.normalizer (D : Set G) →
      D ≤ Subgroup.normalizer (K : Set G)) :
    ⁅V, K⁆ ≤ (Subgroup.center (twoCoreIn K)).map (twoCoreIn K).subtype := by
  have hMnormV : M ≤ Subgroup.normalizer (V : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVM).mp hVnormal
  have hVnormK : V ≤ Subgroup.normalizer (K : Set G) :=
    hnorm V hVp (hBKM.trans hMnormV)
  have hKnormV : K ≤ Subgroup.normalizer (V : Set G) :=
    le_sup_right.trans (hBKM.trans hMnormV)
  let Q : Subgroup G := V ⊓ K
  have hQK : Q ≤ K := inf_le_right
  have hQp : IsPGroup 2 Q := hVp.to_le inf_le_left
  have hQnormal : (Q.subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hQK]
    intro q k hq hk
    refine ⟨?_, K.mul_mem (K.mul_mem hk hq.2) (K.inv_mem hk)⟩
    exact (Subgroup.normal_subgroupOf_iff hVM).mp hVnormal
      q k hq.1 (le_sup_right.trans hBKM hk)
  have hQcore : Q ≤ twoCoreIn K :=
    normal_twoSubgroup_le_twoCoreIn_vk Q K hQK hQp hQnormal
  have hcommV : ⁅V, K⁆ ≤ V :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hKnormV
  have hcommK : ⁅V, K⁆ ≤ K :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp hVnormK
  have hcommQ : ⁅V, K⁆ ≤ Q := le_inf hcommV hcommK
  have hcoreCentralV : twoCoreIn K ≤ Subgroup.centralizer (V : Set G) := by
    simpa [hC0] using hcoreC0
  intro x hx
  have hxV : x ∈ V := hcommV hx
  have hxcore : x ∈ twoCoreIn K := hQcore (hcommQ hx)
  let xc : twoCoreIn K := ⟨x, hxcore⟩
  have hxcCenter : xc ∈ Subgroup.center (twoCoreIn K) := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp
      (hcoreCentralV y.property) x hxV).symm
  exact ⟨xc, hxcCenter, rfl⟩

end Stellmacher.SectionsFiveToSeven
