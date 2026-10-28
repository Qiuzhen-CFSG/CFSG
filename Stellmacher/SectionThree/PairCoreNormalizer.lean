module

public import Stellmacher.SectionsOneToFourDefs

/-!
# A common Sylow subgroup normalizes the core intersection

Suppose `T` is a Sylow 2-subgroup of each of `P₁` and `P₂`, and let
`K = ⟨P₁, P₂⟩`.  Then `K` normalizes `T ∩ O₂(K)`.  For each generator,
`Pᵢ ∩ O₂(K)` is a normal 2-subgroup of `Pᵢ`; it therefore lies in
`O₂(Pᵢ)`, and the Sylow property puts it in `T`.  Thus this intersection
is exactly `T ∩ O₂(K)` and is normalized by both generators.

This is the precise normalizer consequence used where the source invokes
(3.8) in the proof of (5.4).  Stating it separately avoids enlarging the
stable conclusion record of (3.8).

Source: `refs/latex/stellmacher-n-group.tex`, proof of (5.4), journal
pp. 29–30.
-/

open scoped Pointwise

namespace Stellmacher.SectionThree

universe u

variable {G : Type u} [Group G]

private theorem twoCoreAmbient_normal_subgroupOf (K : Subgroup G) :
    ((twoCoreAmbient K).subgroupOf K).Normal := by
  rw [← Subgroup.comap_subtype, twoCoreAmbient,
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
  exact (inferInstance : (pCore 2 K).Normal)

private theorem twoCoreAmbient_isPGroup (K : Subgroup G) :
    IsPGroup 2 (twoCoreAmbient K) :=
  (pCore_isPGroup (p := 2) (G := K)).map K.subtype

private theorem normal_pSubgroup_le_twoCoreAmbient
    (Q K : Subgroup G) (hQK : Q ≤ K)
    (hQp : IsPGroup 2 Q) (hQnormal : (Q.subgroupOf K).Normal) :
    Q ≤ twoCoreAmbient K := by
  have hQpK : IsPGroup 2 (Q.subgroupOf K) :=
    hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQK).symm
  have hle : Q.subgroupOf K ≤ pCore 2 K := le_sSup ⟨hQnormal, hQpK⟩
  calc
    Q = (Q.subgroupOf K).map K.subtype :=
      (Subgroup.map_subgroupOf_eq_of_le hQK).symm
    _ ≤ (pCore 2 K).map K.subtype := Subgroup.map_mono hle
    _ = twoCoreAmbient K := rfl

private theorem twoCoreAmbient_le_of_isSylowSubgroupIn
    {T P : Subgroup G} (hTP : IsSylowSubgroupIn T P) :
    twoCoreAmbient P ≤ T := by
  obtain ⟨U, hU⟩ := hTP
  unfold twoCoreAmbient
  rw [← hU]
  exact Subgroup.map_mono
    ((pCore_isPGroup (p := 2) (G := P)).le_sylow_of_normal U)

private theorem generator_inf_core_normal
    {T P K : Subgroup G} (hTP : IsSylowSubgroupIn T P)
    (hPK : P ≤ K) :
    ((T ⊓ twoCoreAmbient K).subgroupOf P).Normal := by
  have hTPle : T ≤ P := by
    obtain ⟨U, rfl⟩ := hTP
    exact Subgroup.map_subtype_le _
  let R : Subgroup G := P ⊓ twoCoreAmbient K
  have hRP : R ≤ P := inf_le_left
  have hRnormal : (R.subgroupOf P).Normal := by
    apply (Subgroup.normal_subgroupOf_iff hRP).mpr
    intro r p hr hp
    refine ⟨P.mul_mem (P.mul_mem hp hr.1) (P.inv_mem hp), ?_⟩
    exact (Subgroup.normal_subgroupOf_iff
      (show twoCoreAmbient K ≤ K from Subgroup.map_subtype_le _)).mp
        (twoCoreAmbient_normal_subgroupOf K) r p hr.2 (hPK hp)
  have hRp : IsPGroup 2 R :=
    (twoCoreAmbient_isPGroup K).to_le inf_le_right
  have hRcoreP : R ≤ twoCoreAmbient P :=
    normal_pSubgroup_le_twoCoreAmbient R P hRP hRp hRnormal
  have hRleT : R ≤ T :=
    hRcoreP.trans (twoCoreAmbient_le_of_isSylowSubgroupIn hTP)
  have heq : T ⊓ twoCoreAmbient K = R := by
    apply le_antisymm
    · exact le_inf (inf_le_left.trans hTPle) inf_le_right
    · exact le_inf hRleT inf_le_right
  rw [heq]
  exact hRnormal

/-- If `T` is a Sylow 2-subgroup of both generators, their join normalizes
its intersection with the 2-core of the join.  This is the normalizer
consequence used at the invocation of (3.8) in Stellmacher (5.4). -/
public theorem pair_le_normalizer_inf_twoCoreAmbient
    (T P₁ P₂ K : Subgroup G)
    (hT₁ : IsSylowSubgroupIn T P₁)
    (hT₂ : IsSylowSubgroupIn T P₂)
    (hK : K = P₁ ⊔ P₂) :
    K ≤ Subgroup.normalizer (T ⊓ twoCoreAmbient K : Set G) := by
  have hP₁K : P₁ ≤ K := by rw [hK]; exact le_sup_left
  have hP₂K : P₂ ≤ K := by rw [hK]; exact le_sup_right
  have hT₁le : T ≤ P₁ := by
    obtain ⟨U, rfl⟩ := hT₁
    exact Subgroup.map_subtype_le _
  have hT₂le : T ≤ P₂ := by
    obtain ⟨U, rfl⟩ := hT₂
    exact Subgroup.map_subtype_le _
  have hN₁ : P₁ ≤ Subgroup.normalizer (T ⊓ twoCoreAmbient K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (inf_le_left.trans hT₁le)).mp
        (generator_inf_core_normal hT₁ hP₁K)
  have hN₂ : P₂ ≤ Subgroup.normalizer (T ⊓ twoCoreAmbient K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (inf_le_left.trans hT₂le)).mp
        (generator_inf_core_normal hT₂ hP₂K)
  calc
    K = P₁ ⊔ P₂ := hK
    _ ≤ Subgroup.normalizer (T ⊓ twoCoreAmbient K : Set G) :=
      sup_le hN₁ hN₂

end Stellmacher.SectionThree
