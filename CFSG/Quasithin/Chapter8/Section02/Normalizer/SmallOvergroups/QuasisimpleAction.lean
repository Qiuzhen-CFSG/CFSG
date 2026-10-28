module

public import CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.Action

/-!
# Lifting an unchanged action through the quasisimple component

For the containing component K_U, the proper kernel on U is central modulo
O₂(K_U), by 8.2.7. If its action is already realized by L_U, the image of
L_U in K_U/O₂(K_U) has a central supplement. A perfect group has no proper
subgroup with a central supplement, so K_U = L_U O₂(K_U). The actual Sylow
normalizes L_U and absorbs O₂(K_U), and the two-group supplement disappears.

Thus the cocode case follows from the full GL(U) action, without an extra
assumption identifying C_{K_U}(U). The other cases reduce to the genuinely
marked action-image containment. This argument also allows the cubic
central kernel in the code branch; it never replaces that kernel by O₂.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
Proposition 8.2.8(1), printed p.719 (PDF p.736), with 8.2.6–7 as inputs.
The rank-four overgroup inspections remain separate obligations.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups
variable {G : Type*} [Group G]

private theorem eq_top_of_sup_center_eq_top [Group.IsPerfect G]
    (D : Subgroup G) (hgen : D ⊔ center G = ⊤) : D = ⊤ := by
  let : D.Normal := normalizer_eq_top_iff.mp (top_unique (by
    rw [← hgen]
    exact sup_le D.le_normalizer (center_le_normalizer (D : Set G))))
  have hcomm := Normal.commutator_le_of_self_sup_commutative_eq_top hgen
    (inferInstance : IsMulCommutative (center G))
  exact top_unique (by simpa only [Group.IsPerfect.commutator_eq_top] using hcomm)

/-- The remaining model inspections need only compare the literal action
images on U. Quasisimplicity proves the needed central-kernel bound here;
no classification of the kernel or central cover is an additional premise. -/
theorem localResidual_eq_of_quasisimple_actionImage [Finite G] (L K U T : Subgroup G)
    [Group.IsPerfect K] [Theory.GroupTheory.IsQuasisimple (K ⧸ pCore 2 K)]
    (hRK : localResidual L U ≤ K) (hKN : K ≤ normalizer (U : Set G))
    (hQT : K.pCoreIn 2 ≤ T) (hTL : T ≤ normalizer (L : Set G))
    (hTU : T ≤ normalizer (U : Set G))
    (hnontriv : ¬ localResidual L U ≤ centralizer (U : Set G))
    (haction : actionImage K U ≤ actionImage (localResidual L U) U) :
    localResidual L U = K := by
  let R := localResidual L U
  let C := (centralizer (U : Set G)).subgroupOf K
  have hNC : normalizer (U : Set G) ≤ normalizer (centralizer (U : Set G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer _)).mp inferInstance
  let : C.Normal := normal_subgroupOf_of_le_normalizer (hKN.trans hNC)
  have hproper : C ≠ ⊤ := by
    intro he
    apply hnontriv
    intro r hr
    exact (show (⟨r, hRK hr⟩ : K) ∈ C from he ▸ mem_top _)
  let q := QuotientGroup.mk' (pCore 2 K)
  have hc : C.map q ≤ center (K ⧸ pCore 2 K) := by
    apply commutator_top_right_eq_bot_iff_le_center.mp
    rw [← map_top_of_surjective q (QuotientGroup.mk'_surjective _), ← map_commutator]
    exact (Subgroup.map_eq_bot_iff _).mpr (by
      rw [QuotientGroup.ker_mk']
      exact normal_kernel_commutator_le_twoCore C hproper)
  let D := (R.subgroupOf K).map q
  have hgen : D ⊔ center (K ⧸ pCore 2 K) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) x
    let kn : normalizer (U : Set G) := ⟨k, hKN k.property⟩
    obtain ⟨rn, hr, he⟩ := haction (show U.normalizerMonoidHom kn ∈ actionImage K U from
      mem_map_of_mem U.normalizerMonoidHom k.property)
    let r : K := ⟨rn, hRK hr⟩
    have hkr : rn⁻¹ * kn ∈ U.normalizerMonoidHom.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, he, inv_mul_cancel]
    rw [normalizerMonoidHom_ker] at hkr
    have hrc : r⁻¹ * k ∈ C := hkr
    have hm := (D ⊔ center (K ⧸ pCore 2 K)).mul_mem
      (mem_sup_left (mem_map_of_mem q (show r ∈ R.subgroupOf K from hr)))
      (mem_sup_right (hc (mem_map_of_mem q hrc)))
    simpa only [← map_mul, mul_inv_cancel_left] using hm
  have hD : D = ⊤ := eq_top_of_sup_center_eq_top D hgen
  have hs : R.subgroupOf K ⊔ pCore 2 K = ⊤ := by
    have he := congrArg (Subgroup.comap q) hD
    simpa only [D, comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using he
  have hcover : R ⊔ K.pCoreIn 2 = K := by
    have he := congrArg (Subgroup.map K.subtype) hs
    simpa only [Subgroup.map_sup, map_subgroupOf_eq_of_le (show R ≤ K from hRK),
      ← MonoidHom.range_eq_map, range_subtype, pCoreIn] using he
  exact localResidual_eq_of_actionImage_le L K U T hRK hKN hQT hTL hTU
    (inf_le_left.trans (hcover.symm.le)) haction

/-- The cocode branch of 8.2.8(1) from 8.2.6's nontrivial full action,
8.2.7's quasisimple quotient, and the actual source Sylow. -/
theorem cocode_localResidual_eq_and_normal [Finite G]
    (L K U : Subgroup G) (S : Sylow 2 (normalizer (U : Set G)))
    [Group.IsPerfect K] [Theory.GroupTheory.IsQuasisimple (K ⧸ pCore 2 K)]
    (hRK : localResidual L U ≤ K) (hKN : K ≤ normalizer (U : Set G))
    (hNK : normalizer (U : Set G) ≤ normalizer (K : Set G))
    (hSL : (S : Subgroup (normalizer (U : Set G))).map
      (normalizer (U : Set G)).subtype ≤ normalizer (L : Set G))
    (hnontriv : ¬ localResidual L U ≤ centralizer (U : Set G))
    (hfull : actionImage (localResidual L U) U = ⊤) :
    localResidual L U = K ∧
      ((localResidual L U).subgroupOf (normalizer (U : Set G))).Normal := by
  have he := localResidual_eq_of_quasisimple_actionImage L K U _ hRK hKN
    ((pCoreIn_mono_of_normalizes hKN hNK).trans (pCoreIn_le_sylow _ S)) hSL
    (map_subtype_le _) hnontriv (by rw [hfull]; exact le_top)
  exact ⟨he, he ▸ normal_subgroupOf_of_le_normalizer hNK⟩

end CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups
