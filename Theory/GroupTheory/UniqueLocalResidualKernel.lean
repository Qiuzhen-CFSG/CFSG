module
public import Theory.GroupTheory.TwoLocalUniquenessControl
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PCoreImage

/-!
# Residual kernels and unique maximal two-local overgroups

An overgroup escaping the unique maximal two-local over J has no nontrivial
two-core. In a characteristic-two group, the same uniqueness kills a normal
subgroup normalized by J: its two-core vanishes, then self-centralization
kills the subgroup. The residual of a normal kernel is normalized by an
external L when its L-commutators lie in a normal two-subgroup; this follows
by recovering that residual from its product with the two-subgroup.

Source: the uniqueness argument in Aschbacher–Smith 13.3.18(1), printed
p.894. All subgroups and residuals are retained in their original ambient group.
-/

public section
namespace Subgroup
open scoped commutatorElement
variable {G:Type*} [Group G] [Finite G]

/-- The actual generated overgroup has trivial two-core when it escapes
the unique maximal two-local over the original uniqueness subgroup. -/
theorem sup_twoCore_eq_bot_of_unique (J H M:Subgroup G)
    (hu:∀N:Subgroup G,IsMaximalTwoLocal N→J≤N→N=M)
    (hout:¬H≤M) : pCore 2 (J⊔H:Subgroup G)=⊥ := by
  by_contra hn
  let K:Subgroup G:=(J⊔H:Subgroup G).pCoreIn 2
  have hK:K≠⊥ := by
    intro h
    exact hn ((map_eq_bot_iff_of_injective _ (J⊔H).subtype_injective).mp h)
  have hNK:J⊔H≤normalizer (K:Set G):=(J⊔H).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  exact hout (le_sup_right.trans (hNK.trans
    (normalizer_le_of_unique_maximalTwoLocal hu (isPGroup_pCoreIn 2 _) hK
      (le_sup_left.trans hNK))))

/-- A normal subgroup in a characteristic-two group is trivial if the
unique-overgroup subgroup normalizes it while the whole group escapes. -/
theorem normal_eq_bot_of_unique_core (J H M Y:Subgroup G)
    (hu:∀N:Subgroup G,IsMaximalTwoLocal N→J≤N→N=M)
    (hout:¬H≤M)
    (hself:H⊓centralizer (H.pCoreIn 2:Set G)≤H.pCoreIn 2)
    (hYH:Y≤H) (hHY:H≤normalizer (Y:Set G))
    (hJY:J≤normalizer (Y:Set G)) : Y=⊥ := by
  have hcore:Y.pCoreIn 2=⊥ := by
    by_contra hn
    have hchar:normalizer (Y:Set G)≤normalizer (Y.pCoreIn 2:Set G):=
      normalizer_le_normalizer_characteristic_image Y (pCore 2 Y)
    exact hout (hHY.trans (hchar.trans
      (normalizer_le_of_unique_maximalTwoLocal hu (isPGroup_pCoreIn 2 Y) hn (hJY.trans hchar))))
  have hcap:Y⊓H.pCoreIn 2≤Y.pCoreIn 2 := le_pCoreIn_of_normalizes
    ((isPGroup_pCoreIn 2 H).to_le inf_le_right) inf_le_left
    ((le_inf Y.le_normalizer (hYH.trans (H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H))))).trans
      inf_normalizer_le_normalizer_inf)
  have hcomm:⁅Y,H.pCoreIn 2⁆=⊥ := by
    apply le_bot_iff.mp
    rw [←hcore]
    apply le_trans _ hcap
    exact le_inf
      (le_normalizer_iff_commutator_le_left.mp ((pCoreIn_le 2 H).trans hHY))
      (le_normalizer_iff_commutator_le_right.mp (hYH.trans (H.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))))
  have hYQ:Y≤H.pCoreIn 2 :=
    (le_inf hYH (commutator_eq_bot_iff_le_centralizer.mp hcomm)).trans hself
  exact le_bot_iff.mp ((le_inf le_rfl hYQ).trans (hcap.trans_eq hcore))

/-- The residual of an actual normal kernel is normalized by L as soon
as its L-commutators lie in the displayed normal two-group. -/
theorem normalizes_residual_of_commutator_le_two (L H K Q:Subgroup G)
    (hHK:H≤normalizer (K:Set G)) (hQH:Q≤H)
    (hQ:IsPGroup 2 Q) (hLQ:L≤normalizer (Q:Set G))
    (hc:⁅L,(pResidual 2 K).map K.subtype⁆≤Q) :
    L≤normalizer ((pResidual 2 K).map K.subtype:Set G) := by
  let Y:Subgroup G:=(pResidual 2 K).map K.subtype
  let D:=Y⊔Q
  have hHY:H≤normalizer (Y:Set G):=hHK.trans
    (normalizer_le_normalizer_characteristic_image K (pResidual 2 K))
  let : (Y.subgroupOf D).Normal:=normal_subgroupOf_of_le_normalizer
    (sup_le Y.le_normalizer (hQH.trans hHY))
  have hp:IsPPerfect 2 (Y.subgroupOf D):=
    (isPPerfect_embedded_pResidual 2 K).of_surjective
      (subgroupOfEquivOfLe (show Y≤D from le_sup_left)).symm.toMonoidHom
      (subgroupOfEquivOfLe (show Y≤D from le_sup_left)).symm.surjective
  have hs:Y.subgroupOf D⊔Q.subgroupOf D=⊤ := by
    apply map_injective D.subtype_injective
    rw [map_sup,map_subgroupOf_eq_of_le le_sup_left,map_subgroupOf_eq_of_le le_sup_right,
      ←MonoidHom.range_eq_map,range_subtype]
  have hr:(pResidual 2 D).map D.subtype=Y := by
    rw [pResidual_eq_of_isPPerfect_sup _ _ hp hQ.comap_subtype hs,
      map_subgroupOf_eq_of_le le_sup_left]
  have hLD:L≤normalizer (D:Set G) := by
    apply le_normalizer_iff.mpr
    intro l hl d hd
    have hm:D.map (MulAut.conj l).toMonoidHom≤D := by
      rw [show D=Y⊔Q from rfl,map_sup]
      apply sup_le
      · rintro _ ⟨y,hy,rfl⟩
        change l*y*l⁻¹∈Y⊔Q
        have he:l*y*l⁻¹=⁅l,y⁆*y := by simp [commutatorElement_def,mul_assoc]
        rw [he]
        exact (Y⊔Q).mul_mem (mem_sup_right (hc (commutator_mem_commutator hl hy)))
          (mem_sup_left hy)
      · rintro _ ⟨q,hq,rfl⟩
        exact mem_sup_right (le_normalizer_iff.mp hLQ l hl q hq)
    exact hm (mem_map_of_mem _ hd)
  change L≤normalizer (Y:Set G)
  rw [←hr]
  exact hLD.trans (normalizer_le_normalizer_characteristic_image D (pResidual 2 D))
end Subgroup
