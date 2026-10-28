module

public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Commutators.QuotientImage.ActionData
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.CoreEquality
public import Theory.SpecificGroups.PSL3Two.Parabolics.Cores.CubicAction
/-!
# The marked cubic action and index in J.2.4(1)

Restrict the common Ru1 marking to the literal overlap L ∩ H, whose image
is S₄ and whose kernel is S. Its restriction to L₁ = O²(L ∩ H) has image
the actual two-residual of S₄, of order twelve. Therefore the chosen Sylow
three-subgroup B has a cubic image. Conjugation by this image is irreducible
on the four-core. Mapping a B-invariant A ≤ R₁ into that core and pulling
back gives A ≤ S or AS = R₁.

The same map identifies R₁/S with the four-core, giving index four.
Relative normality of S inside L ∩ H and the proved equality R₁ = QS then
transfer this to |Q : Q ∩ S| = 4. These deductions construct both fields of
`CubicQuotientData` without additional action or index assumptions.
The quotient-image assembly consumes this record in
`Fusion.modZ_commutator_eq_of_cubic`.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
J.2.2(1) and J.2.4(1), printed pp.432–434 (PDF pp.443–445).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.Fusion
noncomputable section
variable {G : Type*} [Group G] [Finite G]
private theorem residual_card {X : Type*} [Group X] [Finite X]
    (e : X ≃* Equiv.Perm (Fin 4)) : Nat.card (pResidual 2 X) = 12 := by
  rw [← card_map_of_injective (K := pResidual 2 X) (f := e.toMonoidHom) e.injective,
    map_pResidual, Equiv.Perm.twoResidual_eq_alternating, nat_card_alternatingGroup,
    Nat.card_fin]
  decide

private theorem L₁_le_parabolic (d : LocalSetup G) : d.toTypeRuSetup.L₁ ≤ d.parabolic :=
  map_subtype_le _

private def residualMap (d : LocalSetup G) : d.toTypeRuSetup.L₁ →* d.parabolicMap.range :=
  d.parabolicMap.rangeRestrict.comp (inclusion (L₁_le_parabolic d))

private theorem residualMap_range (d : LocalSetup G) :
    (residualMap d).range = pResidual 2 d.parabolicMap.range := by
  rw [residualMap, MonoidHom.range_comp, inclusion_range]
  have he : d.toTypeRuSetup.L₁.subgroupOf d.parabolic = pResidual 2 d.parabolic := by
    exact comap_map_eq_self_of_injective d.parabolic.subtype_injective _
  rw [he, map_pResidual_of_surjective 2 _ d.parabolicMap.rangeRestrict_surjective]

private theorem exists_cubic_parabolic_image (d : LocalSetup G)
    (B : Sylow 3 d.toTypeRuSetup.L₁) :
    ∃ b : d.toTypeRuSetup.L₁, b ∈ (B : Subgroup d.toTypeRuSetup.L₁) ∧
      orderOf (residualMap d b) = 3 := by
  let f := residualMap d
  let C := B.mapSurjective f.rangeRestrict_surjective
  have hc : Nat.card f.range = 12 := by
    rw [show f.range = pResidual 2 d.parabolicMap.range from residualMap_range d]
    exact residual_card d.parabolicImageEquivS4
  have hC : Nat.card C = 3 := by
    rw [Sylow.card_eq_multiplicity, hc]
    decide +kernel
  obtain ⟨c, hc3⟩ := exists_prime_orderOf_dvd_card' 3 (show 3 ∣ Nat.card C by rw [hC])
  have hmem : (c : f.range) ∈ (B : Subgroup d.toTypeRuSetup.L₁).map f.rangeRestrict := c.property
  obtain ⟨b, hb, he⟩ := hmem
  refine ⟨b, hb, ?_⟩
  have ho : orderOf ((c : f.range) : d.parabolicMap.range) = 3 := by
    rw [orderOf_coe, orderOf_coe, hc3]
  have he' : f b = ((c : f.range) : d.parabolicMap.range) := congrArg Subtype.val he
  rw [he', ho]

private theorem R₁_eq_parabolic_core (d : LocalSetup G) :
    d.toTypeRuSetup.R₁ = d.parabolic.pCoreIn 2 := by
  rw [← d.parabolic_core_eq_R₁, ← d.H_inf_L, inf_comm]

private theorem R₁_image (d : LocalSetup G) :
    (d.toTypeRuSetup.R₁.subgroupOf d.parabolic).map d.parabolicMap.rangeRestrict =
      pCore 2 d.parabolicMap.range := by
  have hk : IsPGroup 2 d.parabolicMap.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict, d.parabolicMap_kernel]
    exact (isPGroup_pCoreIn 2 d.L).comap_subtype
  have hr : d.toTypeRuSetup.R₁.subgroupOf d.parabolic = pCore 2 d.parabolic := by
    rw [R₁_eq_parabolic_core]
    exact comap_map_eq_self_of_injective d.parabolic.subtype_injective _
  rw [hr, ← d.parabolicMap.rangeRestrict.comap_pCore_of_ker_isPGroup
    d.parabolicMap.rangeRestrict_surjective hk,
    map_comap_eq_self (by rw [MonoidHom.range_eq_top_of_surjective _
      d.parabolicMap.rangeRestrict_surjective]; exact le_top)]

/-- Index four for the literal R₁/S. -/
theorem index_R₁_S (d : LocalSetup G) :
    d.toTypeRuSetup.S.relIndex d.toTypeRuSetup.R₁ = 4 := by
  have hi := relIndex_ker (d.toTypeRuSetup.R₁.subgroupOf d.parabolic)
    d.parabolicMap.rangeRestrict
  rw [MonoidHom.ker_rangeRestrict, d.parabolicMap_kernel,
    relIndex_subgroupOf ((pCoreIn_le 2 _).trans (L₁_le_parabolic d)), R₁_image d,
    (Matrix.PSL3Two.ParabolicCoreModel.core_data d.parabolicImageEquivS4).2] at hi
  exact hi

/-- The index appearing in the actual Q-centralizer obstruction. -/
theorem index_Q_S (d : LocalSetup G) :
    d.toTypeRuSetup.S.relIndex d.toTypeRuSetup.Q = 4 := by
  have hQP : d.toTypeRuSetup.Q ≤ d.parabolic := le_inf d.Q_le_L (pCoreIn_le 2 _)
  have hSP : d.toTypeRuSetup.S ≤ d.parabolic := le_inf (pCoreIn_le 2 _) d.S_le_H
  let : (d.toTypeRuSetup.S.subgroupOf d.parabolic).Normal :=
    normal_subgroupOf_of_le_normalizer (inf_le_left.trans d.ru1.steinberg.normalized)
  have hi := relIndex_sup_right (d.toTypeRuSetup.Q.subgroupOf d.parabolic)
    (d.toTypeRuSetup.S.subgroupOf d.parabolic)
  rw [← subgroupOf_sup hQP hSP, relIndex_subgroupOf (sup_le hQP hSP),
    relIndex_subgroupOf hQP, ← d.parabolic_core_eq_Q_sup_S,
    ← R₁_eq_parabolic_core d, index_R₁_S d] at hi
  exact hi.symm
/-- Cubic irreducibility on the actual R₁/S. -/
theorem invariant_R₁_S (d : LocalSetup G) (B : Sylow 3 d.toTypeRuSetup.L₁)
    (A : Subgroup G) (hA : A ≤ d.toTypeRuSetup.R₁)
    (hBA : BSubgroup d.toTypeRuSetup B ≤ normalizer (A : Set G)) :
    A ≤ d.toTypeRuSetup.S ∨ A ⊔ d.toTypeRuSetup.S = d.toTypeRuSetup.R₁ := by
  let P := d.parabolic
  let f := d.parabolicMap.rangeRestrict
  have hRP : d.toTypeRuSetup.R₁ ≤ P :=
    (pCoreIn_le 2 _).trans (L₁_le_parabolic d)
  have hAP : A ≤ P := hA.trans hRP
  have hSP : d.toTypeRuSetup.S ≤ P := le_inf (pCoreIn_le 2 _) d.S_le_H
  have hk : f.ker = d.toTypeRuSetup.S.subgroupOf P := by
    rw [MonoidHom.ker_rangeRestrict, d.parabolicMap_kernel]
  let N := (A.subgroupOf P).map f
  have hN : N ≤ pCore 2 d.parabolicMap.range := by
    rw [← R₁_image d]
    exact map_mono (fun a ha => hA ha)
  obtain ⟨b, hb, hc⟩ := exists_cubic_parabolic_image d B
  have hbn : (b : G) ∈ normalizer (A : Set G) :=
    hBA (mem_map.mpr ⟨b, hb, rfl⟩)
  have hn : residualMap d b ∈ normalizer (N : Set _) := by
    apply (A.subgroupOf P).le_normalizer_map f
    refine mem_map.mpr ⟨inclusion (L₁_le_parabolic d) b, ?_, rfl⟩
    apply mem_normalizer_iff.mpr
    intro a
    exact mem_normalizer_iff.mp hbn a
  rcases Matrix.PSL3Two.ParabolicCoreModel.cubic_invariant_core
      d.parabolicImageEquivS4 (residualMap d b) hc N hN hn with hn | hn
  · left
    have hl := (map_eq_bot_iff (A.subgroupOf P)).mp hn
    rw [hk] at hl
    exact fun a ha => hl (show (⟨a, hAP ha⟩ : P) ∈ A.subgroupOf P from ha)
  · right
    have he := congrArg (fun N : Subgroup d.parabolicMap.range => N.comap f) hn
    change ((A.subgroupOf P).map f).comap f = _ at he
    rw [comap_map_eq, hk] at he
    have hkr : IsPGroup 2 f.ker := by
      rw [hk]
      exact (isPGroup_pCoreIn 2 d.L).comap_subtype
    rw [f.comap_pCore_of_ker_isPGroup d.parabolicMap.rangeRestrict_surjective hkr] at he
    have hm := congrArg (fun N : Subgroup P => N.map P.subtype) he
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hAP,
      map_subgroupOf_eq_of_le hSP] at hm
    exact hm.trans (R₁_eq_parabolic_core d).symm

/-- The point-parabolic marking supplies both cubic action obligations. -/
theorem cubicQuotientData (d : LocalSetup G) (B : Sylow 3 d.toTypeRuSetup.L₁) :
    CubicQuotientData d B :=
  ⟨invariant_R₁_S d B, index_Q_S d⟩
end
end CFSG.Quasithin.ChapterJ.Fusion
