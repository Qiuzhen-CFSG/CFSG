module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternativesPreparation
public import CFSG.Quasithin.Chapter4.Section02.Unitary.FullModule
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedNormalSeedMovedModule
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedNormalSeedQuotient
public import CFSG.Quasithin.Chapter13.Section05.A5Source.Context
public import Theory.Representation.AlternatingFiveLinearTwoObstruction

/-!
# The original cubic-fixed vector in an actual marked moved section

Keep the original chosen A₅ module inside the full source module and then
inside the literal star moved space. Its cubic-fixed nonzero vector remains
nonzero there. The same star map carries its cubic to an element of order
three modulo the complete two-core of the marked seed. The acting group may have any specified marking.

This is source data for the native cover obstruction. No identification
of the whole four-dimensional module with a natural plane is assumed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open ChapterC ChapterB.QuasisimpleSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}

set_option maxHeartbeats 2400000 in
/-- The original Steinberg cubic supplies a nonzero fixed vector in the
same core-fixed, fully moved subspace under an arbitrary actor marking. -/
theorem a5_source_moved_cubic_fixed_vector
    (d : Chapter13.Section05.A5Source.Context T L V V₁ V₂ V₃)
    (c : SourceConfiguration T L) (hf : generalizedFitting c.K = pCore 2 c.K)
    (s : MovedSection ((starRepresentation (c.K.map c.H.subtype) (c.I.pCoreIn 2)).comp
      (offenderSubgroup (starRepresentation (c.K.map c.H.subtype) (c.I.pCoreIn 2))).subtype)
      ((starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype)).subgroupOf
        (offenderSubgroup (starRepresentation (c.K.map c.H.subtype) (c.I.pCoreIn 2)))))
    {D : Type*} [Group D]
    (e : ((starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype)).subgroupOf
      (offenderSubgroup (starRepresentation (c.K.map c.H.subtype) (c.I.pCoreIn 2)))) ≃* D) :
    let K := c.K.map c.H.subtype
    let R := c.I.pCoreIn 2
    let C := starImage K R K
    let O := offenderSubgroup (starRepresentation K R)
    let hCO := (C27Source.star_moved_section_from_source (c.block_source_input hf)).1
    let E := (subgroupOfEquivOfLe hCO).symm.trans e
    let B := (L.subgroupOf K).map (E.toMonoidHom.comp (toStarImage K R))
    let σ := s.space.toRepresentation.comp ((C.subgroupOf O).subtype.comp e.symm.toMonoidHom)
    ∃ A : Submodule (ZMod 2) s.space.toSubmodule,
        A ≤ fixedSpace σ (B.pCoreIn 2) ∧ subspaceCommutator σ A B = A ∧
        ∃ b : B, orderOf (QuotientGroup.mk' (pCore 2 B) b) = 3 ∧
          ∃ w : s.space.toSubmodule, w ≠ 0 ∧ w ∈ A ∧ σ b.val w = w := by
  let K := c.K.map c.H.subtype
  let R := c.I.pCoreIn 2
  let C := starImage K R K
  let O := offenderSubgroup (starRepresentation K R)
  have hsource := c.block_source_input hf
  have hCO : C ≤ O := (C27Source.star_moved_section_from_source hsource).1
  let eC := subgroupOfEquivOfLe hCO
  let E := eC.symm.trans e
  let q := E.toMonoidHom.comp (toStarImage K R)
  let B := (L.subgroupOf K).map q
  let σ := s.space.toRepresentation.comp ((C.subgroupOf O).subtype.comp e.symm.toMonoidHom)
  have hn : (L.subgroupOf (c.H ⊓ normalizer (L : Set G))).Normal :=
    normal_subgroupOf_of_le_normalizer inf_le_right
  obtain ⟨A,hA,hm,hlift⟩ := c.c28.constrained_normal_seed_moved_module hn d.quotient
    c.K c.component c.quotient c.block_source_outside hf s e
  refine ⟨A,hA,hm,?_⟩
  let qL : L →* B := (q.subgroupMap (L.subgroupOf K)).comp
    (subgroupOfEquivOfLe c.le_component).symm.toMonoidHom
  have hquot : ∃ a : (L ⧸ pCore 2 L) ≃* (B ⧸ pCore 2 B),
      ∀ l : L, a (QuotientGroup.mk' (pCore 2 L) l) =
        QuotientGroup.mk' (pCore 2 B) (qL l) :=
    (c.c28.constrained_normal_seed_quotient (D := D) d.quotient
      c.K c.component c.quotient c.block_source_outside hf c.le_component E).2.2
  obtain ⟨aQ₀,haQ₀⟩ := hquot
  let aQ := d.quotient.symm.trans aQ₀
  have haQ (l : L) : aQ (d.flag.module.action l) =
      QuotientGroup.mk' (pCore 2 B) (qL l) := by
    rw [←d.quotient_mk l]
    change aQ₀ (d.quotient.symm (d.quotient (QuotientGroup.mk' (pCore 2 L) l))) = _
    rw [d.quotient.symm_apply_apply]
    exact haQ₀ l
  obtain ⟨a,ha,v,hv,hav⟩ := BinaryPermutation.AlternatingFiveLinearTwo.exists_cubic_fixed_ne_zero
  obtain ⟨l,hl⟩ := d.flag.module.onto a
  have hord : orderOf (QuotientGroup.mk' (pCore 2 B) (qL l)) = 3 := by
    rw [←haQ,hl]
    exact (orderOf_injective aQ.toMonoidHom aQ.injective a).trans ha
  let z : V := ⟨d.flag.module.map (Multiplicative.ofAdd v),d.flag.module.range_eq.le ⟨_,rfl⟩⟩
  have hz : (z : G) ≠ 1 := by
    intro he
    exact hv (Multiplicative.ofAdd.injective
      (d.flag.module.injective (he.trans d.flag.module.map.map_one.symm)))
  have hzl : (l : G) * (z : G) * (l : G)⁻¹ = z := by
    have hh := d.flag.module.equivariant l v
    rw [hl,hav] at hh
    exact hh
  have hVW := Section02.Unitary.chosen_le_fullModule d.chosen
  obtain ⟨w,hw,he,_⟩ := hlift ⟨z,hVW z.property⟩
  have hwne : w ≠ 0 := by
    intro hw0
    rw [hw0] at he
    exact hz he.symm
  have hact : (σ (qL l).val w).val =
      starRepresentation K R ((starImage K R K).subtype
        (toStarImage K R ⟨l,c.le_component l.property⟩)) w.val := by
    change starRepresentation K R
      (((e.symm (e (eC.symm
        (toStarImage K R ⟨l,c.le_component l.property⟩))) : C.subgroupOf O) : O) :
          StarQuotient K R) w.val = _
    rw [e.symm_apply_apply]
    rfl
  have hfix : σ (qL l).val w = w := by
    apply Subtype.ext
    rw [hact]
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    change (((starRepresentation K R (QuotientGroup.mk' (starKernel K R)
      ⟨l,mem_sup_left (c.le_component l.property)⟩) w.val).toMul :
        (K ⊔ R : Subgroup G)) : G) = _
    rw [starRepresentation_apply]
    change (l : G) * (((w.val.toMul : starV K R) : (K ⊔ R : Subgroup G)) : G) *
      (l : G)⁻¹ = (((w.val.toMul : starV K R) : (K ⊔ R : Subgroup G)) : G)
    rw [he]
    exact hzl
  exact ⟨qL l,hord,w,hwne,hw,hfix⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
