module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternatingGeometry.Contracts
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingSevenExtensionCoordinates
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.Radical

/-!
# The actual seven-letter action in the source A₇ branch

The ordinary block model gives coordinates on the whole U(K), with the
literal KS conjugation action and kernel O₂(KS). All transport uses the
original inclusions K ≤ H ≤ G. The original radical R cannot disappear in
this action: O₂(KS) ≤ R, and equality would make K normalize R, contrary
to the characteristic-normalizer control in C.2.8.

These results construct the unmarked action used by the local-coordinate
proof. Identifying the two fixed letters and the full moved module remains
with the rank-one block-alternating assembly owner.
Source: Aschbacher--Smith C.4.1(1), C.4.6 and 4.3.7, pp.151--152,616.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Characteristic-normalizer control excludes the trivial radical image
before any coordinate or transposition marking is chosen. -/
theorem SourceConfiguration.radical_not_le_join_core (c : SourceConfiguration T L) :
    ¬ c.I.pCoreIn 2 ≤
      (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H)).pCoreIn 2 := by
  intro h
  have he := le_antisymm h c.block_join_core_le
  have hn : c.K.map c.H.subtype ≤ normalizer (c.I.pCoreIn 2 : Set G) := by
    rw [he]
    exact (le_sup_left : c.K.map c.H.subtype ≤
      c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H)).trans
        ((c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H)).le_normalizer.trans
          (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  exact c.component_outside
    (((le_inf (map_subtype_le _) hn).trans c.c28.normalizer_le).trans inf_le_right)

/-- Every action with the source two-core kernel sees the original R. -/
theorem SourceConfiguration.alternating_radical_image_ne_bot
    (c : SourceConfiguration T L)
    (f : (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H) : Subgroup G) →*
      Equiv.Perm (Fin 7))
    (hk : f.ker = pCore 2
      (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H) : Subgroup G)) :
    ((c.I.pCoreIn 2).subgroupOf
      (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H))).map f ≠ ⊥ := by
  intro hbot
  have hr := (Subgroup.map_eq_bot_iff _).mp hbot
  rw [hk] at hr
  apply c.radical_not_le_join_core
  intro r hrR
  have hrJ : r ∈ c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H) :=
    (c.core_sylow.le.trans (inf_le_left.trans le_sup_right)) hrR
  exact mem_map_of_mem _ (hr (show (⟨r,hrJ⟩ :
    (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H) : Subgroup G)) ∈
      (c.I.pCoreIn 2).subgroupOf _ from hrR))

/-- The defining ordinary block model gives a compatible chart on all of
U(K), retaining the actual action kernel and a nontrivial original R-image. -/
theorem SourceConfiguration.exists_alternating_join_chart
    (c : SourceConfiguration T L) (ha : ChapterC.IsAlternatingBlock c.K 7) :
    ∃ d : BinaryPermutation.SevenParabolic.Ordinary.Chart
      (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H)) (c.K.map c.H.subtype)
      ((ChapterC.blockU (c.K.map c.H.subtype)).map (c.K.map c.H.subtype).subtype),
      d.actor.ker = pCore 2
        (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H) : Subgroup G) ∧
      ((c.I.pCoreIn 2).subgroupOf
        (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H))).map d.actor ≠ ⊥ := by
  let A := c.K.map c.H.subtype
  let S := (T : Subgroup G) ⊓ c.H
  let J := A ⊔ S
  let B := A.subgroupOf J
  have hAJ : A ≤ J := le_sup_left
  have hSJ : S ≤ J := le_sup_right
  have hn : J ≤ normalizer (A : Set G) :=
    sup_le A.le_normalizer (inf_le_right.trans c.normalizer_component.le)
  let : B.Normal := normal_subgroupOf_of_le_normalizer hn
  let eBA : B ≃* A := subgroupOfEquivOfLe hAJ
  have hB : ChapterC.IsAlternatingBlock B 7 :=
    ChapterC.RankOne.Solvable.isAlternatingBlock_of_equiv eBA.symm
      (c.ambient_alternating_block ha)
  have hgen : B ⊔ S.subgroupOf J = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hAJ,
      map_subgroupOf_eq_of_le hSJ,← MonoidHom.range_eq_map,range_subtype]
  have hp : IsPGroup 2 (J ⧸ B) := isPGroup_quotient_of_sup_eq_top B
    (S.subgroupOf J) (T.isPGroup'.to_le inf_le_left).comap_subtype hgen
  obtain ⟨f,e,hk,himage,he⟩ := hB.exists_extension_coordinates B hp
  let U₀ := (ChapterC.blockU B).map B.subtype
  let U := (ChapterC.blockU A).map A.subtype
  have hU : U₀.map J.subtype = U := by
    change ((ChapterC.blockU B).map B.subtype).map J.subtype = _
    rw [map_map]
    have hm := congrArg (map A.subtype)
      (ChapterC.RankOne.Solvable.blockU_map_equiv eBA)
    rw [map_map] at hm
    exact hm
  let eU : U₀ ≃* U := (U₀.equivMapOfInjective J.subtype J.subtype_injective).trans
    (MulEquiv.subgroupCongr hU)
  have heU (u : U₀) : (eU u : G) = ((u : J) : G) := rfl
  let e' := eU.symm.trans e
  have hnU : J ≤ normalizer (U : Set G) :=
    hn.trans (normalizer_le_normalizer_characteristic_image A (ChapterC.blockU A))
  have he' (j : J) (u : U) :
      (e'.symm (BinaryPermutation.SevenMarkedAction.coreAction (f j) (e' u)) : G) =
        (j : G) * (u : G) * (j : G)⁻¹ := by
    have hh := congrArg (fun x : J => (x : G)) (he j (eU.symm u))
    have hu : (((eU.symm u : U₀) : J) : G) = u :=
      (heU (eU.symm u)).symm.trans (congrArg Subtype.val (eU.apply_symm_apply u))
    change (eU (e.symm (BinaryPermutation.SevenMarkedAction.coreAction (f j)
      (e (eU.symm u)))) : G) = _
    rw [heU]
    simpa only [coe_mul,coe_inv,hu] using hh
  let d : BinaryPermutation.SevenParabolic.Ordinary.Chart J A U := {
    moduleEquiv := e'
    actor := f
    normalized := hnU
    component_image := himage
    equivariant := by
      intro j u
      have hh := he' j u
      have hh' : e'.symm (BinaryPermutation.SevenMarkedAction.coreAction (f j) (e' u)) =
          ⟨(j : G) * (u : G) * (j : G)⁻¹,
            le_normalizer_iff.mp hnU j j.property u u.property⟩ := Subtype.ext hh
      have h := congrArg (fun v : U => (e' v).toAdd) hh'
      rw [e'.apply_symm_apply] at h
      exact h.symm }
  exact ⟨d,hk,c.alternating_radical_image_ne_bot f hk⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
