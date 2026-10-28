module
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.LinearThreeSmallCore
public import CFSG.Quasithin.ChapterI.Section04To05.C3Recognition.PlaneCenterApplications

/-!
# Ambient assembly of the original binary-three C₃ system

For the literal three vertices LT, J and H, the ambient group is their
source-generated subgroup LT ∨ H. Their common Sylow subgroup has trivial
normal core by F.9.1. The source chief-count calculation supplies the strict
core-size bound required by I.5. The local residue producer supplies only
the middle quotient, chamber intersection and three rank-two parabolic lattices.

The terminal uses the center of the actual third vertex H: its original
order-two line is central by F.9.1, contradicting the proved I.5 plane-vertex
center theorem. It never substitutes centrality in the generated ambient group.

Source: Aschbacher--Smith, 13.7.6(1), printed p.940, and I.5.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.OrdinarySource.LinearThreeFamily
open Section08.SourceCompletion Quasithin.I5
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H J : Subgroup G}

def family (A J H : Subgroup G) : Fin 3 → Subgroup (A ⊔ H : Subgroup G) :=
  ![A.subgroupOf (A ⊔ H), J.subgroupOf (A ⊔ H), H.subgroupOf (A ⊔ H)]

omit [Finite G] in
theorem family_generate (A J H : Subgroup G) : (⨆ i, family A J H i) = ⊤ := by
  apply map_injective (A ⊔ H).subtype_injective
  rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, range_subtype]
  change (⨆ i, (family A J H i).map (A ⊔ H).subtype) = A ⊔ H
  apply le_antisymm (iSup_le (fun i => map_subtype_le _))
  apply sup_le
  · apply le_iSup_of_le (0 : Fin 3)
    change A ≤ (A.subgroupOf (A ⊔ H)).map (A ⊔ H).subtype
    rw [map_subgroupOf_eq_of_le le_sup_left]
  · apply le_iSup_of_le (2 : Fin 3)
    change H ≤ (H.subgroupOf (A ⊔ H)).map (A ⊔ H).subtype
    rw [map_subgroupOf_eq_of_le le_sup_right]

omit [Finite G] in
theorem family_sylow (A J H : Subgroup G) (hTA : (T : Subgroup G) ≤ A)
    (hc : chamberSubgroup (family A J H) = (T : Subgroup G).subgroupOf (A ⊔ H)) :
    ∀ i, ∃ S : Sylow 2 (family A J H i),
      (S : Subgroup (family A J H i)) =
        (chamberSubgroup (family A J H)).subgroupOf (family A J H i) := by
  intro i
  let R : Sylow 2 (A ⊔ H : Subgroup G) := T.subtype (hTA.trans le_sup_left)
  have ht : (R : Subgroup (A ⊔ H : Subgroup G)) ≤ family A J H i := by
    rw [Sylow.coe_subtype, ← hc]
    exact iInf_le _ i
  exact ⟨R.subtype ht, by rw [Sylow.coe_subtype, hc]; rfl⟩

omit [Finite G] in
theorem family_core_free (A J H : Subgroup G) (hTA : (T : Subgroup G) ≤ A)
    (hc : chamberSubgroup (family A J H) = (T : Subgroup G).subgroupOf (A ⊔ H))
    (hcore : pCore 2 (A ⊔ H : Subgroup G) = ⊥) :
    (chamberSubgroup (family A J H)).normalCore = ⊥ := by
  have hp : IsPGroup 2 (chamberSubgroup (family A J H)) := by
    rw [hc]
    exact (T.subtype (hTA.trans le_sup_left)).isPGroup'
  apply le_bot_iff.mp
  rw [← hcore]
  exact le_sSup ⟨inferInstance, hp.to_le (chamberSubgroup (family A J H)).normalCore_le⟩

theorem source_third_center_nontrivial
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis) :
    center H ≠ ⊥ := by
  obtain ⟨v,hv,_⟩ := (Nat.card_eq_two_iff' (1 : V₁)).mp d.line_card
  have hVH : V₁ ≤ H := d.line_le_plane.trans (d.plane_le_seed.trans
    (d.seed_le.trans (d.chosen.le_sylow.trans h.T_le_H)))
  let z : H := ⟨v,hVH v.property⟩
  have hz : z ∈ center H := by
    rw [mem_center_iff]
    intro a
    apply Subtype.ext
    exact (mem_centralizer_iff.mp (h.H_centralizes a.property) v v.property).symm
  intro he
  rw [he,mem_bot] at hz
  exact hv (Subtype.ext (congrArg (fun a : H => (a : G)) hz))

theorem source_false_of_C3_system
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (S : DSystem .C3 ((L ⊔ (T : Subgroup G)) ⊔ H : Subgroup G))
    (hthird : S.family 2 = H.subgroupOf ((L ⊔ (T : Subgroup G)) ⊔ H)) : False := by
  exact source_third_center_nontrivial d h
    (Quasithin.I5.C3Recognition.original_plane_vertex_center_eq_bot _ H le_sup_right S hthird)

/-- Assemble only the remaining local residues; the ambient and numerical source
conditions are discharged from the literal original setup. -/
noncomputable def source_system
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hJ : J ≤ (L ⊔ (T : Subgroup G)) ⊔ H)
    (hc : chamberSubgroup (family (L ⊔ (T : Subgroup G)) J H) =
      (T : Subgroup G).subgroupOf ((L ⊔ (T : Subgroup G)) ⊔ H))
    (eJ : (J ⧸ pCore 2 J) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (eH : (H ⧸ pCore 2 H) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))
    (hpoint : let F := family (L ⊔ (T : Subgroup G)) J H
      RankTwoParabolics (F 0) ((chamberSubgroup F).subgroupOf (F 0))
        (localParabolic F 0 1) (localParabolic F 0 2))
    (hline : let F := family (L ⊔ (T : Subgroup G)) J H
      RankTwoParabolics (F 1) ((chamberSubgroup F).subgroupOf (F 1))
        (localParabolic F 1 0) (localParabolic F 1 2))
    (hplane : let F := family (L ⊔ (T : Subgroup G)) J H
      RankTwoParabolics (F 2) ((chamberSubgroup F).subgroupOf (F 2))
        (localParabolic F 2 0) (localParabolic F 2 1)) :
    DSystem .C3 ((L ⊔ (T : Subgroup G)) ⊔ H : Subgroup G) := by
  let A := L ⊔ (T : Subgroup G)
  let F := family A J H
  let e0 : F 0 ≃* A := subgroupOfEquivOfLe le_sup_left
  let e1 : F 1 ≃* J := subgroupOfEquivOfLe hJ
  let e2 : F 2 ≃* H := subgroupOfEquivOfLe le_sup_right
  have hlarge : 32 < Nat.card (pCore 2 (F 0)) := by
    have hc0 : Nat.card (pCore 2 (F 0)) = Nat.card (pCore 2 A) := by
      rw [← pCore_map_iso 2 e0, card_map_of_injective e0.injective]
    have hcA : Nat.card (A.pCoreIn 2) = Nat.card (pCore 2 A) :=
      card_map_of_injective A.subtype_injective
    rw [hc0, ← hcA]
    exact source_large_core d h hU hV
  exact {
    family := F
    finite_vertex := fun _ => inferInstance
    point_A3 := fun he => nomatch he
    point_C3 := fun _ => Or.inr ⟨(QuotientGroup.congr _ _ e0 (pCore_map_iso 2 e0)).trans
      (nonabelian_quotient_equiv d h hU hV)⟩
    line_quotient := ⟨(QuotientGroup.congr _ _ e1 (pCore_map_iso 2 e1)).trans eJ⟩
    plane_quotient := ⟨(QuotientGroup.congr _ _ e2 (pCore_map_iso 2 e2)).trans eH⟩
    sylow := family_sylow A J H le_sup_right hc
    point_parabolics := hpoint
    line_parabolics := hline
    plane_parabolics := hplane
    generate := family_generate A J H
    core_free := family_core_free A J H le_sup_right hc h.generated_core
    nondegenerate := fun _ => Or.inr hlarge }

end CFSG.Quasithin.Chapter13.Section07.OrdinarySource.LinearThreeFamily
