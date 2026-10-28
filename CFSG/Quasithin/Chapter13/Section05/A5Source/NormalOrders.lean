module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalPointStructure
public import Theory.GroupTheory.NormalizedSupConsequences
/-!
# Matched point and plane alternatives for the original normal A5 pair

The common Borel has index three in the point group and five in the plane
group. The quaternion point core and its quotient therefore determine both
endpoint orders simultaneously. The ordinary endpoint has plane group L;
the doubled endpoint has symmetric-five plane quotient. These calculations
match the point quotient models on the same original groups and supply the
full local alternatives used by the unitary-amalgam recognition step.

Source: Aschbacher–Smith 13.5.15(8), printed pp.920–921. The compatible
unitary-amalgam isomorphism of 13.5.17 remains a separate source obligation.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio Section08
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G} [IsElementaryAbelian 2 V]
  (d : Context T L V V₁ V₂ V₃)
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
  (hH : H ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
    (centralizer (V₁ : Set G)) (normalizer (L : Set G)))
  (hU : ¬ IsMulCommutative (Source.UH H V₃))
  (hn : ((residualCentralizer L V₁).subgroupOf H).Normal)
include d hA312 hH hU hn

omit hA312 hU hn [IsElementaryAbelian 2 V] in
theorem normal_plane_borel_index :
    (residualCentralizer L V₁ ⊔ (T : Subgroup G)).relIndex (L ⊔ (T : Subgroup G)) = 5 := by
  let B := residualCentralizer L V₁ ⊔ (T : Subgroup G)
  have hBL : B ≤ normalizer (L : Set G) :=
    sup_le (((map_subtype_le _).trans inf_le_left).trans L.le_normalizer) d.normalizes_L
  have hjoin : L ⊔ B = L ⊔ (T : Subgroup G) := by
    apply le_antisymm
    · exact sup_le le_sup_left (sup_le_sup ((map_subtype_le _).trans inf_le_left) le_rfl)
    · exact sup_le le_sup_left (le_sup_right.trans le_sup_right)
  have hinter : B ⊓ L = L ⊓ centralizer (V₁ : Set G) := by
    apply le_antisymm
    · exact le_inf inf_le_right (inf_le_left.trans (hH.1.2.trans hH.2.1))
    · refine le_inf ?_ inf_le_left
      rw [←d.borel_eq_point_centralizer]
      exact le_sup_left.trans d.borel_sup_sylow_eq_residual_sup_sylow.le
  change B.relIndex (L ⊔ (T : Subgroup G)) = 5
  rw [←hjoin,relIndex_sup_of_normalizes L B hBL,←inf_relIndex_right,hinter]
  exact d.point_centralizer_relIndex

theorem normal_local_card : Nat.card L = 960 := by
  obtain ⟨g,hg,hg₁⟩ := d.exists_block_conjugator
  have hc := (normal_block_consequences d hA312 hH hU hg hg₁ hn).2.1
  have hcard : Nat.card (pCore 2 L) = 16 := by
    have hh : Nat.card (L.pCoreIn 2) = Nat.card (pCore 2 L) :=
      card_map_of_injective L.subtype_injective
    rw [hc,d.module_card] at hh
    exact hh.symm
  rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 L),hcard,
    Nat.card_congr d.quotient.toEquiv,nat_card_alternatingGroup]
  norm_num

theorem normal_local_orders :
    (Nat.card H = 576 ∧
      Nat.card (residualCentralizer L V₁ ⊔ (T : Subgroup G) : Subgroup G) = 192 ∧
      Nat.card (L ⊔ (T : Subgroup G) : Subgroup G) = 960) ∨
    (Nat.card H = 1152 ∧
      Nat.card (residualCentralizer L V₁ ⊔ (T : Subgroup G) : Subgroup G) = 384 ∧
      Nat.card (L ⊔ (T : Subgroup G) : Subgroup G) = 1920) := by
  let B := residualCentralizer L V₁ ⊔ (T : Subgroup G)
  let M := L ⊔ (T : Subgroup G)
  have hBH : B ≤ H := hH.1.2
  have hBM : B ≤ M := sup_le_sup ((map_subtype_le _).trans inf_le_left) le_rfl
  have hcH := (B.subgroupOf H).card_mul_index
  have hcM := (B.subgroupOf M).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hBH).toEquiv] at hcH
  rw [Nat.card_congr (subgroupOfEquivOfLe hBM).toEquiv] at hcM
  change Nat.card B * B.relIndex H = Nat.card H at hcH
  change Nat.card B * B.relIndex M = Nat.card M at hcM
  rw [normal_local_join_index d hA312 hH hU hn] at hcH
  rw [normal_plane_borel_index d hH] at hcM
  dsimp only [B,M] at hcH hcM
  rcases normal_point_card_cases d hA312 hH hU hn with hc | hc <;> omega

private theorem plane_quotient_symmetric_of_card
    (hM : Nat.card (L ⊔ (T : Subgroup G) : Subgroup G) = 1920) :
    Nonempty (((L ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 5)) := by
  let M := L ⊔ (T : Subgroup G)
  let f := d.localActor
  have hk : f.ker = pCore 2 M := d.localActor_kernel_eq_core d.normalizes_L
  have hc : Nat.card f.ker = 16 := by
    rw [hk]
    have hh : Nat.card (M.pCoreIn 2) = Nat.card (pCore 2 M) :=
      card_map_of_injective M.subtype_injective
    rw [normal_local_core_eq_module d hA312 hH hU hn,d.module_card] at hh
    exact hh.symm
  have hr : Nat.card f.range = 120 := by
    have hh := f.ker.card_mul_index
    rw [hc,index_ker,hM] at hh
    omega
  have htop : f.range = ⊤ := eq_of_le_of_card_ge le_top (by
    rw [Nat.card_congr Subgroup.topEquiv.toEquiv,hr]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial])
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f (MonoidHom.range_eq_top.mp htop))⟩

/-- The complete matched alternatives of original 13.5.15(8), with M=LT
and the literal point and plane quotients. -/
theorem normal_source13_5_15_eight :
    Source.QH H = Source.UH H V₃ ∧
    (∃ f : Source.Hstar H →* NormalBranch.OmegaPlusFour, Function.Injective f) ∧
    (((L ⊔ (T : Subgroup G)) = L ∧
        Nonempty (Source.Hstar H ≃* Equiv.Perm (Fin 3) × Multiplicative (ZMod 3))) ∨
      (Nonempty (((L ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 5)) ∧
        Nonempty (Source.Hstar H ≃* NormalBranch.OmegaPlusFour))) := by
  refine ⟨normal_core_eq_closure d hA312 hH hU hn,
    (normal_star_embedding d hA312 hH hU hn).1,?_⟩
  obtain ⟨q,_⟩ := normal_point_core_geometry d hA312 hH hU hn
  have hc := (pCore 2 H).card_mul_index
  rw [q.card,index_eq_card] at hc
  rcases normal_local_orders d hA312 hH hU hn with ⟨hHc,_,hMc⟩ | ⟨hHc,_,hMc⟩
  · left
    have he : L ⊔ (T : Subgroup G) = L := (eq_of_le_of_card_ge le_sup_left (by
      rw [hMc,normal_local_card d hA312 hH hU hn])).symm
    refine ⟨he,?_⟩
    have h18 : Nat.card (Source.Hstar H) = 18 := by
      change Nat.card (H ⧸ pCore 2 H) = 18
      rw [hHc] at hc
      omega
    obtain ⟨e⟩ := normal_point_quotient_of_eighteen d hA312 hH hU hn h18
    exact ⟨e.trans MulEquiv.prodComm⟩
  · right
    refine ⟨plane_quotient_symmetric_of_card d hA312 hH hU hn hMc,?_⟩
    have h36 : Nat.card (Source.Hstar H) = 36 := by
      change Nat.card (H ⧸ pCore 2 H) = 36
      rw [hHc] at hc
      omega
    exact normal_point_quotient_of_thirtysix d hA312 hH hU hn h36

end CFSG.Quasithin.Chapter13.Section05.A5Source
