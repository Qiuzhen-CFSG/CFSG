module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.FirstResidual
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.EightSylow
public import Theory.GroupTheory.CComponent.LocalImageEquality

/-!
# The normal first component in the original triality centralizer

The literal inclusion into Mc/O₂(Mc) identifies the first endpoint's image
with PSL₂(8). The already identified elementary Sylow has order eight, so
the A.3.12 non-enlargement argument identifies the containing component
with H itself. The earlier unique-containment result therefore makes H
normal in Mc. Characteristicity of O₂(H) then gives N_G(H) = Mc.
Frattini's argument and the original N_G(T) placement give
Mc = H join (M intersect Mc), retaining the full original overlap.

Source: Aschbacher--Smith 14.2.18, printed p.987. The marked triality
amalgam is the explicit earlier 14.2.16 input. The cubic field extension
and ambient recognition remain with the same source-family owner;
this module does not equate Mc with H. The literal terminal application
is `TerminalSolvable/EightBorelComponent.lean`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
open ChapterA.Section03.SourceEmbeddings.EightSylow
variable {G : Type*} [Group G] [Finite G]
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {T : Sylow 2 G} {M Mc H : Subgroup G}
variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
include hG hempty hM hu hmany hcard e hH

/-- Original 14.2.18: the first endpoint is the containing C-component,
and is normal in Mc. This is relative normality in the centralizer. -/
theorem source_first_normal_component (r : MarkedTriality T M Mc H) :
    (H.subgroupOf Mc).IsCComponent ∧ (H.subgroupOf Mc).Normal := by
  have hHM := source_first_le_partner hG hempty hM hu hmany hcard e hH
  have hTM := hH.1.1.2.trans hHM
  let S := T.subtype hTM
  let B := H.subgroupOf Mc
  have hB : B ∈ Chapter1.L Mc S :=
    (Chapter1.mem_LIn_iff_subgroupOf hTM hHM).mp
      (source_first_mem_local_family hG hempty hM hu hmany hcard e hH r)
  obtain ⟨C,⟨hC,hBC,hCN⟩,_⟩ :=
    source_first_normal_containing_component hG hempty hM hu hmany hcard e hH r
  let q := QuotientGroup.mk' (pCore 2 Mc)
  let f := q.comp (inclusion hHM)
  have hfker : f.ker = pCore 2 H := by
    change (QuotientGroup.mk' (pCore 2 Mc)).ker.comap (inclusion hHM) = _
    rw [QuotientGroup.ker_mk']
    exact source_first_core_comap hG hempty hM hu hmany hcard e hH r
  have hfrange : f.range = B.map q := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact ⟨inclusion hHM y,y.property,rfl⟩
    · rintro ⟨y,hy,rfl⟩
      exact ⟨⟨y,hy⟩,rfl⟩
  let a : B.map q ≃* Theory.PSL2.BinaryGroup 3 :=
    (MulEquiv.subgroupCongr hfrange.symm).trans
      ((QuotientGroup.quotientKerEquivRange f).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hfker).trans (firstQuotientEquiv r)))
  have huMc : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
  have hQ := ChapterE.Structure.sqtk_two_quotient (hG.twoLocal_sqtk huMc.1.1)
    (pCore 2 Mc) pCore_isPGroup
  have hSm : Nat.card (S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 Mc))) ≤ 8 :=
    (source_partner_quotient_sylow hG hempty hM hu hmany hcard e hH r).2.le
  let : Group.IsNilpotent (pCore 2 Mc) := pCore_isNilpotent
  have himg : B.map q = C.map q :=
    containing_eq_of_eight_section hQ (pCore_quotient_pCore_eq_bot 2)
      (S.mapSurjective (QuotientGroup.mk'_surjective _)) hSm
      (Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hB)
      (hC.map_quotient _) (map_mono hBC) a
  have he : B = C := local_cComponent_eq_of_map_eq hB.1 hC hBC q
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup.le_sylow_of_normal S) himg
  change B.IsCComponent ∧ B.Normal
  rw [he]
  exact ⟨hC,hCN⟩

/-- The original partner normalizes the original first subgroup. -/
theorem source_partner_le_first_normalizer (r : MarkedTriality T M Mc H) :
    Mc ≤ normalizer (H : Set G) :=
  (normal_subgroupOf_iff_le_normalizer
    (source_first_le_partner hG hempty hM hu hmany hcard e hH)).mp
      (source_first_normal_component hG hempty hM hu hmany hcard e hH r).2




/-- The source partner is the full ambient normalizer of the first component. -/
theorem source_first_normalizer_eq (r : MarkedTriality T M Mc H) :
    normalizer (H : Set G) = Mc := by
  apply le_antisymm ?_ (source_partner_le_first_normalizer hG hempty hM hu hmany hcard e hH r)
  exact (normalizer_le_normalizer_characteristic_image H (pCore 2 H)).trans
    (source_firstCore_normalizer_eq hG hempty hM hu hmany hcard e hH r).le

/-- Frattini's argument puts every possible extension of the first component
in the original overlap with M. The full odd Borel factor is retained. -/
theorem source_partner_factorization (r : MarkedTriality T M Mc H) :
    Mc = H ⊔ (M ⊓ Mc) := by
  have hHM := source_first_le_partner hG hempty hM hu hmany hcard e hH
  have hTM := hH.1.1.2.trans hHM
  let S := T.subtype hTM
  let B := H.subgroupOf Mc
  let : B.Normal := (source_first_normal_component hG hempty hM hu hmany hcard e hH r).2
  have hSB : (S : Subgroup Mc) ≤ B := comap_mono hH.1.1.2
  have ht := S.normalizer_sup_eq_top' hSB
  have hN : normalizer (S : Set Mc) ≤ (M ⊓ Mc).subgroupOf Mc := by
    intro x hx
    have hx' : (x : G) ∈ normalizer (T : Set G) := by
      change x ∈ normalizer ((T : Subgroup G).subgroupOf Mc : Set Mc) at hx
      rw [← subgroupOf_normalizer_eq hTM] at hx
      exact hx
    exact source_lemma_14_2_2_7 hG T hempty hM hu hmany hcard e hx'
  apply le_antisymm ?_ (sup_le hHM inf_le_right)
  have hh : (⊤ : Subgroup Mc) ≤ (H ⊔ (M ⊓ Mc)).subgroupOf Mc := by
    rw [←ht]
    exact sup_le (hN.trans (comap_mono le_sup_right)) (comap_mono le_sup_left)
  intro x hx
  exact hh (show (⟨x,hx⟩ : Mc) ∈ (⊤ : Subgroup Mc) from mem_top _)

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
