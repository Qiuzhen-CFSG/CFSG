module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentElevenContainment
public import Theory.GroupTheory.PResidual.CommutatorImage
public import Theory.GroupTheory.PResidual.PerfectImage
public import Theory.ThreeSubgroups

/-!
# The actual cubic commutator of the intrinsic residual core

Lift K-star = [K-star,V-star] through H → H/O₂(H), using the perfect
original component. The three-subgroups argument then gives [O₂(H),K] ≤ U_H.
For the actual P_K = P ∩ K, coprime commutator idempotence and the proved
U_H ≤ O₂(L₁) ≤ O₂(H) give [O₂(L₁),P_K] = [U_H,P_K].

Every subgroup lies in the original G; O₂(L₁) is the intrinsic core.
The following cubic module bounds this commutator. The additional identity
with the whole core still requires the source block argument.
Source: Aschbacher--Smith, proof of 12.6.26, printed p.833.
-/

public section
namespace CFSG.Quasithin.Chapter12.Section06
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
set_option backward.isDefEq.respectTransparency false
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1)
  (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
  (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)


include hH in
/-- Lift the full component commutator through the literal two-core quotient. -/
theorem SourceHypothesis.original_selectedComponent_full_commutator :
    ⁅c.K,V⁆ = c.K := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let B := c.K.subgroupOf H
  let A := V.subgroupOf H
  let := c.ccomponent.perfect
  have hVH : V ≤ H := S.chosen.le_sylow.trans (fun x hx => hH.1.2 (Or.inr hx))
  have hnorm : A ≤ normalizer (B : Set H) := by
    rw [←subgroupOf_normalizer_eq c.le_H]
    exact comap_mono (S.original_module_normalizes_selectedComponent D hZ z hH c)
  have hperf : IsPPerfect 2 B := (pResidual_eq_top_iff 2 B).mp (pResidual_eq_top_of_isPerfect 2)
  have hh := eq_commutator_of_isPPerfect_of_map_eq B A hperf hnorm q
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup) c.full_commutator.symm
  have hm := congrArg (map H.subtype) hh
  simpa only [B,A,map_commutator,map_subgroupOf_eq_of_le c.le_H,
    map_subgroupOf_eq_of_le hVH] using hm.symm

include hz hTV hTz hbound hH hn in
/-- The original component moves the full H-core only into the point span. -/
theorem SourceHypothesis.original_selectedComponent_core_commutator_le_pointSpan :
    ⁅H.pCoreIn 2,c.K⁆ ≤ (D.fullSetup hZ T z).UH H := by
  let E := D.fullSetup hZ T z
  have h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  have hHN : H ≤ normalizer (E.UH H : Set G) := le_normalizer_conjugateSpanBy _ _
  have hKN := c.le_H.trans hHN
  have hVN : V ≤ normalizer (E.UH H : Set G) := h.V_le_H.trans hHN
  have hQN := (pCoreIn_le 2 H).trans hHN
  have hKQ : c.K ≤ normalizer (H.pCoreIn 2 : Set G) := c.le_H.trans
    (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
  have hQV : ⁅H.pCoreIn 2,V⁆ ≤ E.UH H :=
    (h.core_module_commutator_le_seed (E.perpendicular_index hz)
      (E.nonabelian_inputs h (S.original_perpendicular_centralizer D hZ z hz hTV hTz hbound) hn).2.1).trans
      (le_conjugateSpanBy _ _)
  rw [commutator_comm,←S.original_selectedComponent_full_commutator D hZ z hH c]
  apply commutator_commutator_le_of_rotate_of_le_normalizer hKN hVN hQN
  · rw [commutator_comm V (H.pCoreIn 2)]
    exact (commutator_mono hQV le_rfl).trans (le_normalizer_iff_commutator_le_left.mp hKN)
  · exact (commutator_mono (le_normalizer_iff_commutator_le_left.mp hKQ) le_rfl).trans hQV

include hz hTV hTz hbound hH hn a in
/-- Coprime idempotence identifies the actual cubic commutators of the
intrinsic residual core and the original point span. -/
theorem SourceHypothesis.original_selectedComponent_cubic_core_commutator
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (P : Sylow 3 (D.fullSetup hZ T z).L₁) :
    let E := D.fullSetup hZ T z
    let PK := ((P : Subgroup E.L₁).map E.L₁.subtype) ⊓ c.K
    ⁅E.L₁.pCoreIn 2,PK⁆ = ⁅E.UH H,PK⁆ := by
  let E := D.fullSetup hZ T z
  let PK := ((P : Subgroup E.L₁).map E.L₁.subtype) ⊓ c.K
  let R := E.L₁.pCoreIn 2
  have hPK : IsPGroup 3 PK := (P.isPGroup'.map E.L₁.subtype).to_le inf_le_left
  have hcop := IsPGroup.coprime_card_of_ne 3 2 (by decide) PK R hPK (isPGroup_pCoreIn 2 E.L₁)
  have hPN : PK ≤ normalizer (R : Set G) :=
    (inf_le_left.trans (map_subtype_le _)).trans (E.L₁.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image E.L₁ (pCore 2 E.L₁)))
  have hid := commutator_closure_coprime_idempotent R (PK : Set G)
    (by simpa only [closure_eq] using hPN)
    (fun x hx => hcop.of_dvd_left (PK.orderOf_dvd_natCard hx))
  simp only [closure_eq] at hid
  have hRU : ⁅R,PK⁆ ≤ E.UH H :=
    (commutator_mono (S.original_selectedComponent_residual_core_le D hZ z hz hTV hTz hbound hH hn c a hTI hns)
      inf_le_right).trans
      (S.original_selectedComponent_core_commutator_le_pointSpan D hZ z hz hTV hTz hbound hH hn c)
  apply le_antisymm
  · exact hid.ge.trans (commutator_mono hRU le_rfl)
  · exact commutator_mono (S.original_selectedComponent_pointSpan_le_residual_core
      D hZ z hz hTV hTz hbound hH hn c a hTI hns) le_rfl

end CFSG.Quasithin.Chapter12.Section06
