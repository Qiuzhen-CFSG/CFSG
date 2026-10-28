module

public import CFSG.Quasithin.Chapter13.Section08.LinearFour.ChiefSections
public import Theory.GroupTheory.NoncentralChiefRefinement.BinaryRestriction
public import Theory.GroupTheory.NoncentralChiefRefinement.UniqueResidualLayer
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# The conditional linear-four contradiction on H_C/V_H

Construct an H-chief series between the literal normal subgroups V_H and H_C.
The small commutator image bounds its noncentral count by one. A two-perfect
component K moving H_C/V_H rules out count zero: a central chief flag is
centralized by the two-residual. Every noncentral factor has the actual natural
four-space model, hence order sixteen. This contradicts the no-unique-four-factor
clause of 13.8.31(3). Surjectivity of the actual K-image in H/O₂(H) proves
that the same factors are K-irreducible and identifies their K-noncentral count.

The final application supplies the commutator containment from the source
centralizer chain. No chief-series witness, irreducibility, faithfulness, upper
count bound or section dimension is assumed. The earlier local setup, 13.8.32
indices and 13.8.31 obstruction remain inputs, to be discharged by their source
owners. This conditional theorem alone does not prove original13.8.28.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), printed pp.965–966.
-/

public section
open Subgroup Representation NoncentralChiefRefinement
open BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
variable {G : Type*} [Group G] [Finite G]

private theorem count_ne_zero_of_component_moves
    (H HC VH K : Subgroup G) (hKH : K ≤ H) (hK : IsPPerfect 2 K)
    (hmove : ¬ ⁅HC, K⁆ ≤ VH)
    (s : ChiefSeries H) (hp : IsPGroup 2 s.last.val)
    (hhead : s.head.val.map H.subtype = VH)
    (hlast : s.last.val.map H.subtype = HC) : s.noncentralTwoCount ≠ 0 := by
  intro hz
  have hh := s.residual_commutator_le_head_of_count_zero hp hz
  have hh' := map_mono (f := H.subtype) hh
  rw [map_commutator, hhead, hlast] at hh'
  have hk := le_pResidual_of_isPPerfect (K.subgroupOf H)
    (hK.of_surjective (subgroupOfEquivOfLe hKH).symm.toMonoidHom
      (subgroupOfEquivOfLe hKH).symm.surjective)
  have hk' := map_mono (f := H.subtype) hk
  rw [map_subgroupOf_eq_of_le hKH] at hk'
  exact hmove ((commutator_mono le_rfl hk').trans hh')

/-- The endgame contradiction, conditional only on the earlier source geometry
and the 13.8.31(3) obstruction on literal K-irreducible sections. -/
theorem linear_four_exclusion_of_chief_obstruction
    (H QH HC VH Uγ K : Subgroup G) [IsElementaryAbelian 2 Uγ]
    (hQH : QH = H.pCoreIn 2) (hVC : VH ≤ HC) (hCQ : HC ≤ QH)
    (hHC : H ≤ normalizer (HC : Set G)) (hVH : H ≤ normalizer (VH : Set G))
    (hU : Nat.card Uγ = 32) (hstar : QH.relIndex Uγ = 2)
    (hintersection : 8 ≤ Nat.card (Uγ ⊓ VH : Subgroup G))
    (hcomm : ⁅HC, Uγ⁆ ≤ HC ⊓ Uγ) (hUH : Uγ ≤ H)
    (hcover : IsSQTK KnownSimple.IsKnownSimple H)
    (e : (H ⧸ pCore 2 H) ≃* LinearGroup 4)
    (hKH : K ≤ H) (hK : IsPPerfect 2 K) (hmove : ¬ ⁅HC, K⁆ ≤ VH)
    (hKonto : Function.Surjective
      ((QuotientGroup.mk' (pCore 2 H)).comp (K.subgroupOf H).subtype))
    (hnotfour : ∀ s : ChiefSeries H,
      s.head.val.map H.subtype = VH → s.last.val.map H.subtype = HC →
      (∀ i : Fin s.length, ∀ D : Subgroup (Section (s i.castSucc) (s i.succ)),
        (∀ k : K.subgroupOf H, ∀ x, x ∈ D →
          sectionAction (s i.castSucc) (s i.succ) k x ∈ D) → D = ⊥ ∨ D = ⊤) →
      s.restrictedNoncentralCount (K.subgroupOf H) = 1 → ∀ i : Fin s.length,
        (¬ ∀ k : K.subgroupOf H, ∀ x,
          sectionAction (s i.castSucc) (s i.succ) k x = x) →
          Nat.card (Section (s i.castSucc) (s i.succ)) ≠ 16) : False := by
  have hQHle : QH ≤ H := by rw [hQH]; exact pCoreIn_le 2 H
  have hCH : HC ≤ H := hCQ.trans hQHle
  have hVH' : VH ≤ H := hVC.trans hCH
  let nc : (HC.subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hCH).mpr hHC
  let nv : (VH.subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hVH').mpr hVH
  let nvc : (VH.subgroupOf HC).Normal :=
    (normal_subgroupOf_iff_le_normalizer hVC).mpr (hCH.trans hVH)
  obtain ⟨s, hs0, hs1⟩ := exists_chiefSeries
    (⟨VH.subgroupOf H, nv⟩ : NormalNode H) (⟨HC.subgroupOf H, nc⟩ : NormalNode H)
    (subgroupOf_mono H hVC)
  have hhead : s.head.val.map H.subtype = VH := by
    rw [hs0]
    exact map_subgroupOf_eq_of_le hVH'
  have hlast : s.last.val.map H.subtype = HC := by
    rw [hs1]
    exact map_subgroupOf_eq_of_le hCH
  have hupper := chief_series_noncentral_count_le_one H QH HC VH Uγ
    hQH hVC hCQ hU hstar hintersection hcomm hUH e s hhead hlast
  have hp : IsPGroup 2 s.last.val := by
    apply (pCore_isPGroup (p := 2) (G := H)).to_le
    intro x hx
    have hm : (x : G) ∈ QH := hCQ (hlast ▸ mem_map_of_mem H.subtype hx)
    rw [hQH] at hm
    exact (mem_map_iff_mem H.subtype_injective).mp hm
  have hn := count_ne_zero_of_component_moves H HC VH K hKH hK hmove s hp hhead hlast
  have hone : s.noncentralTwoCount = 1 := by omega
  have hex : Nonempty {i : Fin s.length // IsNoncentralTwo (s i.castSucc) (s i.succ)} :=
    Finite.card_pos_iff.mp (show 0 < s.noncentralTwoCount by omega)
  obtain ⟨⟨i, hi⟩⟩ := hex
  have hpi (j : Fin s.length) : IsPGroup 2 (s j.succ).val :=
    hp.to_le (CompositionSeries.le_last j.succ)
  have hchiefK := fun j => chief_restricted_irreducible _ _ (s.step j) (hpi j)
    (K.subgroupOf H) hKonto
  have hcountK : s.restrictedNoncentralCount (K.subgroupOf H) = 1 :=
    (s.restrictedNoncentralCount_eq hp _ hKonto).trans hone
  have hiK : ¬ ∀ k : K.subgroupOf H, ∀ x,
      sectionAction (s i.castSucc) (s i.succ) k x = x := by
    exact fun hh => hi.2 ((chief_restricted_central_iff _ _ (s.step i)
      (hpi i) _ hKonto).mpr hh)
  apply hnotfour s hhead hlast hchiefK hcountK i hiK
  apply chief_section_card_sixteen H QH HC VH Uγ hQH hCQ hU hstar
    hintersection hcomm hUH hcover e _ _ (s.step i) hi.2
  · rw [← hhead]
    exact map_mono (CompositionSeries.head_le i.castSucc)
  · rw [← hlast]
    exact map_mono (CompositionSeries.le_last i.succ)

/-- The actual centralizer and intersection inputs on pp.965–966 imply the
linear-four contradiction, once the earlier 13.8.31 source obstruction is supplied. -/
theorem source_linear_four_exclusion
    (H Q QH HC V3 V VH R A1 Uγ Gγ K : Subgroup G)
    [IsElementaryAbelian 2 Uγ]
    (hQH : QH = H.pCoreIn 2) (hVC : VH ≤ HC)
    (hQR : QH ≤ R) (hindex : Q.relIndex R = 4)
    (hcent : Q ⊓ QH ≤ centralizer (V3 : Set G))
    (hdual : (QH ⊓ centralizer (V3 : Set G)).relIndex QH = 4)
    (hHCQH : HC ≤ QH) (hHCV3 : HC ≤ centralizer (V3 : Set G))
    (hHHC : H ≤ normalizer (HC : Set G))
    (hQV : Q ≤ centralizer (V : Set G))
    (hVH : VH = conjugateSpanBy V H) (hA1 : A1 ≤ VH)
    (hGγ : Gγ = centralizer (A1 : Set G))
    (hGγUγ : Gγ ≤ normalizer (Uγ : Set G)) (hUγH : Uγ ≤ H)
    (hU : Nat.card Uγ = 32) (hstar : QH.relIndex Uγ = 2)
    (hintersection : 8 ≤ Nat.card (Uγ ⊓ VH : Subgroup G))
    (hcover : IsSQTK KnownSimple.IsKnownSimple H)
    (e : (H ⧸ pCore 2 H) ≃* LinearGroup 4)
    (hKH : K ≤ H) (hK : IsPPerfect 2 K) (hmove : ¬ ⁅HC, K⁆ ≤ VH)
    (hKonto : Function.Surjective
      ((QuotientGroup.mk' (pCore 2 H)).comp (K.subgroupOf H).subtype))
    (hnotfour : ∀ s : ChiefSeries H,
      s.head.val.map H.subtype = VH → s.last.val.map H.subtype = HC →
      (∀ i : Fin s.length, ∀ D : Subgroup (Section (s i.castSucc) (s i.succ)),
        (∀ k : K.subgroupOf H, ∀ x, x ∈ D →
          sectionAction (s i.castSucc) (s i.succ) k x ∈ D) → D = ⊥ ∨ D = ⊤) →
      s.restrictedNoncentralCount (K.subgroupOf H) = 1 → ∀ i : Fin s.length,
        (¬ ∀ k : K.subgroupOf H, ∀ x,
          sectionAction (s i.castSucc) (s i.succ) k x = x) →
          Nat.card (Section (s i.castSucc) (s i.succ)) ≠ 16) : False := by
  obtain ⟨_, _, _, hc⟩ := final_centralizer_chain H Q QH HC V3 V VH R A1 Uγ Gγ
    hQR hindex hcent hdual hHCQH hHCV3 hHHC hQV hVH hA1 hGγ hGγUγ hUγH
  have hHV : H ≤ normalizer (VH : Set G) := by
    rw [hVH]
    exact le_normalizer_conjugateSpanBy V H
  exact linear_four_exclusion_of_chief_obstruction H QH HC VH Uγ K hQH hVC hHCQH
    hHHC hHV hU hstar hintersection hc hUγH hcover e hKH hK hmove hKonto hnotfour

end CFSG.Quasithin.Chapter13.Section08.LinearFour
