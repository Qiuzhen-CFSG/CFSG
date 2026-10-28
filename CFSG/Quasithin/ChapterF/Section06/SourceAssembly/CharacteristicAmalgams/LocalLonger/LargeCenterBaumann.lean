module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.CharacteristicAmalgams.LocalRankOne
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.CharacteristicAmalgams.Baumann
public import Theory.GroupTheory.CenterFreeCubicBaumann
public import Stellmacher.BaumannMap

/-!
# Baumann selection from a large cubic critical center

For a commuting critical path in a characteristic-two Goldschmidt triple,
the initial vertex is centerless and its center module is elementary and
centralized by its two-core. If that module has order greater than four,
the cubic maximal-elementary argument places the common Sylow Baumann
subgroup in the initial core. Faithfulness and Baumann heredity then force
it outside the next core. Sylow conjugacy retains this noncontainment for
any actual Sylow of the selected next edge.

This discharges the selected-Baumann premise in the second extraction of
Stellmacher (9.3), p.49, directly from the cubic hypotheses, without the
ambient version of (6.1).
-/

public section
open Subgroup Theory.GroupTheory
open Stellmacher Stellmacher.SectionsFiveToSeven Stellmacher.Later
open Stellmacher.SectionsFiveToSeven.CosetGraphContext
open Stellmacher.SectionsFiveToSeven.SevenSix
namespace CFSG.Quasithin.ChapterF
universe u
variable {G : Type u} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

private theorem sylow_baumann_core_transfer
    {G : Type u} [Group G] [Finite G] (U V : Sylow 2 G)
    (hU : baumannIn (U : Subgroup G) ≤ pCore 2 G) :
    baumannIn (V : Subgroup G) ≤ pCore 2 G := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G U V
  have hV : (V : Subgroup G) = (U : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [← hg,Sylow.coe_subgroup_smul,Subgroup.pointwise_smul_def]
    congr 1
  have hBm : (baumannIn (U : Subgroup G)).map (MulAut.conj g).toMonoidHom =
      baumannIn (V : Subgroup G) := by
    rw [hV]
    exact baumann_map_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective _
  rw [← hBm]
  rintro a ⟨u,hu,rfl⟩
  exact (inferInstance : (pCore 2 G).Normal).conj_mem u (hU hu) g


theorem IsGoldschmidtTriple.critical_baumann_le_initial_core_of_large_center
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hgood₁ : generalizedFitting G₁ = pCore 2 G₁)
    (hgood₂ : generalizedFitting G₂ = pCore 2 G₂)
    (Γ : CosetGraphContext.{u,u} G (G₁ ⊓ G₂) G₁ G₂) (cp : CriticalPath Γ)
    (hcomm : ⁅z Γ cp.a,z Γ cp.a'⁆ = ⊥)
    (hlarge : 4 < Nat.card (ZAt Γ cp.a)) :
    baumannIn (G₁ ⊓ G₂) ≤ QAt Γ cp.a := by
  have h7 := h.sectionSeven_of_characteristic_two hcore hgood₁ hgood₂
  let P := stabilizer Γ cp.a
  let V := (ZAt Γ cp.a).subgroupOf P
  have hTP : G₁ ⊓ G₂ ≤ P := cp.S_le_edge_stabilizers.trans inf_le_left
  obtain ⟨_,S,hS⟩ := (SevenSix.edge_sylow_data h7 Γ cp).1
  have hS' : (S : Subgroup P) = (G₁ ⊓ G₂).subgroupOf P := by
    apply map_injective P.subtype_injective
    rw [map_subgroupOf_eq_of_le hTP]
    exact hS
  have hZP : ZAt Γ cp.a ≤ P := by
    exact (lemma_seven_three h7 Γ).center_core cp.a cp.firstStep
      ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj) |>.trans
      (SevenSix.omegaOneCenter_le_centerAmbient (q Γ cp.a)) |>.trans
      ((map_subtype_le (center (q Γ cp.a))).trans (by
        rw [q, Γ.twoCoreAt_def]
        exact map_subtype_le _))
  have hVnorm : V.Normal := (normal_subgroupOf_iff_le_normalizer hZP).mpr
    (stabilizer_le_normalizer_z Γ cp.a)
  let := hVnorm
  have he : Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) := by
    rcases cp.edge_stabilizers_are_P with he | he
    · rw [show P = G₁ from he.1]
      exact h.quotient_left
    · rw [show P = G₂ from he.1]
      exact h.quotient_right
  have hc : center P = ⊥ := (lemma_seven_five h7 Γ cp hcomm).start_center_trivial
  have hQ : (pCore 2 P).map P.subtype = QAt Γ cp.a := by
    exact (Γ.twoCoreAt_def cp.a).symm
  have hVQ : V ≤ centralizer (pCore 2 P : Set P) := by
    intro x hx y hy
    apply Subtype.ext
    have hz := (lemma_seven_four h7 Γ cp).edge_centralizer
    have hyQ : (y : G) ∈ q Γ cp.a := by
      change (y : G) ∈ QAt Γ cp.a
      rw [← hQ]
      exact mem_map_of_mem P.subtype hy
    rw [← hz] at hyQ
    exact hyQ.2 (x : G) hx |>.symm
  have hZQ : ZAt Γ cp.a ≤ q Γ cp.a :=
    ((lemma_seven_three h7 Γ).center_core cp.a cp.firstStep
      ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj)).trans
      ((SevenSix.omegaOneCenter_le_centerAmbient _).trans (map_subtype_le _))
  have hVS : V ≤ (S : Subgroup P) := by
    rw [hS']
    intro x hx
    exact (hZQ.trans (SevenSix.local_cores_le_edge_sylow h7 Γ cp).1) hx
  let hZE : IsElementaryAbelian 2 (ZAt Γ cp.a) := SevenSix.z_isElementaryAbelian_of_neighbor h7 Γ
    ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj)
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.subgroupOf hZP
  have hlargeV : 4 < Nat.card V := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hZP).toEquiv]
  have hb := SymmetricThreeTwoCore.baumann_le_core_of_large_elementary he.some S V
    hVS hc hVQ hlargeV
  have hmapped := map_mono (f := P.subtype) hb
  rw [baumann_map_injective P.subtype P.subtype_injective, hS, hQ] at hmapped
  exact hmapped

/-- The exact noncontainment selecting the second actor in the large-center branch of (9.3). -/
theorem IsGoldschmidtTriple.critical_baumann_not_le_next_core_of_large_center
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hgood₁ : generalizedFitting G₁ = pCore 2 G₁)
    (hgood₂ : generalizedFitting G₂ = pCore 2 G₂)
    (Γ : CosetGraphContext.{u,u} G (G₁ ⊓ G₂) G₁ G₂) (cp : CriticalPath Γ)
    (hcomm : ⁅z Γ cp.a,z Γ cp.a'⁆ = ⊥)
    (hlarge : 4 < Nat.card (ZAt Γ cp.a)) :
    ¬ baumannIn (G₁ ⊓ G₂) ≤ QAt Γ cp.firstStep := by
  have hleft := h.critical_baumann_le_initial_core_of_large_center hcore hgood₁ hgood₂ Γ cp hcomm hlarge
  intro hright
  have hh := h.baumann_not_le_both_cores hcore
  change baumannIn (G₁ ⊓ G₂) ≤ q Γ cp.a at hleft
  change baumannIn (G₁ ⊓ G₂) ≤ q Γ cp.firstStep at hright
  rw [q, Γ.twoCoreAt_def] at hleft hright
  change baumannIn (G₁ ⊓ G₂) ≤ twoCoreIn (Γ.stabilizer cp.a) at hleft
  change baumannIn (G₁ ⊓ G₂) ≤ twoCoreIn (Γ.stabilizer cp.firstStep) at hright
  rcases cp.edge_stabilizers_are_P with he | he
  · rw [he.1] at hleft
    rw [he.2] at hright
    exact hh.elim (fun hn => hn hleft) (fun hn => hn hright)
  · rw [he.1] at hleft
    rw [he.2] at hright
    exact hh.elim (fun hn => hn hright) (fun hn => hn hleft)

/-- The large-center noncontainment for the literal selected edge Sylow. -/
theorem IsGoldschmidtTriple.critical_selected_edge_baumann_not_le_core_of_large_center
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hgood₁ : generalizedFitting G₁ = pCore 2 G₁)
    (hgood₂ : generalizedFitting G₂ = pCore 2 G₂)
    (Γ : CosetGraphContext.{u,u} G (G₁ ⊓ G₂) G₁ G₂) (cp : CriticalPath Γ)
    (hcomm : ⁅z Γ cp.a,z Γ cp.a'⁆ = ⊥)
    (hlarge : 4 < Nat.card (ZAt Γ cp.a))
    (l : Γ.Vertex) (hl : l ∈ neighborhood Γ cp.firstStep)
    (U : Sylow 2 (stabilizer Γ cp.firstStep ⊓ stabilizer Γ l : Subgroup G)) :
    ¬ baumannIn (sylowTwoAmbient (stabilizer Γ cp.firstStep ⊓ stabilizer Γ l) U) ≤
      q Γ cp.firstStep := by
  have h7 := h.sectionSeven_of_characteristic_two hcore hgood₁ hgood₂
  have hnot := h.critical_baumann_not_le_next_core_of_large_center hcore hgood₁ hgood₂ Γ cp hcomm hlarge
  let P := stabilizer Γ cp.firstStep
  let W := sylowTwoAmbient (P ⊓ stabilizer Γ l) U
  have hW : IsSylowTwoIn W P :=
    ((lemma_seven_three h7 Γ).sylow_and_core _ _ hl U).1
  obtain ⟨_,R,hR⟩ := hW
  obtain ⟨_,R0,hR0⟩ := (edge_sylow_data h7 Γ cp).2
  have hBm (V : Sylow 2 P) :
      (baumannIn (V : Subgroup P)).map P.subtype =
        baumannIn ((V : Subgroup P).map P.subtype) :=
    baumann_map_injective P.subtype P.subtype_injective _
  intro hbad
  rw [q,Γ.twoCoreAt_def] at hbad
  have hRbad : baumannIn (R : Subgroup P) ≤ pCore 2 P := by
    apply (Subgroup.map_le_map_iff_of_injective P.subtype_injective).mp
    rw [hBm,hR]
    exact hbad
  have hR0bad := sylow_baumann_core_transfer R R0 hRbad
  have hTbad : baumannIn (G₁ ⊓ G₂) ≤ twoCoreIn P := by
    have hm := Subgroup.map_mono (f := P.subtype) hR0bad
    rw [hBm,hR0] at hm
    exact hm
  apply hnot
  change baumannIn (G₁ ⊓ G₂) ≤ q Γ cp.firstStep
  rw [q, Γ.twoCoreAt_def]
  exact hTbad

end CFSG.Quasithin.ChapterF
