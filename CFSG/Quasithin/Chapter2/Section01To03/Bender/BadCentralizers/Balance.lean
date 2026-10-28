module

public import CFSG.Quasithin.Chapter2.Section01To03.Bender.BadCentralizers.LocalSetup

/-!
# The ordinary balance application in the Bender argument

The universal earlier-source I.3.1(1),(2) implication supplies an ordinary
component J whose involution orbit contains the selected component. The
proved uniform U-normalization makes that orbit equal J. Proper-K applies
to the actual involution centralizer; no swapped-pair quotient theorem or
rank-three refinement of balance is used.

The input remains with qt-i-03-l-balance and qt-i-03, and the Bender parent
retains its final discharge. Source: Proposition 2.2.2, printed p.520,
and Lemma I.3.1, printed pp.414--415.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter2.BenderFusion
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M : Subgroup G}

namespace BadCentralizers

universe v

/-- The ordinary-component projection of the universal earlier-source
I.3.1(1),(2). Its producer is qt-i-03-l-balance / qt-i-03, and the Bender
parent must supply it. The component orbit is retained in the conclusion;
containment in one component is proved only in the application below. -/
@[expose] def OrdinaryBalance13 (C : GroupClass.{v}) : Prop :=
  ∀ (H : Type v) [Group H] [Finite H], IsKGroup C H → pPrimeCore 2 H = ⊥ →
    ∀ (t : H), orderOf t = 2 →
      ∀ (D : Subgroup H), IsComponentIn D (centralizer ({t} : Set H)) →
        ∃ J : Subgroup H, IsComponent H J ∧ D ≤ componentOrbit J (zpowers t)

private theorem componentOrbit_eq_of_normalizes {H : Type*} [Group H]
    (J A : Subgroup H) (hn : A ≤ normalizer (J : Set H)) : componentOrbit J A = J :=
  le_antisymm (iSup_conjugates_le_of_le_normalizer J A J le_rfl hn) (le_componentOrbit J A)

end BadCentralizers

/-- The genuine universal ordinary balance input gives exactly the
centralizer containment consumed by maximal-component geometry. Proper-K
is used for C_G(v), and the orbit is collapsed by proved U-normalization. -/
theorem LocalControlWitness.balance_at_maximal_bad_component
    (w : LocalControlWitness T M) {C : GroupClass} (hG : IsSimpleQTKE C G)
    (hM : HasCharacteristicTwo M)
    (hbad : ∃ u ∈ w.U, u ≠ 1 ∧ ¬ centralizer ({u} : Set G) ≤ M)
    (source13 : BadCentralizers.OrdinaryBalance13 C)
    {L : Subgroup G} (hmax : Maximal (fun K => K ∈ badCentralizerComponents w) L)
    {v : G} (hv : v ∈ componentFixedSubgroup w L) (hv1 : v ≠ 1) :
    ∃ J : Subgroup G, IsComponentIn J (centralizer ({v} : Set G)) ∧ L ≤ J := by
  let : IsElementaryAbelian 2 w.U := w.elementary
  let : IsSimpleGroup G := hG.simple
  let H := centralizer ({v} : Set G)
  have hHproper : H ≠ ⊤ := by
    intro he
    have hvZ : v ∈ center G := by
      apply mem_center_iff.mpr
      intro x
      have hxH : x ∈ H := he.symm ▸ mem_top x
      exact mem_centralizer_singleton_iff.mp hxH
    have hZ : center G = ⊥ := by
      rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with hb | ht
      · exact hb
      · exact (hG.nonabelian (center_eq_top_iff.mp ht)).elim
    exact hv1 (mem_bot.mp (hZ ▸ hvZ))
  have hK : IsKGroup C H := hG.properK H hHproper
  have hcore : pPrimeCore 2 H = ⊥ := w.oddCore_element_centralizer_eq_bot hM hbad hv.1
  obtain ⟨u, hu, hu1, hL⟩ := hmax.1.2
  have huH : u ∈ H := w.le_element_centralizer hv.1 hu
  let t : H := ⟨u, huH⟩
  have ht : orderOf t = 2 := orderOf_eq_prime
    (Subtype.ext (elemPow_eq_one_of_isElementaryAbelian u hu))
    (fun he => hu1 (congrArg Subtype.val he))
  have hLH : L ≤ H := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr (hv.2 x hx)
  let D := L.subgroupOf H
  have hDC : D ≤ centralizer ({t} : Set H) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (Subtype.ext (mem_centralizer_singleton_iff.mp (hL.1 hx)))
  let f : centralizer ({t} : Set H) →* centralizer ({u} : Set G) :=
    { toFun := fun x => ⟨((x : H) : G),
        mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property))⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hD : IsComponentIn D (centralizer ({t} : Set H)) := by
    refine ⟨hDC, ?_, ?_⟩
    · exact hL.2.1.comap f
    · let : IsQuasisimple L := hL.quasisimple
      let : IsQuasisimple D := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hLH).symm
      exact IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hDC).symm
  obtain ⟨J, hJ, hDJ⟩ := source13 H hK hcore t ht D hD
  let JG := J.map H.subtype
  have hJG : IsComponentIn JG H := by
    have hJH : JG ≤ H := map_subtype_le _
    have he : JG.subgroupOf H = J := by
      apply map_injective H.subtype_injective
      exact map_subgroupOf_eq_of_le hJH
    exact ⟨hJH, he.symm ▸ hJ⟩
  have hUN : w.U ≤ normalizer (JG : Set G) :=
    w.normalizes_all_element_centralizer_components hM hbad hv.1 JG hJG
  have hmem (x : H) : (x : G) ∈ JG ↔ x ∈ J := by
    constructor
    · rintro ⟨y, hy, he⟩
      exact (Subtype.ext he : y = x) ▸ hy
    · exact mem_map_of_mem H.subtype
  have htN : t ∈ normalizer (J : Set H) := by
    apply mem_normalizer_iff.mpr
    intro x
    exact (hmem x).symm.trans
      (((mem_normalizer_iff.mp (hUN hu) (x : G))).trans (hmem (t * x * t⁻¹)))
  have hOrbit : componentOrbit J (zpowers t) = J :=
    BadCentralizers.componentOrbit_eq_of_normalizes J (zpowers t) (zpowers_le.mpr htN)
  refine ⟨JG, hJG, ?_⟩
  rw [hOrbit] at hDJ
  have hh := map_mono (f := H.subtype) hDJ
  change (L.subgroupOf H).map H.subtype ≤ J.map H.subtype at hh
  rw [map_subgroupOf_eq_of_le hLH] at hh
  exact hh

end CFSG.Quasithin.Chapter2.BenderFusion
