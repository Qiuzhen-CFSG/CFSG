module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.CentralFactors.Construction
public import Theory.SpecificGroups.Alternating.FiveBorelCentralFactor

/-!
# Field-four Borel calculations for the exceptional central factors

The actual PSL₂(4) ≃ A₅ comparison identifies the Borel action and places
C_{K*D*}(K*) inside D*. This discharges the placement premise in the
centralizer-factor construction and identifies its literal star image.

Independently, the source bound [L₀,t] ≤ O₂(L₀) is transported through
H/O₂(H), with each two-core embedded in its own group. Equality of the
L₀* and Borel action images then forces t* to act on K* by an inner
automorphism. The assembly owner supplies that image equality and uses
the external-X alternative; no central-factor identification is assumed here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
13.8.20, printed pp.954–955 (PDF pp.971–972).
-/

public section
open Subgroup
open CFSG.Quasithin.Chapter13.Section08
open Theory.SpecificGroups.Alternating.FiveBorelCentralFactor

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.CentralFactors

variable {G : Type*} [Group G]

/-- The field-four Borel forces the action image of D* to equal its own. -/
theorem linear_two_four_borel_action
    (H K D : Subgroup G) [(Source.starImage H K).Normal]
    (hDH : D ≤ H) (hD : IsPPerfect 2 D)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (eK : Source.starImage H K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (P : Sylow 2 (Source.starImage H K))
    (hBD : borel (Source.starImage H K) P ≤ Source.starImage H D)
    (hDN : Source.starImage H D ≤ normalizer (borel (Source.starImage H K) P : Set (Source.Hstar H))) :
    (Source.starImage H D).map (MulAut.conjNormal : Source.Hstar H →* MulAut (Source.starImage H K)) =
      (borel (Source.starImage H K) P).map MulAut.conjNormal := by
  obtain ⟨e₅⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  exact twoPerfect_conjugation_eq_borel _ _ (eK.trans e₅) P
    (star_isPPerfect H D hDH hD) hBD hDN

/-- Place the constructed relative centralizer inside D* using the actual Borel. -/
theorem linear_two_four_starCentralizer_le
    (H K D : Subgroup G) [(Source.starImage H K).Normal]
    (hDH : D ≤ H) (hD : IsPPerfect 2 D)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (eK : Source.starImage H K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (P : Sylow 2 (Source.starImage H K))
    (hBD : borel (Source.starImage H K) P ≤ Source.starImage H D)
    (hDN : Source.starImage H D ≤ normalizer (borel (Source.starImage H K) P : Set (Source.Hstar H))) :
    starCentralizer H K D ≤ Source.starImage H D := by
  obtain ⟨e₅⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  exact centralizer_le_twoPerfect _ _ (eK.trans e₅) P
    (star_isPPerfect H D hDH hD) hBD hDN

/-- The Borel calculation discharges the placement premise of the residual
construction and identifies its literal star image. -/
theorem linear_two_four_borel_centralFactor_starImage [Finite G]
    (H K D : Subgroup G) [(Source.starImage H K).Normal]
    (hDH : D ≤ H) (hD : IsPPerfect 2 D)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (eK : Source.starImage H K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (P : Sylow 2 (Source.starImage H K))
    (hBD : borel (Source.starImage H K) P ≤ Source.starImage H D)
    (hDN : Source.starImage H D ≤ normalizer (borel (Source.starImage H K) P : Set (Source.Hstar H))) :
    Source.starImage H (centralFactor H K D) = starCentralizer H K D := by
  obtain ⟨_, _, _, hp⟩ := linear_two_four_centralizer_product H K D hDH hD hF eK
  exact centralFactor_starImage_eq H K D
    (linear_two_four_starCentralizer_le H K D hDH hD hF eK P hBD hDN) hp

/-- Transport the source commutator bound, keeping the two-core embedded in
its own subgroup before taking the literal H/O₂(H) image. -/
theorem star_commutator_le_core (H Y : Subgroup G) (hYH : Y ≤ H) (t : H)
    (hcomm : ⁅Y, zpowers t.val⁆ ≤ Y.pCoreIn 2) :
    ⁅Source.starImage H Y, zpowers (QuotientGroup.mk' (pCore 2 H) t)⁆ ≤
      (Source.starImage H Y).pCoreIn 2 := by
  have hc : ⁅Y.subgroupOf H, zpowers t⁆ ≤ (Y.subgroupOf H).pCoreIn 2 := by
    have hm : (⁅Y.subgroupOf H, zpowers t⁆).map H.subtype ≤
        ((Y.subgroupOf H).pCoreIn 2).map H.subtype := by
      rw [map_commutator, map_subgroupOf_eq_of_le hYH, MonoidHom.map_zpowers,
        core_subgroupOf_map hYH]
      exact hcomm
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hm (mem_map.mpr ⟨x, hx, rfl⟩)
    exact H.subtype_injective hyx ▸ hy
  exact commutator_image_le_core (QuotientGroup.mk' (pCore 2 H)) (Y.subgroupOf H) t hc

/-- The source L₀ commutator bound rules out an outer actor in the field-four
case, once the assembly has established L₀'s actual Borel action image. -/
theorem linear_two_four_L₀_actor_inner
    (H K L₀ : Subgroup G) [(Source.starImage H K).Normal]
    (hL₀H : L₀ ≤ H)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (eK : Source.starImage H K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (P : Sylow 2 (Source.starImage H K)) (t : H)
    (himage : (Source.starImage H L₀).map
        (MulAut.conjNormal : Source.Hstar H →* MulAut (Source.starImage H K)) =
      (borel (Source.starImage H K) P).map MulAut.conjNormal)
    (ht : QuotientGroup.mk' (pCore 2 H) t ∈
      normalizer (borel (Source.starImage H K) P : Set (Source.Hstar H)))
    (hcomm : ⁅L₀, zpowers t.val⁆ ≤ L₀.pCoreIn 2) :
    (MulAut.conjNormal (QuotientGroup.mk' (pCore 2 H) t) :
      MulAut (Source.starImage H K)) ∈ MulAut.innerSubgroup (Source.starImage H K) := by
  obtain ⟨e₅⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  exact inner_of_borel_image_commutator _ _ (eK.trans e₅) P _ himage ht
    (star_commutator_le_core H L₀ hL₀H t hcomm)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.CentralFactors
