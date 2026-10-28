module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.ParabolicDegrees
public import Theory.SpecificGroups.AlternatingSix.ParabolicPair

/-!
# Both original parabolics in the alternating-six component

The actual component is normal and supplements the common Sylow subgroup.
Restrict the Sylow and both vertices to that component; normal supplement
indices preserve their degrees and their intersection. In the ordinary A₆
row the degrees are fifteen. Their images remain distinct through the full
two-core quotient, since otherwise their intersection would be the Sylow
image and have index forty-five. One conjugation then identifies the two
images with the opposite duad and syntheme parabolics.

The selected component and its A₆ quotient remain explicit case hypotheses.
This constructs the simultaneous marking needed for the remaining module
comparison in 13.4.7(1iv); it does not select or exclude that case.
Source: Aschbacher--Smith 13.4.7, printed pp.900--901.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V A B : Subgroup G}
variable (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexA : ((Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (A : Set G)).relIndex (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : ((Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (B : Set G)).relIndex (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)


include h₀ D m h1332 hTA hTB eA eB hne hindexA hindexB hK

/-- Restrict the original pair and its common Sylow to the actual component. -/
theorem original_pair_component_parabolic_restriction :
    let X := A ⊔ B
    let C := K.map X.subtype
    ∃ S : Sylow 2 C,
      (S : Subgroup C) = (T : Subgroup G).subgroupOf C ∧
      (A.subgroupOf C).index = A.relIndex X ∧
      (B.subgroupOf C).index = B.relIndex X ∧
      A.subgroupOf C ⊓ B.subgroupOf C = (S : Subgroup C) := by
  let X := A ⊔ B
  let C := K.map X.subtype
  let SX : Sylow 2 X := T.subtype (hTA.trans le_sup_left)
  let : K.Normal := (original_pair_component_geometry h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK).1
  obtain ⟨R,hR⟩ := SX.exists_subgroupOf_eq_of_normal K
  let j := K.equivMapOfInjective X.subtype X.subtype_injective
  let S : Sylow 2 C := R.mapSurjective (f := j.toMonoidHom) j.surjective
  have hS : (S : Subgroup C) = (T : Subgroup G).subgroupOf C := by
    ext c
    obtain ⟨k,rfl⟩ := j.surjective c
    change j k ∈ (R : Subgroup K).map j.toMonoidHom ↔ _
    refine (mem_map_iff_mem (f := j.toMonoidHom) (K := (R : Subgroup K))
      (x := k) j.injective).trans ?_
    rw [hR]
    rfl
  have hg : K ⊔ (SX : Subgroup X) = ⊤ := by
    rw [← (original_pair_component_is_residual h₀ D m h1332
      hTA hTB eA eB hne hindexA hindexB K hK).1]
    exact pResidual_sup_sylow_eq_top SX
  have index (P : Subgroup G) (hTP : (T : Subgroup G) ≤ P) :
      (P.subgroupOf C).index = P.relIndex X := by
    change (P.subgroupOf C).index = (P.subgroupOf X).index
    have hh := normal_intersection_relIndex (P.subgroupOf X) ⊤ K le_top (by
      rw [←hg]
      exact sup_le_sup le_rfl (show (SX : Subgroup X) ≤ P.subgroupOf X from fun _ ht => hTP ht))
    have hP : (P.subgroupOf X).subgroupOf K = (P.subgroupOf C).comap j.toMonoidHom := rfl
    simpa only [top_subgroupOf,relIndex_top_right,hP,
      (P.subgroupOf C).index_comap_of_surjective (f := j.toMonoidHom) j.surjective] using hh
  refine ⟨S,hS,index A hTA,index B hTB,?_⟩
  change (A ⊓ B).subgroupOf C = (S : Subgroup C)
  rw [intersection_eq_sylow hTA hTB eA eB hne,hS]

open Theory.SpecificGroups.SymmetricSix

/-- One literal quotient marking identifies both opposite A₆ parabolics and their Sylow. -/
theorem original_pair_alternating_parabolic_pair
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃* A6) :
    let C := K.map (A ⊔ B).subtype
    ∃ e : (C ⧸ pCore 2 C) ≃* A6,
      let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
      ((T : Subgroup G).subgroupOf C).map f = a6Borel ∧
      (((A.subgroupOf C).map f = a6DuadStabilizer ∧
        (B.subgroupOf C).map f = a6SynthemeStabilizer) ∨
       ((A.subgroupOf C).map f = a6SynthemeStabilizer ∧
        (B.subgroupOf C).map f = a6DuadStabilizer)) := by
  let X := A ⊔ B
  let C := K.map X.subtype
  obtain ⟨S,hS,hiA,hiB,hAB⟩ := original_pair_component_parabolic_restriction
    h₀ D m h1332 hTA hTB eA eB hne hindexA hindexB K hK
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
  have hq : Function.Surjective q := eK.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker ≤ (S : Subgroup C) := by
    rw [MonoidHom.ker_comp_of_injective _ _ eK.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal S
  have hSA : (S : Subgroup C) ≤ A.subgroupOf C := by rw [hS]; exact fun _ ht => hTA ht
  have hSB : (S : Subgroup C) ≤ B.subgroupOf C := by rw [hS]; exact fun _ ht => hTB ht
  have hc : Nat.card (C ⧸ pCore 2 C) = 360 := by
    rw [Nat.card_congr eK.toEquiv,nat_card_alternatingGroup]
    norm_num
  obtain ⟨hdegA,hdegB⟩ := original_pair_parabolic_index_formula
    h₀ D m h1332 hTA hTB eA eB hne hindexA hindexB K hK
  change A.relIndex X * 3 * 2 ^ (Nat.card (C ⧸ pCore 2 C)).factorization 2 =
    Nat.card (C ⧸ pCore 2 C) at hdegA
  change B.relIndex X * 3 * 2 ^ (Nat.card (C ⧸ pCore 2 C)).factorization 2 =
    Nat.card (C ⧸ pCore 2 C) at hdegB
  rw [hc,show (Nat.factorization 360) 2 = 3 from by decide +kernel] at hdegA hdegB
  have h15A : A.relIndex X = 15 := by omega
  have h15B : B.relIndex X = 15 := by omega
  have hia : ((A.subgroupOf C).map q).index = 15 := by
    rw [index_map_eq _ hq (hk.trans hSA),hiA]
    exact h15A
  have hib : ((B.subgroupOf C).map q).index = 15 := by
    rw [index_map_eq _ hq (hk.trans hSB),hiB]
    exact h15B
  have hn : (A.subgroupOf C).map q ≠ (B.subgroupOf C).map q := by
    intro hh
    have he : A.subgroupOf C = B.subgroupOf C := by
      have hc := congrArg (Subgroup.comap q) hh
      simpa only [comap_map_eq,sup_of_le_left (hk.trans hSA),sup_of_le_left (hk.trans hSB)] using hc
    have ha : A.subgroupOf C = (S : Subgroup C) := by
      change A.subgroupOf C ⊓ B.subgroupOf C = (S : Subgroup C) at hAB
      simpa only [←he,inf_idem] using hAB
    have hiS : (S.mapSurjective hq).index = 15 := by
      change ((S : Subgroup C).map q).index = 15
      rw [←ha]
      exact hia
    have hh := (S.mapSurjective hq : Subgroup A6).index_mul_card
    rw [hiS,(S.mapSurjective hq).card_eq_multiplicity,a6_order] at hh
    norm_num [show (Nat.factorization 360) 2 = 3 from by decide +kernel] at hh
  obtain ⟨a,hSa,hab⟩ := AlternatingPair.pair_marking (S.mapSurjective hq)
    ((A.subgroupOf C).map q) ((B.subgroupOf C).map q)
    (map_mono hSA) (map_mono hSB) hia hib hn
  have hcomp : (eK.trans a).toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C)) =
      a.toMonoidHom.comp q := by ext x; rfl
  refine ⟨eK.trans a,?_,?_⟩
  · rw [←hS]
    rw [hcomp]
    change ((S : Subgroup C).map q).map a.toMonoidHom = a6Borel at hSa
    simpa only [map_map] using hSa
  · rw [hcomp]
    simpa only [map_map] using hab

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
