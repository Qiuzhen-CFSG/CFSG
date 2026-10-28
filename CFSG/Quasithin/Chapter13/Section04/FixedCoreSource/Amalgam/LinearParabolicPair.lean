module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearFixedLine
public import Theory.SpecificGroups.PSL3Two.Parabolics.CompanionMarking

/-!
# A simultaneous marking of the original linear parabolics

Restrict both original vertices and the common Sylow to the actual normal
component. The normal supplement index formula gives degree seven for both
restrictions. Their intersection is the restricted Sylow. Thus a marking
sending the second vertex to the line parabolic necessarily sends the first
to the point parabolic, under the same quotient map.

This fixes the relative orientation needed to compare the two original
fixed-line orbit modules; no orientation relative to a constituent is
assumed. The model equivalence is the actual linear-case hypothesis.
Source1332OneTwo retains its preceding producer and final discharge with
the fixed-core assembly. Source: Aschbacher–Smith 13.4.7, pp.900–901.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}

/-- One quotient marking identifies both original parabolics and the
literal intersection of the common Sylow with the selected component. -/
theorem original_pair_linear_companion_image
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      Matrix.PSL3Two.PSL)
    (e : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      BinaryLinearThree.Group)
    (hB : (B.subgroupOf (K.map (A ⊔ B).subtype)).map
      (e.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.lineParabolicSL)
    (hSb : ((T : Subgroup G).subgroupOf (K.map (A ⊔ B).subtype)).map
      (e.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.borelSL) :
    (A.subgroupOf (K.map (A ⊔ B).subtype)).map
      (e.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.pointParabolicSL := by
  let X := A ⊔ B
  let C := K.map X.subtype
  obtain ⟨S,hS,_⟩ := original_pair_linear_parabolic h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK eK
  rw [←hS] at hSb
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker ≤ (S : Subgroup C) := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal S
  have hSA : (S : Subgroup C) ≤ A.subgroupOf C := by rw [hS]; exact fun _ ht => hTA ht
  have hSB : (S : Subgroup C) ≤ B.subgroupOf C := by rw [hS]; exact fun _ ht => hTB ht
  have hiA : (A.subgroupOf C).index = 7 := by
    let SX : Sylow 2 X := T.subtype (hTA.trans le_sup_left)
    let : K.Normal := (original_pair_component_geometry h₀ D m h1332
      hTA hTB eA eB hne hindexA hindexB K hK).1
    let j := K.equivMapOfInjective X.subtype X.subtype_injective
    have hg : K ⊔ (SX : Subgroup X) = ⊤ := by
      rw [← (original_pair_component_is_residual h₀ D m h1332
        hTA hTB eA eB hne hindexA hindexB K hK).1]
      exact pResidual_sup_sylow_eq_top SX
    have hAP : (A.subgroupOf X).subgroupOf K = (A.subgroupOf C).comap j.toMonoidHom := rfl
    have hi : (A.subgroupOf C).index = A.relIndex X := by
      change (A.subgroupOf C).index = (A.subgroupOf X).index
      have hh := normal_intersection_relIndex (A.subgroupOf X) ⊤ K le_top (by
        rw [←hg]
        exact sup_le_sup le_rfl (show (SX : Subgroup X) ≤ A.subgroupOf X from fun _ ht => hTA ht))
      simpa only [top_subgroupOf,relIndex_top_right,hAP,
        (A.subgroupOf C).index_comap_of_surjective (f := j.toMonoidHom) j.surjective] using hh
    have hc : Nat.card (C ⧸ pCore 2 C) = 168 :=
      (Nat.card_congr eK.toEquiv).trans Matrix.PSL3Two.card_PSL
    have ha := (original_pair_parabolic_index_formula h₀ D m h1332
      hTA hTB eA eB hne hindexA hindexB K hK).1
    change A.relIndex X * 3 * 2 ^ (Nat.card (C ⧸ pCore 2 C)).factorization 2 =
      Nat.card (C ⧸ pCore 2 C) at ha
    rw [hc,show (Nat.factorization 168) 2 = 3 from by decide +kernel] at ha
    rw [hi]
    omega
  have hi : A.subgroupOf C ⊓ B.subgroupOf C = (S : Subgroup C) := by
    change (A ⊓ B).subgroupOf C = (S : Subgroup C)
    rw [intersection_eq_sylow hTA hTB eA eB hne,hS]
  have hA := Matrix.PSL3Two.companion_point_image f hf
    (A.subgroupOf C) (B.subgroupOf C) hiA (hk.trans hSA) (hk.trans hSB)
    (hSb ▸ map_mono hSA) hB (by rw [hi]; exact S.isPGroup')
  exact hA

/-- Both original parabolics and the common Sylow are marked by one
isomorphism of the literal component quotient. -/
theorem original_pair_linear_parabolic_pair
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      Matrix.PSL3Two.PSL) :
    let C := K.map (A ⊔ B).subtype
    ∃ e : (C ⧸ pCore 2 C) ≃* BinaryLinearThree.Group,
      let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
      (A.subgroupOf C).map f = Matrix.PSL3Two.pointParabolicSL ∧
      (B.subgroupOf C).map f = Matrix.PSL3Two.lineParabolicSL ∧
      ((T : Subgroup G).subgroupOf C).map f = Matrix.PSL3Two.borelSL := by
  obtain ⟨S,hS,hi⟩ := original_pair_linear_parabolic h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK eK
  obtain ⟨e,hB,hSb⟩ := BinaryLinearThree.FixedParabolicQuotient.exists_marking
    eK S (B.subgroupOf (K.map (A ⊔ B).subtype))
      (by rw [hS]; exact fun _ ht => hTB ht) hi
  rw [hS] at hSb
  exact ⟨e,original_pair_linear_companion_image h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK eK e hB hSb,hB,hSb⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
