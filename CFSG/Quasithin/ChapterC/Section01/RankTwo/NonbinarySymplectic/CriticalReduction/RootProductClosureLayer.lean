module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootProductThompsonLayer
public import Glauberman.BaumannClosureTransport
public import Theory.GroupTheory.PGroup.SylowOmegaSimpleAction

/-!
# The native omega modules of the actual Baumann closure

The enlarged original Thompson omega layer lies in the original Baumann
subgroup. Inside the active rank-one envelope, its normal closure N keeps
the original-degree SL₂ quotient and the whole two-residual. The actual
Sylow intersection retains the original all-abelian Thompson central omega
and Baumann subgroup; its Baumann conjugates generate N internally.

The full natural Sylow-fixed seed embeds into the ordinary omega-center
of this new Sylow. Its native normal closure is elementary, noncentral,
and contained in Ω₁Z(O₂(N)), with its exact fixed/moved splitting. Its
centralizer, and that of the whole core omega, are exactly O₂(N). Thus
this actual native module has faithful original-degree SL₂ action modulo
the whole core, with all central attachments retained.

Source: MS93 (5.1), printed p.913, the Baumann and Niles preparation.
The equality between the new Sylow and its Baumann subgroup, selected-path
generation, Niles conclusion, and terminal distance exclusions remain open.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit CentralRootGeometry.SmallMovers
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The original Baumann closure retains its rank-one quotient, all-abelian
central omega and noncentral native Sylow-center module at the original
field degree. Its whole two-residual agrees with the original envelope. -/
theorem Input.replacement_root_product_native_baumann_closure
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t)
    (E₁ E₂ : Subgroup (FreeAmalgam d.radical))
    (hE₁ : E₁ ≤ Q d.radical t) (hE₂ : E₂ ≤ Q d.radical t)
    (hc₁ : (Q d.radical a).relIndex E₁ = Nat.card F)
    (hc₂ : (Q d.radical a).relIndex E₂ = Nat.card F)
    (hi₁ : (centralizer (E₁ : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) = Nat.card F)
    (hi₂ : (centralizer (E₂ : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) = Nat.card F)
    (hprod : (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F ^ 2) : Set (FreeAmalgam d.radical)) ⊆
      (E₁ : Set (FreeAmalgam d.radical)) * (E₂ : Set (FreeAmalgam d.radical))) :
    ∃ E : BinaryField, E.degree = n ∧
      ∃ I : Subgroup (FreeAmalgam d.radical), I ≤ stabilizer d.radical a ∧ Q d.radical a ≤ I ∧
      ∃ S : Sylow 2 I,
        (S : Subgroup I).map I.subtype =
          Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) (Nat.card F ^ 2) ∧
        (Glauberman.baumannSubgroup (S : Subgroup I)).map I.subtype =
          Glauberman.baumannSubgroup (Q d.radical t) ∧
        omegaCenterIn (thompsonSubgroup (Q d.radical t)) ⊔ U d.radical a ≤
          Glauberman.baumannSubgroup (Q d.radical t) ∧
      let N := normalClosure (Glauberman.baumannSubgroup (S : Subgroup I) : Set I)
      N ⊔ pCore 2 I = ⊤ ∧
      Nonempty ((N ⧸ pCore 2 N) ≃* Matrix.SpecialLinearGroup (Fin 2) E.Carrier) ∧
      (pCore 2 N).map N.subtype = N ⊓ pCore 2 I ∧
      generalizedFitting N = pCore 2 N ∧
      (pResidual 2 N).map N.subtype = pResidual 2 I ∧
      U d.radical a ≤ N.map I.subtype ∧
      ∃ P : Sylow 2 N,
        ((P : Subgroup N).map N.subtype).map I.subtype =
          Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t)
            (Nat.card F ^ 2) ⊓ N.map I.subtype ∧
        Order.HasUniqueMaximalOver (P : Subgroup N) ⊤ ∧
        ((omegaCenterIn (thompsonSubgroup (P : Subgroup N))).map N.subtype).map I.subtype =
          omegaCenterIn (thompsonSubgroup (Q d.radical t)) ∧
        ((Glauberman.baumannSubgroup (P : Subgroup N)).map N.subtype).map I.subtype =
          Glauberman.baumannSubgroup (Q d.radical t) ∧
        normalClosure (Glauberman.baumannSubgroup (P : Subgroup N) : Set N) = ⊤ ∧
        IsElementaryAbelian 2
          (normalClosure (omegaCenterIn (thompsonSubgroup (P : Subgroup N)) : Set N)) ∧
        ⁅omegaCenterIn (thompsonSubgroup (P : Subgroup N)),pResidual 2 N⁆ ≠ ⊥ ∧
        U d.radical a ⊓ centralizer
            (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t)
              (Nat.card F ^ 2) : Set (FreeAmalgam d.radical)) ≤
          ((omegaCenterIn (P : Subgroup N)).map N.subtype).map I.subtype ∧
        IsElementaryAbelian 2 (normalClosure (omegaCenterIn (P : Subgroup N) : Set N)) ∧
        normalClosure (omegaCenterIn (P : Subgroup N) : Set N) ≤ pCore 2 N ∧
        ⁅normalClosure (omegaCenterIn (P : Subgroup N) : Set N),pResidual 2 N⁆ ≠ ⊥ ∧
        normalClosure (omegaCenterIn (P : Subgroup N) : Set N) =
          ⁅normalClosure (omegaCenterIn (P : Subgroup N) : Set N),(⊤ : Subgroup N)⁆ ⊔
          (normalClosure (omegaCenterIn (P : Subgroup N) : Set N) ⊓ center N) ∧
        normalClosure (omegaCenterIn (P : Subgroup N) : Set N) ≤ omegaCenterIn (pCore 2 N) ∧
        centralizer (normalClosure (omegaCenterIn (P : Subgroup N) : Set N) : Set N) = pCore 2 N ∧
        centralizer (omegaCenterIn (pCore 2 N) : Set N) = pCore 2 N := by
  obtain ⟨E,hE,I,hI,hQI,S,hS,⟨eI⟩,hm,hmt,hBa,hOm,hTh,hB,hκ⟩ :=
    h.replacement_root_product_active_rank_one d geometry hb ha hat
      E₁ E₂ hE₁ hE₂ hc₁ hc₂ hi₁ hi₂ hprod
  let := finite_stabilizer d.radical a
  let : Finite I := Finite.of_injective (inclusion hI) (inclusion_injective hI)
  let q := eI.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))
  have hq : Function.Surjective q := eI.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 I := by
    change eI.toMonoidHom.ker.comap (QuotientGroup.mk' (pCore 2 I)) = _
    rw [eI.toMonoidHom.ker_eq_bot eI.injective,MonoidHom.comap_bot,QuotientGroup.ker_mk']
  have hBnat : ¬ Glauberman.baumannSubgroup (S : Subgroup I) ≤ pCore 2 I := by
    intro hh
    apply hB
    have hh' := map_mono (f := I.subtype) hh
    rwa [hBa] at hh'
  have hEc : 4 ≤ Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) h.nonbinary
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha hat
  have hIrange : I ≤ j.range := hI.trans_eq hjr.symm
  have hmap : (I.comap j).map j = I := map_comap_eq_self hIrange
  let ep : I.comap j ≃* I := ((I.comap j).equivMapOfInjective j hj).trans
    (MulEquiv.subgroupCongr hmap)
  have hselfI : centralizer (pCore 2 I : Set I) ≤ pCore 2 I := by
    apply (Theory.Quasithin.centralizer_pCore_le_iff 2 ep).mp
    apply centralizer_pCore_le_of_pCore_le (I.comap j) (h.replacement_core_selfCentralizing d)
    intro x hx
    exact hQI (hjQ ▸ mem_map_of_mem j hx)
  let N := normalClosure (Glauberman.baumannSubgroup (S : Subgroup I) : Set I)
  obtain ⟨hgen,heN,hcores,hfit,P,hP,hunique⟩ :=
    Glauberman.baumann_normalClosure_rank_one hEc S q hq hk hBnat hselfI
  change N ⊔ pCore 2 I = ⊤ at hgen
  have hgenS : N ⊔ (S : Subgroup I) = ⊤ := top_unique (by
    rw [←hgen]
    exact sup_le_sup_left (pCore_isPGroup.le_sylow_of_normal S) N)
  let W := omegaCenterIn (thompsonSubgroup (Q d.radical t)) ⊔ U d.radical a
  obtain ⟨_,hWe,hWn,hWQ,_,_⟩ := h.replacement_root_product_thompson_layer d geometry hb ha hat
    E₁ E₂ hE₁ hE₂ hc₁ hc₂ hi₁ hi₂ hprod
  let : IsElementaryAbelian 2 W := hWe
  have hWI : W ≤ I := hWQ.trans hQI
  let W₀ := W.subgroupOf I
  let : IsElementaryAbelian 2 W₀ := IsElementaryAbelian.subgroupOf hWI
  let : W₀.Normal := (normal_subgroupOf_iff_le_normalizer hWI).mpr (hI.trans hWn)
  have hZW : omegaCenterIn (thompsonSubgroup (S : Subgroup I)) ≤ W₀ := by
    intro x hx
    exact (show omegaCenterIn (thompsonSubgroup (Q d.radical t)) ≤ W from le_sup_left)
      (hOm ▸ mem_map_of_mem I.subtype hx)
  have hmove : ⁅omegaCenterIn (thompsonSubgroup (S : Subgroup I)),pResidual 2 I⁆ ≠ ⊥ := by
    intro hz
    apply hmt
    have hm := congrArg (Subgroup.map I.subtype) hz
    rwa [map_commutator,hOm,Subgroup.map_bot] at hm
  have hn := Glauberman.baumann_normalClosure_native_layer S N W₀ rfl hgenS hZW hmove P hP
  have hQT : Q d.radical a ≤ Q d.radical t := by
    rw [←hjQ,←hjR]
    exact map_mono (h.replacement_core_le d)
  have hWB : W ≤ Glauberman.baumannSubgroup (Q d.radical t) :=
    Glauberman.elementary_layer_le_baumann _ W (hWQ.trans hQT) le_sup_left
  have hUB : U d.radical a ≤ Glauberman.baumannSubgroup (Q d.radical t) := le_sup_right.trans hWB
  have hUI : U d.radical a ≤ I := le_sup_right.trans hWI
  let U₀ := (U d.radical a).subgroupOf I
  let : IsElementaryAbelian 2 (U d.radical a) := IsElementaryAbelian.of_le (show U d.radical a ≤ W from le_sup_right)
  let : IsElementaryAbelian 2 U₀ := IsElementaryAbelian.subgroupOf hUI
  have hUmap : U₀.map I.subtype = U d.radical a := map_subgroupOf_eq_of_le hUI
  have hUB₀ : U₀ ≤ Glauberman.baumannSubgroup (S : Subgroup I) := by
    apply (map_le_map_iff_of_injective I.subtype_injective).mp
    rw [hUmap,hBa]
    exact hUB
  have hUN : U₀ ≤ N := hUB₀.trans le_normalClosure
  have hUS : U₀ ≤ (S : Subgroup I) := hUB₀.trans inf_le_left
  have hfixed : (U₀ ⊓ centralizer (S : Set I)).map I.subtype =
      U d.radical a ⊓ centralizer
        (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t)
          (Nat.card F ^ 2) : Set (FreeAmalgam d.radical)) := by
    change (U₀ ⊓ centralizer ((S : Subgroup I) : Set I)).map I.subtype = _
    rw [←map_inf_centralizer_of_injective I.subtype I.subtype_injective,hUmap,hS]
  have hfixedMove : ⁅U₀ ⊓ centralizer (S : Set I),pResidual 2 I⁆ ≠ ⊥ := by
    intro hz
    apply hm
    have hz' := congrArg (Subgroup.map I.subtype) hz
    rwa [map_commutator,hfixed,Subgroup.map_bot] at hz'
  have ho := Glauberman.baumann_closure_sylow_omega_layer S N U₀ hgenS hUN hUS
    hfixedMove P hP hn.2.2.2.2.2.1
  obtain ⟨eN⟩ := heN
  let qN := eN.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 N))
  have hqN : Function.Surjective qN := eN.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkN : qN.ker = pCore 2 N := by
    change eN.toMonoidHom.ker.comap (QuotientGroup.mk' (pCore 2 N)) = _
    rw [eN.toMonoidHom.ker_eq_bot eN.injective,MonoidHom.comap_bot,QuotientGroup.ker_mk']
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) E.Carrier) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hEc
  let : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) E.Carrier) :=
    (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := E.Carrier)).isSimpleGroup
  let : IsElementaryAbelian 2 (normalClosure (omegaCenterIn (P : Subgroup N) : Set N)) := ho.2.1
  have hkernel := Theory.GroupTheory.sylow_omega_closure_centralizers_of_simple_quotient
    P qN hqN hkN ho.2.2.2.1
  have hOmegaCore := Theory.GroupTheory.sylow_omega_closure_le_core_omega P
  refine ⟨E,hE,I,hI,hQI,S,hS,hBa,hWB,hgen,⟨eN⟩,hcores,hfit,
    Subgroup.pResidual_of_normal_pGroup_supplement 2 N (S : Subgroup I) S.isPGroup' hgenS,?_,P,?_,hunique,
    ?_,?_,hn.2.2.2.1,hn.2.2.2.2.2.1,hn.2.2.2.2.2.2.2,?_,ho.2.1,ho.2.2.1,ho.2.2.2.1,ho.2.2.2.2,hOmegaCore,hkernel⟩
  · rw [←hUmap]
    exact map_mono hUN
  · rw [hP,Subgroup.map_inf _ _ _ I.subtype_injective,hS]
  · rw [hn.2.1,hOm]
  · rw [hn.2.2.1,hBa]
  · have hh := map_mono (f := I.subtype) ho.1
    rwa [hfixed] at hh

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
