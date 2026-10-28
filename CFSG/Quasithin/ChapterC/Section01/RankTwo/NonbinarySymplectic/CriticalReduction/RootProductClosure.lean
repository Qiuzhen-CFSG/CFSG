module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootProductActive
public import Glauberman.BaumannRankOneClosure
public import Theory.GroupTheory.CComponent.QuasisimpleFactors

/-!
# The actual Baumann normal closure and its rank-one local data

Inside the active source envelope F, form the literal normal closure C of
the original Baumann subgroup. Its nontrivial SL₂ image normally generates
the quotient, so C O₂(F) = F. The same quotient map gives C/O₂(C) = SL₂
at the original field degree and O₂(C) = C intersect O₂(F). The ambient
self-centralizing core makes F and then C groups of characteristic two.
The actual Sylow subgroup of C is J_alpha(T_beta) intersect C and has a
unique maximal overgroup.

Source: MS93 (5.1), printed p.913, the Baumann step before Niles. To obtain
the source F₀ from C it remains to prove that this Sylow intersection is
exactly the original Baumann subgroup. Selected-path generation, arbitrary-
degree Niles, terminal exclusions and the distance-two witness remain open.
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

/-- The actual Baumann normal closure supplements the active rank-one
core and has the original SL₂ quotient. Its Sylow subgroup is the exact
intersection with the original small-mover join. The remaining Baumann
step is to prove that this intersection equals the original Baumann group. -/
theorem Input.replacement_root_product_baumann_closure
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
      ∃ I : Subgroup (FreeAmalgam d.radical), I ≤ stabilizer d.radical a ∧
      ∃ C : Subgroup (FreeAmalgam d.radical), C ≤ I ∧ (C.subgroupOf I).Normal ∧
        C = (normalClosure ((Glauberman.baumannSubgroup (Q d.radical t)).subgroupOf I : Set I)).map
          I.subtype ∧
        Glauberman.baumannSubgroup (Q d.radical t) ≤ C ∧
        C ⊔ (pCore 2 I).map I.subtype = I ∧
        Nonempty ((C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin 2) E.Carrier) ∧
        (pCore 2 C).map C.subtype = C ⊓ (pCore 2 I).map I.subtype ∧
        generalizedFitting C = pCore 2 C ∧
        ∃ P : Sylow 2 C, (P : Subgroup C).map C.subtype =
          Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t)
            (Nat.card F ^ 2) ⊓ C ∧
          Order.HasUniqueMaximalOver (P : Subgroup C) ⊤ := by
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
  obtain ⟨hgen,⟨eN⟩,hcores,hfit,T,hT,hunique⟩ :=
    Glauberman.baumann_normalClosure_rank_one hEc S q hq hk hBnat hselfI
  change N ⊔ pCore 2 I = ⊤ at hgen
  change (pCore 2 N).map N.subtype = N ⊓ pCore 2 I at hcores
  let C := N.map I.subtype
  let e : N ≃* C := N.equivMapOfInjective I.subtype I.subtype_injective
  let : Finite C := Finite.of_surjective e e.surjective
  have hNsub : C.subgroupOf I = N := comap_map_eq_self_of_injective I.subtype_injective N
  have hCn : (C.subgroupOf I).Normal := by rw [hNsub]; infer_instance
  have hBsub : (Glauberman.baumannSubgroup (Q d.radical t)).subgroupOf I =
      Glauberman.baumannSubgroup (S : Subgroup I) := by
    rw [←hBa]
    exact comap_map_eq_self_of_injective I.subtype_injective _
  have hCeq : C = (normalClosure ((Glauberman.baumannSubgroup (Q d.radical t)).subgroupOf I : Set I)).map
      I.subtype := by rw [hBsub]
  have hBC : Glauberman.baumannSubgroup (Q d.radical t) ≤ C := by
    rw [←hBa]
    exact map_mono le_normalClosure
  have hgen' : C ⊔ (pCore 2 I).map I.subtype = I := by
    have hh := congrArg (Subgroup.map I.subtype) hgen
    rwa [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hh
  have hcorem : ((pCore 2 N).map N.subtype).map I.subtype = (pCore 2 C).map C.subtype := by
    rw [←pCore_map_iso 2 e,Subgroup.map_map,Subgroup.map_map]
    rfl
  have hcores' : (pCore 2 C).map C.subtype = C ⊓ (pCore 2 I).map I.subtype := by
    rw [←hcorem,hcores,Subgroup.map_inf _ _ _ I.subtype_injective]
  let eqQ := e.symm.toMonoidHom.pCoreQuotientEquiv e.symm.surjective
    (IsPGroup.ker_isPGroup_of_injective (p := 2) e.symm.injective)
  let P : Sylow 2 C := T.mapSurjective (f := e.toMonoidHom) e.surjective
  have hfit' : generalizedFitting C = pCore 2 C := by
    have hh := congrArg (Subgroup.map e.toMonoidHom) hfit
    rwa [map_generalizedFitting_equiv,pCore_map_iso] at hh
  have hu : Order.HasUniqueMaximalOver (P : Subgroup C) ⊤ := by
    have hh := hunique.map e.mapSubgroup
    rw [OrderIso.map_top] at hh
    exact hh
  refine ⟨E,hE,I,hI,C,map_subtype_le _,hCn,hCeq,hBC,hgen',⟨eqQ.trans eN⟩,hcores',hfit',P,?_,hu⟩
  change ((T : Subgroup N).map e.toMonoidHom).map C.subtype = _
  rw [Subgroup.map_map]
  change (T : Subgroup N).map (I.subtype.comp N.subtype) = _
  rw [←Subgroup.map_map,hT,Subgroup.map_inf _ _ _ I.subtype_injective,hS]

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
