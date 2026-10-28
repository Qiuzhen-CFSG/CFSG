module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.Center
public import Theory.GroupTheory.PerfectSmallTwoAction
public import Theory.GroupTheory.CComponent.SolvableSupplement
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.SpecificGroups.SymmetricFive.WreathComponents

/-!
# The original component in the natural HS action branch

The canonical subgroup is the embedded solvable residual of H. Its image in
H/O₂(H) is the alternating subgroup of the literal symmetric-five model.
Solvable-kernel component lifting proves relative C-component membership;
the same quotient and the original Sylow subgroup give H = KT. The image is
the actual SL₂(4) matrix group, so K is transitive on the nonzero quotient
vectors. Perfectness also makes K centralize the source center of order four.

Natural coordinates remain an explicit input, to be constructed by the source
alternative exclusions. These are component construction results, not a proof
of 14.3.32. The commutator and indecomposability conclusions are separate.
Source: Aschbacher--Smith, 14.3.32(4), printed pp.1003--1004.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Theory.SpecificGroups.SymmetricFive.WreathComponents
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G}

def sourceComponent (F : InvariantFlag T V 3) : Subgroup G :=
  (solvableResidual F.H).map F.H.subtype

private theorem symmetric_residual_sylow (S : Sylow 2 (Equiv.Perm (Fin 5))) :
    solvableResidual (Equiv.Perm (Fin 5)) ⊔ (S : Subgroup _) = ⊤ := by
  rw [symmetric_residual]
  have hp : IsPGroup 2 ((Equiv.Perm (Fin 5)) ⧸ alternatingGroup (Fin 5)) := by
    apply (IsPGroup.iff_card (p := 2)).mpr
    exact ⟨1, by rw [pow_one, ← index_eq_card]; exact alternatingGroup.index_eq_two⟩
  apply top_unique
  rw [← pResidual_sup_sylow_eq_top S]
  exact sup_le_sup (sInf_le ⟨inferInstance, hp⟩) le_rfl

private theorem residual_component_of_symmetricFive {D : Type*} [Group D] [Finite D]
    (e : (D ⧸ pCore 2 D) ≃* Equiv.Perm (Fin 5)) :
    (solvableResidual D).IsCComponent := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 D))
  have hk : f.ker = pCore 2 D := by
    dsimp only [f]
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  let : Group.IsNilpotent f.ker := hk ▸ pCore_isPGroup.isNilpotent
  have hq : IsComponent (Equiv.Perm (Fin 5)) (solvableResidual (Equiv.Perm (Fin 5))) :=
    ⟨(inferInstance : (solvableResidual (Equiv.Perm (Fin 5))).Normal).isSubnormal,
      symmetric_residual_quasisimple⟩
  exact residual_isCComponent_of_surjective f
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) hq.isCComponent

private theorem residual_sylow_of_symmetricFive {D : Type*} [Group D] [Finite D]
    (e : (D ⧸ pCore 2 D) ≃* Equiv.Perm (Fin 5)) (S : Sylow 2 D) :
    solvableResidual D ⊔ (S : Subgroup D) = ⊤ := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 D))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hm : (solvableResidual D ⊔ (S : Subgroup D)).map f = ⊤ := by
    rw [Subgroup.map_sup, map_solvableResidual_eq f hf]
    exact symmetric_residual_sylow (S.mapSurjective hf)
  have hk : f.ker = pCore 2 D := by
    dsimp only [f]
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hh := congrArg (comap f) hm
  rw [comap_map_eq, comap_top, hk, sup_assoc,
    sup_eq_left.mpr (pCore_isPGroup.le_sylow_of_normal S)] at hh
  exact hh

theorem NaturalCoordinates.sourceComponent_isCComponent (F : InvariantFlag T V 3)
    (hc : NaturalCoordinates F) : ((sourceComponent F).subgroupOf F.H).IsCComponent := by
  obtain ⟨e, _, _⟩ := hc
  have hh := residual_component_of_symmetricFive
    (e.trans Representation.SL2FourNatural.SemilinearNormalizer.symmetricFiveEquiv)
  simpa only [sourceComponent, subgroupOf,
    comap_map_eq_self_of_injective F.H.subtype_injective] using hh

theorem NaturalCoordinates.sourceComponent_supplement (F : InvariantFlag T V 3)
    (hc : NaturalCoordinates F) : F.H = sourceComponent F ⊔ (T : Subgroup G) := by
  obtain ⟨e, _, _⟩ := hc
  have hTH : (T : Subgroup G) ≤ F.H := F.invariant 1
  have hh := congrArg (map F.H.subtype) (residual_sylow_of_symmetricFive
    (e.trans Representation.SL2FourNatural.SemilinearNormalizer.symmetricFiveEquiv)
    (T.subtype hTH))
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] at hh
  simpa only [sourceComponent, Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] using hh.symm

private theorem specialField_residual :
    solvableResidual Representation.SL2FourNatural.SemilinearNormalizer.specialField =
      Representation.SL2FourNatural.action.range.subgroupOf
        Representation.SL2FourNatural.SemilinearNormalizer.specialField := by
  let : Finite Representation.SL2FourNatural.SemilinearNormalizer.specialField :=
    Finite.of_equiv (Equiv.Perm (Fin 5))
      Representation.SL2FourNatural.SemilinearNormalizer.symmetricFiveEquiv.toEquiv.symm
  apply map_injective (f := Representation.SL2FourNatural.SemilinearNormalizer.symmetricFiveEquiv.toMonoidHom)
    Representation.SL2FourNatural.SemilinearNormalizer.symmetricFiveEquiv.injective
  rw [map_solvableResidual_eq _
    Representation.SL2FourNatural.SemilinearNormalizer.symmetricFiveEquiv.surjective,
    symmetric_residual,
    Representation.SL2FourNatural.SemilinearNormalizer.symmetricFiveEquiv_special]

theorem NaturalCoordinates.sourceComponent_transitive (F : InvariantFlag T V 3)
    (hc : NaturalCoordinates F) (x y : F.Uhat) (hx : x ≠ 1) (hy : y ≠ 1) :
    ∃ h : F.H, (h : G) ∈ sourceComponent F ∧ F.uhatAction h x = y := by
  obtain ⟨e, c, he⟩ := hc
  have hcx : (c x).toAdd ≠ 0 := by
    intro hz
    exact hx (c.injective (by simpa using congrArg Multiplicative.ofAdd hz))
  have hcy : (c y).toAdd ≠ 0 := by
    intro hz
    exact hy (c.injective (by simpa using congrArg Multiplicative.ofAdd hz))
  obtain ⟨a, ha⟩ := Representation.SL2FourNatural.transitive_nonzero
    (c x).toAdd (c y).toAdd hcx hcy
  let a' : Representation.SL2FourNatural.SemilinearNormalizer.specialField :=
    ⟨Representation.SL2FourNatural.action a, (show Representation.SL2FourNatural.action.range ≤
      Representation.SL2FourNatural.SemilinearNormalizer.specialField from le_sup_left) ⟨a, rfl⟩⟩
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 F.H))
  have hm : (solvableResidual F.H).map f =
      Representation.SL2FourNatural.action.range.subgroupOf
        Representation.SL2FourNatural.SemilinearNormalizer.specialField := by
    rw [map_solvableResidual_eq f
      (e.surjective.comp (QuotientGroup.mk'_surjective _)), specialField_residual]
  have ham : a' ∈ (solvableResidual F.H).map f := by
    rw [hm]
    exact ⟨a, rfl⟩
  obtain ⟨h, hh, hq⟩ := ham
  refine ⟨h, mem_map_of_mem F.H.subtype hh, c.injective ?_⟩
  have hv := he h x
  change (c (F.uhatAction h x)).toAdd = (f h).val (c x).toAdd at hv
  rw [hq] at hv
  exact congrArg Multiplicative.ofAdd (hv.trans ha)

omit [Finite G] in
theorem sourceComponent_le (F : InvariantFlag T V 3) : sourceComponent F ≤ F.H :=
  map_subtype_le _

omit [Finite G] in
theorem sourceComponent_normal (F : InvariantFlag T V 3) :
    ((sourceComponent F).subgroupOf F.H).Normal := by
  simpa only [sourceComponent, subgroupOf,
    comap_map_eq_self_of_injective F.H.subtype_injective] using
    (inferInstance : (solvableResidual F.H).Normal)

theorem sourceComponent_centralizes_center [IsMulCommutative V] (F : InvariantFlag T V 3)
    (hz : Nat.card (center F.U) ≤ 4) :
    sourceComponent F ≤ centralizer (F.ZU : Set G) := by
  have hZH : F.ZU ≤ F.H := (map_subtype_le (center F.U)).trans F.U_le_H
  let : (F.ZU.subgroupOf F.H).Normal :=
    normal_subgroupOf_of_le_normalizer F.H_normalizes_ZU
  have hcard : Nat.card (F.ZU.subgroupOf F.H) ≤ 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hZH).toEquiv,
      show Nat.card F.ZU = Nat.card (center F.U) from
        card_map_of_injective F.U.subtype_injective]
    exact hz
  have hh := le_centralizer_of_isPerfect_of_card_le_four
    (solvableResidual F.H) (F.ZU.subgroupOf F.H) hcard
  rintro k ⟨h, hh', rfl⟩ z hz
  exact congrArg (fun x : F.H => (x : G)) (hh hh' ⟨z, hZH hz⟩ hz)

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
