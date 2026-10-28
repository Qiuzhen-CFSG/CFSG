module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.Solvable.Witness
public import CFSG.Quasithin.ChapterB.Section06To07.IntrinsicMinimalParabolic
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.RatioSource.OutsideWitness.SourceE29.Solvable.Fitting
public import Theory.GroupTheory.AmalgamLocalCores
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
/-!
# The universal solvable E.2.9 source theorem

Restrict the original configuration to the minimal parabolic’s carrier and
apply the proved solvable witness construction. The inclusion equivalence
transports both literal subgroup maps, the prescribed Sylow intersection,
the relative normal core, and its dihedral quotient back to the original
ambient group. The separate characteristic-two inheritance theorem supplies
the second clause for every actual member.

This discharges `EarlierE29Solvable` with no witness or classification premise.
Source: Aschbacher–Smith, E.2.4 and E.2.8–9, printed pp.217,221–222;
application in 15.4.2(4), printed p.1156.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.RatioSource.OutsideWitness
universe u
variable {X : Type u} [Group X] [Finite X]

private theorem member_of_intrinsic {T : Sylow 2 X} {H N V : Subgroup X}
    (hTH : (T : Subgroup X) ≤ H) (hVH : V ≤ H)
    (w : ChapterE.Witnesses.Solvable.Witness (T.subtype hTH) (N.subgroupOf H) (V.subgroupOf H)) :
    ∃I:Subgroup X,Nonempty (SolvableMember T H N V I) := by
  let I := w.subgroup.map H.subtype
  let e : w.subgroup ≃* I := w.subgroup.equivMapOfInjective H.subtype H.subtype_injective
  have hIH : I ≤ H := map_subtype_le _
  have hVI : V ≤ I := by
    have hh := map_mono (f := H.subtype) w.le
    rwa [map_subgroupOf_eq_of_le hVH] at hh
  have hecomp : I.subtype.comp e.toMonoidHom = H.subtype.comp w.subgroup.subtype := by
    ext x
    rfl
  have hU : ((V.subgroupOf H).subgroupOf w.subgroup).map e.toMonoidHom = V.subgroupOf I := by
    apply map_injective I.subtype_injective
    rw [map_map,hecomp,← map_map,map_subgroupOf_eq_of_le w.le,
      map_subgroupOf_eq_of_le hVH,map_subgroupOf_eq_of_le hVI]
  have hA : (N.subgroupOf I).comap e.toMonoidHom = (N.subgroupOf H).subgroupOf w.subgroup := by
    ext x
    rfl
  have hcore : (N.subgroupOf I).normalCore.comap e.toMonoidHom =
      ((N.subgroupOf H).subgroupOf w.subgroup).normalCore := by
    rw [← normalCore_comap_of_surjective e.toMonoidHom e.surjective,hA]
  let C := ((N.subgroupOf H).subgroupOf w.subgroup).normalCore
  let D := (N.subgroupOf I).normalCore
  let f : C →* D := (e.toMonoidHom.comp C.subtype).codRestrict D (fun x => hcore.ge x.property)
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply e.injective
      exact congrArg Subtype.val hxy
    · intro y
      obtain ⟨x,hx⟩ := e.surjective y
      have hxC : x ∈ C := hcore.le (show e x ∈ D from hx.symm ▸ y.property)
      exact ⟨⟨x,hxC⟩,Subtype.ext hx⟩
  obtain ⟨P,hP⟩ := w.core_two_closed
  let R := P.mapSurjective hf.2
  have hR : (R : Subgroup D).Normal := hP.map f hf.2
  let S := w.sylow.mapSurjective (f := e.toMonoidHom) e.surjective
  have hS : (S : Subgroup I).map I.subtype = (T : Subgroup X) ⊓ I := by
    change ((w.sylow : Subgroup w.subgroup).map e.toMonoidHom).map I.subtype = _
    rw [map_map,hecomp,← map_map,w.sylow_eq,Subgroup.map_inf _ _ _ H.subtype_injective]
    change ((T : Subgroup X).subgroupOf H).map H.subtype ⊓ I = _
    rw [map_subgroupOf_eq_of_le hTH]
  have hgen : V.subgroupOf I ⊔ (V.subgroupOf I).map (MulAut.conj (e w.conjugator)).toMonoidHom = ⊤ := by
    have hh := congrArg (fun A : Subgroup w.subgroup => A.map e.toMonoidHom) w.generate
    rw [Subgroup.map_sup,hU,map_top_of_surjective _ e.surjective,map_map] at hh
    have he : e.toMonoidHom.comp (MulAut.conj w.conjugator).toMonoidHom =
        (MulAut.conj (e w.conjugator)).toMonoidHom.comp e.toMonoidHom := by
      ext x
      simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,map_mul,map_inv]
    rw [he,← map_map,hU] at hh
    exact hh
  obtain ⟨p,a,hp,hp2,ha,⟨d⟩⟩ := w.dihedral
  have hquot := QuotientGroup.equivOfSurjectiveComap e.toMonoidHom e.surjective C D hcore
  exact ⟨I,⟨⟨hIH,hVI,S,hS,e w.conjugator,hgen,⟨R,hR⟩,
    p,a,hp,hp2,ha,⟨hquot.symm.trans d⟩⟩⟩⟩

/-- The genuine solvable E.2.9 witness in the original ambient coordinates. -/
theorem Configuration.exists_solvableMember {T : Sylow 2 X} {H N V : Subgroup X}
    (c : Configuration T H N V) (hs : Group.IsSolvable H) :
    ∃I:Subgroup X,Nonempty (SolvableMember T H N V I) := by
  have hTH := c.sylow_le_maximal.trans c.maximal.le
  have hVH := c.le_sylow.trans hTH
  let S := T.subtype hTH
  let U := V.subgroupOf H
  let M := N.subgroupOf H
  obtain ⟨hmin,hmax⟩ := ChapterB.intrinsic_minimalParabolic T H N
    c.minimal c.sylow_le_maximal c.maximal
  have hM : M = ChapterB.minimalParabolicMax S hmin :=
    ChapterB.minimalParabolicMax_unique S hmin hmax (comap_mono c.sylow_le_maximal)
  let := c.elementary
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hVH
  have hUS : U ≤ (S : Subgroup H) := comap_mono c.le_sylow
  have hn : (U.subgroupOf (S : Subgroup H)).Normal := by
    apply (normal_subgroupOf_iff_le_normalizer hUS).mpr
    rw [show U = V.subgroupOf H from rfl,← subgroupOf_normalizer_eq hVH]
    exact comap_mono ((normal_subgroupOf_iff_le_normalizer c.le_sylow).mp c.normal_in_sylow)
  have hUc : U ≤ M.pCoreIn 2 := by
    apply (map_le_map_iff_of_injective H.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hVH,← Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective 2 H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le c.maximal.le]
    exact c.le_core
  have hout : ¬ U ≤ M.normalCore := by
    intro hh
    have hh := map_mono (f := H.subtype) hh
    rw [map_subgroupOf_eq_of_le hVH] at hh
    exact c.outside hh
  have hex : Nonempty (ChapterE.Witnesses.Solvable.Witness S M U) := by
    rw [hM] at hUc hout ⊢
    exact ChapterE.Witnesses.Solvable.solvable_witness S hmin hs U hUS hn hUc hout
  obtain ⟨w⟩ := hex
  exact member_of_intrinsic hTH hVH w

/-- Universal E.2.9 on the solvable source branch, with no witness parameter. -/
theorem source_earlierE29Solvable : EarlierE29Solvable.{u} := by
  intro X _ _ T H N V c hs
  exact ⟨c.exists_solvableMember hs,fun _ w hfit => w.generalizedFitting_eq_twoCore c hfit⟩
end CFSG.Quasithin.Chapter15.Section04.RatioSource.OutsideWitness
end
