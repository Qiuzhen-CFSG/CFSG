module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourcePairSupplement

/-!
# The selected original pair has two-core U_H

The actual cubic rotation gives an order-six supplement and an upper bound
192 for the pair order. Its original starred image is S₃, whose two-core is
trivial. Since the kernel contains the already constructed order32 U_H, the
cardinality identity forces equality with the actual pair two-core.

Source: Aschbacher–Smith13.5.15, printed p.920.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourcePairExact
open Section08.SourceCompletion
open SourceOrthogonal SourceOddRotation SourcePairSupplement
open ChapterF.Section09.Setup.Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L)≃*alternatingGroup (Fin 6))
  (hseed : D.Vplus=⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬IsMulCommutative D.UH)
include d h e hseed hn hU

theorem core_eq_closure (v r:G) (hv:v∈D.V) (hvq:v∉D.QH)
    (hv2:v^2=1) (hr:orderOf r=3) (hrH:r∈D.H) (hi:v*r*v⁻¹=r⁻¹) :
    (D.V⊔D.V.map (MulAut.conj r).toMonoidHom).pCoreIn 2=D.UH := by
  let I := D.V⊔D.V.map (MulAut.conj r).toMonoidHom
  have hIH : I≤D.H := sup_le h.V_le_H (by
    rintro _ ⟨x,hx,rfl⟩
    exact D.H.mul_mem (D.H.mul_mem hrH (h.V_le_H hx)) (D.H.inv_mem hrH))
  have hp := (odd_rotation_is_cubic d h e hseed hn hU v r hv hv2 (by decide:Nat.Prime 3)
    (by decide:3≠2) hr hrH hi).2
  have hUI := SourcePairCore.closure_le_nonTwo_pair d h e hseed hn hU r hrH hp
  obtain ⟨j⟩ := original_star_pair_symmetricThree d h e hseed hn hU r hrH hp
  let f := pairProjection I hIH
  let j' := (MulEquiv.subgroupCongr (pairProjection_range I hIH)).trans j
  let η := j'.toMonoidHom.comp f.rangeRestrict
  have hη : Function.Surjective η := j'.surjective.comp f.rangeRestrict_surjective
  have hk : η.ker=f.ker := by
    ext x
    change j' (f.rangeRestrict x)=1↔f x=1
    rw [j'.map_eq_one_iff]
    exact Subtype.ext_iff
  have htwo : IsPGroup 2 η.ker := by
    rw [hk,pairProjection_ker]
    exact (isPGroup_pCoreIn 2 D.H).comap_subtype
  have hcore : f.ker=pCore 2 I := hk.symm.trans (ker_eq_twoCore_of_surjective_perm_three η hη htwo)
  have hc : Nat.card f.range=6 := by
    rw [Nat.card_congr j'.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm]
    decide
  have hcount := f.ker.index_mul_card
  rw [index_ker,hc] at hcount
  have hbound := pair_card_le d h e hseed hn hU v r hv hvq hv2 hr hrH hi
  have hkerCard : Nat.card f.ker≤32 := by change Nat.card I≤192 at hbound;omega
  have hUker : D.UH.subgroupOf I≤f.ker := by
    rw [pairProjection_ker]
    exact comap_mono h.UH_le_QH
  have hUcard : Nat.card (D.UH.subgroupOf I)=32 :=
    (Nat.card_congr (subgroupOfEquivOfLe hUI).toEquiv).trans
      (SourceQuaternion.source13_5_15_five d h e hseed hn hU).2.1
  have heq : D.UH.subgroupOf I=f.ker := eq_of_le_of_card_ge hUker (by rw [hUcard];exact hkerCard)
  change (pCore 2 I).map I.subtype=D.UH
  rw [←hcore,←heq,map_subgroupOf_eq_of_le hUI]

theorem exists_original_pair_core : ∃r∈D.H,orderOf r=3 ∧
    (D.V⊔D.V.map (MulAut.conj r).toMonoidHom).pCoreIn 2=D.UH ∧
    Nonempty ((Section08.Source.starImage D.H
      (D.V⊔D.V.map (MulAut.conj r).toMonoidHom))≃*Equiv.Perm (Fin 3)) := by
  obtain ⟨v,hv,hvq,hv2,p,hp,hp2,r,hrH,hr,hi⟩ := exists_odd_rotation h hU
  obtain ⟨hp3,hpair⟩ := odd_rotation_is_cubic d h e hseed hn hU v r hv hv2 hp hp2 hr hrH hi
  have hr3 : orderOf r=3 := hr.trans hp3
  exact ⟨r,hrH,hr3,core_eq_closure d h e hseed hn hU v r hv hvq hv2 hr3 hrH hi,
    original_star_pair_symmetricThree d h e hseed hn hU r hrH hpair⟩

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourcePairExact
end
