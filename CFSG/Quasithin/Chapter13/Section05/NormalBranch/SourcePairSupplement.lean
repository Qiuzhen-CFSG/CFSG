module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceOddRotation
public import Theory.GroupTheory.DihedralGeneratedFactor
public import Theory.GroupTheory.SymmetricThreeTwoCore

/-!
# A literal order-six supplement to the quaternion pair

The selected cubic rotation and original involution generate a dihedral
group of order six. The index-two seed places V in its product with U_H;
conjugation gives the other generator. Thus the original pair is U_H times
this actual supplement and has order at most192.

Source: Aschbacher–Smith13.5.15, printed p.920.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourcePairSupplement
open Section08.SourceCompletion
open SourceOrthogonal SourceOddRotation
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L)≃*alternatingGroup (Fin 6))
  (hseed : D.Vplus=⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬IsMulCommutative D.UH)

omit [Finite G] in
theorem supplement_card (v r:G) (hvq:v∉D.QH) (hv2:v^2=1) (hr:orderOf r=3)
    (hi:v*r*v⁻¹=r⁻¹) : Nat.card (zpowers r⊔zpowers v:Subgroup G)=6 := by
  have hvn : v≠1 := fun he=>hvq (he ▸ D.QH.one_mem)
  have hvo : orderOf v=2 := orderOf_eq_prime hv2 hvn
  have hout : v∉zpowers r := by
    intro hh
    have hd := (zpowers r).orderOf_dvd_natCard hh
    rw [hvo,Nat.card_zpowers,hr] at hd
    norm_num at hd
  exact (DihedralGroup.sup_zpowers_equiv_of_inversion (by decide:0<3) r v hr hv2 hout hi).1

include d h e hseed hn hU in
theorem pair_eq_closure_sup_supplement (v r:G) (hv:v∈D.V) (hvq:v∉D.QH)
    (hv2:v^2=1) (hr:orderOf r=3) (hrH:r∈D.H) (hi:v*r*v⁻¹=r⁻¹) :
    D.V⊔D.V.map (MulAut.conj r).toMonoidHom=D.UH⊔(zpowers r⊔zpowers v) := by
  let I := D.V⊔D.V.map (MulAut.conj r).toMonoidHom
  let J := D.UH⊔(zpowers r⊔zpowers v)
  have hp := (odd_rotation_is_cubic d h e hseed hn hU v r hv hv2 (by decide:Nat.Prime 3)
    (by decide:3≠2) hr hrH hi).2
  have hUI := SourcePairCore.closure_le_nonTwo_pair d h e hseed hn hU r hrH hp
  have hrI := rotation_mem_pair v r hv hv2 (by decide:Nat.Prime 3) (by decide:3≠2) hr hi
  apply le_antisymm
  · have hvplus : v∉D.Vplus := fun hh=>hvq (h.UH_le_QH (le_conjugateSpanBy _ _ hh))
    have hV : D.V≤J := by
      rw [←sup_zpowers_eq_of_relIndex_prime h.plus_le Nat.prime_two (seed_index d) hv hvplus]
      exact sup_le ((le_conjugateSpanBy _ _).trans le_sup_left)
        (le_sup_right.trans le_sup_right)
    refine sup_le hV ?_
    rintro _ ⟨x,hx,rfl⟩
    have hrJ : r∈J := mem_sup_right (mem_sup_left (mem_zpowers r))
    exact J.mul_mem (J.mul_mem hrJ (hV hx)) (J.inv_mem hrJ)
  · exact sup_le hUI (sup_le (zpowers_le.mpr hrI) (zpowers_le.mpr (mem_sup_left hv)))

include d h e hseed hn hU in
theorem pair_card_le (v r:G) (hv:v∈D.V) (hvq:v∉D.QH)
    (hv2:v^2=1) (hr:orderOf r=3) (hrH:r∈D.H) (hi:v*r*v⁻¹=r⁻¹) :
    Nat.card (D.V⊔D.V.map (MulAut.conj r).toMonoidHom:Subgroup G)≤192 := by
  have he := pair_eq_closure_sup_supplement d h e hseed hn hU v r hv hvq hv2 hr hrH hi
  rw [he]
  have hjH : zpowers r⊔zpowers v≤D.H :=
    sup_le (zpowers_le.mpr hrH) (zpowers_le.mpr (h.V_le_H hv))
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes D.UH (zpowers r⊔zpowers v)
    (hjH.trans (le_normalizer_conjugateSpanBy D.Vplus D.H))
  rw [(SourceQuaternion.source13_5_15_five d h e hseed hn hU).2.1,supplement_card v r hvq hv2 hr hi] at hc
  have hp := Nat.card_pos (α:=(D.UH⊓(zpowers r⊔zpowers v):Subgroup G))
  nlinarith

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourcePairSupplement
end
