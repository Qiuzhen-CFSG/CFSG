module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting
public import Theory.GroupTheory.SolvableRadical.SolvableKernel

/-!
# Even normal subgroups in the noncentral Fitting branch

For a noncentral C-component with trivial two-core, the source Fitting
quotient is SL₂ over a prime field. The existing common clauses give
`[R(C),R(C)] = F(C)` and `[R(C):F(C)] = 2`, while `F(C)` has odd order.
A proper even normal subgroup is solvable, hence lies in `R(C)`; parity
forces it to supplement `F(C)`. Its image in the resulting quotient of the
solvable radical is both perfect and solvable, so it is trivial. Therefore
an even proper normal subgroup is exactly the solvable radical, and the
quotient is the corresponding PSL₂ group.

This is the kernel bridge used by the original rank-one overcomponent
recognition. Source: Aschbacher--Smith A.3.6 and the radical argument on
printed pp.43--45.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.Section02
open scoped commutatorElement MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.NoncentralFitting
variable {G : Type*} [Group G] [Finite G] {C : Subgroup G}

/-- An even proper normal subgroup is the entire radical in the noncentral-Fitting branch. -/
theorem even_normal_eq_radical {κ : GroupClass} (hG : IsSQTK κ G)
    (hO : pCore 2 G=⊥) (hC : C.IsCComponent)
    (hn : ¬fittingSubgroup C≤center C)
    (N : Subgroup C) [N.Normal] (hN : N≠⊤) (heven : 2∣Nat.card N) :
    N=solvableRadical C := by
  have hquot := primeSL2FittingQuotient_of_noncentral
    RankActions.primeSL2CoverRigidity hG hO hC hn
  have hs := (structure_of_noncentral hG hO hC hn).1
  have hd := CoreShapes.radical_derived_eq_fitting hC hO hquot hs
  have hi := CoreShapes.fitting_radical_index hquot
  have hodd := fitting_odd_card hC hO
  let _ : Group.IsSolvable N :=
    hC.isSolvable_of_subnormal_lt_top (inferInstance : N.Normal).isSubnormal hN
  have hNR : N≤solvableRadical C := le_solvableRadical N inferInstance inferInstance
  have hFR : fittingSubgroup C≤solvableRadical C :=
    le_solvableRadical _ inferInstance inferInstance
  have hnot : ¬N≤fittingSubgroup C := by
    intro h
    exact (Nat.not_even_iff_odd.mpr hodd) ((even_iff_two_dvd).mpr (heven.trans (card_dvd_of_le h)))
  have hjoin : N⊔fittingSubgroup C=solvableRadical C := by
    have hm := (fittingSubgroup C).relIndex_mul_relIndex (N⊔fittingSubgroup C)
      (solvableRadical C) le_sup_right (sup_le hNR hFR)
    rw [hi] at hm
    rcases (Nat.dvd_prime Nat.prime_two).mp (dvd_of_mul_left_eq _ hm) with h | h
    · exact le_antisymm (sup_le hNR hFR) (relIndex_eq_one.mp h)
    · have hf : (fittingSubgroup C).relIndex (N⊔fittingSubgroup C)=1 := by
        rw [h] at hm
        omega
      exact (hnot (le_sup_left.trans (relIndex_eq_one.mp hf))).elim
  let q := QuotientGroup.mk' N
  have hNq : N.map q=⊥ := (Subgroup.map_eq_bot_iff _).mpr (by simpa only [q,QuotientGroup.ker_mk'] using (le_refl N))
  have himg : (fittingSubgroup C).map q=(solvableRadical C).map q := by
    rw [←hjoin,Subgroup.map_sup,hNq,bot_sup_eq]
  let J := (solvableRadical C).map q
  have hp : Group.IsPerfect J := by
    rw [Subgroup.isPerfect_iff,←map_commutator,hd]
    exact himg
  let _ := hp
  let _ : Group.IsSolvable J := Group.isSolvable_of_surjective
    (q.subgroupMap_surjective (solvableRadical C))
  have hj : J=⊥ := by
    by_contra hh
    let _ : Nontrivial J := (Subgroup.nontrivial_iff_ne_bot J).mpr hh
    exact Group.IsPerfect.not_isSolvable J inferInstance
  apply le_antisymm hNR
  simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hj

/-- The actual proper even normal quotient is a prime-field PSL₂, and its kernel is the radical. -/
theorem even_normal_quotient {κ : GroupClass} (hG : IsSQTK κ G)
    (hO : pCore 2 G=⊥) (hC : C.IsCComponent)
    (hn : ¬fittingSubgroup C≤center C)
    (N : Subgroup C) [N.Normal] (hN : N≠⊤) (heven : 2∣Nat.card N) :
    fittingSubgroup C≤N ∧ N=solvableRadical C ∧
      ∃p:ℕ,p.Prime ∧ 3<p ∧ Nonempty ((C⧸N)≃*PSL(2,ZMod p)) := by
  have hR := even_normal_eq_radical hG hO hC hn N hN heven
  refine ⟨hR ▸ le_solvableRadical _ inferInstance inferInstance,hR,?_⟩
  obtain ⟨p,hp,hp3,⟨e⟩⟩ := primeSL2FittingQuotient_of_noncentral
    RankActions.primeSL2CoverRigidity hG hO hC hn
  let _ : Fact p.Prime := ⟨hp⟩
  let q := QuotientGroup.mk' (fittingSubgroup C)
  let _ : Group.IsSolvable q.ker := by
    change Group.IsSolvable (QuotientGroup.mk' (fittingSubgroup C)).ker
    rw [QuotientGroup.ker_mk']
    infer_instance
  refine ⟨p,hp,hp3,⟨(QuotientGroup.quotientMulEquivOfEq hR).trans
    ((solvableRadicalQuotientEquiv q (QuotientGroup.mk'_surjective _)).trans
      (Theory.SpecificGroups.SL2.ResidualTwoExtension.radicalQuotientEquiv
        (by simpa using hp3) e))⟩⟩

/-- Intrinsic source consumer on an actual nonquasisimple C-component carrier. -/
theorem intrinsic_even_normal_quotient {H : Type*} [Group H] [Finite H]
    {κ : GroupClass} (hH : IsSQTK κ H) (hO : pCore 2 H=⊥)
    (hC : (⊤ : Subgroup H).IsCComponent) (hn : ¬IsQuasisimple H)
    (N : Subgroup H) [N.Normal] (hN : N≠⊤) (heven : Even (Nat.card N)) :
    N=solvableRadical H ∧
      ∃p:ℕ,p.Prime ∧ 3<p ∧ Nonempty ((H⧸N)≃*PSL(2,ZMod p)) := by
  let e : (⊤ : Subgroup H)≃*H := topEquiv
  have hnc : ¬fittingSubgroup (⊤ : Subgroup H)≤center (⊤ : Subgroup H) := by
    intro hf
    have hR : solvableRadical (⊤ : Subgroup H)=center (⊤ : Subgroup H) :=
      le_antisymm (solvableRadical_le_center_of_fitting_le_center hf)
        (le_solvableRadical _ inferInstance
          (Group.isSolvable_of_comm (fun a b => Subtype.ext
            (mem_center_iff.mp a.property b).symm)))
    let _ := hC.perfect
    let _ := hC.isSimpleGroup_quotient_solvableRadical
    let _ : IsQuasisimple (⊤ : Subgroup H) :=
      ⟨(QuotientGroup.quotientMulEquivOfEq hR).symm.isSimpleGroup⟩
    exact hn (IsQuasisimple.of_mulEquiv e)
  let N₀ := N.comap e.toMonoidHom
  have hmap : N₀.map e.toMonoidHom=N :=
    map_comap_eq_self_of_surjective e.surjective N
  have hproper : N₀≠⊤ := by
    intro hz
    apply hN
    rw [←hmap,hz,map_top_of_surjective _ e.surjective]
  have hcard : Nat.card N₀=Nat.card N := by
    have hc := Nat.card_congr (N₀.equivMapOfInjective e.toMonoidHom e.injective).toEquiv
    simpa only [hmap] using hc
  obtain ⟨_,hR,p,hp,hp3,⟨f⟩⟩ := even_normal_quotient hH hO hC hnc N₀ hproper
    (by rw [hcard];exact even_iff_two_dvd.mp heven)
  refine ⟨?_,p,hp,hp3,⟨(QuotientGroup.congr N₀ N e hmap).symm.trans f⟩⟩
  rw [←hmap,hR,map_solvableRadical_equiv]

end CFSG.Quasithin.ChapterA.Section03.NoncentralFitting
