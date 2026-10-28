module
public import Theory.Frattini.CentralElementarySupplement
public import Theory.Frattini.Intersection
public import Theory.Frattini.BinarySquares
public import Theory.GroupTheory.OddAutomorphismElementaryIndexTwo

/-!
# Frattini layers of a conjugate index-two centralizer pair

Let S be a finite two-subgroup and R=C_S(U) have index two, where U is
central elementary in R. If an automorphism preserving S moves U outside R,
then R and its image are central elementary supplements of their intersection.
Their embedded Frattini subgroups agree and are fixed by the automorphism.
Only S is finite; the ambient group need not be.

This is the binary core-pair calculation in DGS, Groups and Graphs (1985),
proof of 6.5, printed p.122.
-/

open Subgroup
open scoped Pointwise
public section
namespace Subgroup
variable {G : Type*} [Group G]

private theorem index_two_sup_eq (S R U : Subgroup G)
    (hRS : R ≤ S) (hUS : U ≤ S) (hi : R.relIndex S = 2) (ho : ¬ U ≤ R) :
    R ⊔ U = S := by
  have hm := relIndex_mul_relIndex R (R ⊔ U) S le_sup_left (sup_le hRS hUS)
  rw [hi] at hm
  have hn : R.relIndex (R ⊔ U) ≠ 1 := fun he =>
    ho (le_sup_right.trans (relIndex_eq_one.mp he))
  have he : (R ⊔ U).relIndex S = 1 := by
    rcases Nat.prime_mul_iff.mp (hm ▸ Nat.prime_two) with hh | hh
    · exact hh.2
    · exact (hn hh.2).elim
  exact le_antisymm (sup_le hRS hUS) (relIndex_eq_one.mp he)

private theorem central_supplement_intersection (R U W : Subgroup G)
    (hUR : U ≤ R) (hspan : R ≤ U ⊔ W) (hn : U ≤ normalizer (W : Set G)) :
    R = U ⊔ (R ⊓ W) := by
  apply le_antisymm ?_ (sup_le hUR inf_le_left)
  intro r hr
  have hh : r ∈ (U : Set G) * (W : Set G) := by
    rw [←coe_mul_of_left_le_normalizer_right U W hn]
    exact hspan hr
  obtain ⟨u,hu,w,hw,rfl⟩ := hh
  have hwR : w ∈ R := by
    simpa only [inv_mul_cancel_left] using R.mul_mem (R.inv_mem (hUR hu)) hr
  exact mul_mem_sup hu ⟨hwR,hw⟩

private theorem local_frattini_central_supplement (A D Z : Subgroup G)
    [Finite A] (hp : IsPGroup 2 A) (he : IsElementaryAbelian 2 Z)
    (hc : Z ≤ centralizer (A : Set G)) (hA : A = Z ⊔ D) :
    (frattini A).map A.subtype = (frattini D).map D.subtype := by
  have hDA : D ≤ A := hA ▸ le_sup_right
  let : Finite D := Finite.of_injective (inclusion hDA) (inclusion_injective _)
  let : Fact (IsPGroup 2 A) := ⟨hp⟩
  let : Fact (IsPGroup 2 D) := ⟨hp.of_injective (inclusion hDA) (inclusion_injective _)⟩
  let : IsElementaryAbelian 2 Z := he
  apply le_antisymm
  · rw [map_le_iff_le_comap, hp.frattini_eq_closure_squares]
    apply (closure_le (K := ((frattini D).map D.subtype).comap A.subtype)).mpr
    rintro _ ⟨a,rfl⟩
    have hx : (a : G) ∈ (Z : Set G) * (D : Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right Z D
        ((hc.trans (centralizer_le hDA)).trans (centralizer_le_normalizer _)),←hA]
      exact a.property
    obtain ⟨z,hz,d,hd,heq⟩ := hx
    change (a : G) ^ 2 ∈ (frattini D).map D.subtype
    have hcomm : Commute z d := (hc hz d (hDA hd)).symm
    rw [←heq,hcomm.mul_pow,elemPow_eq_one_of_isElementaryAbelian z hz,one_mul]
    exact mem_map_of_mem D.subtype
      (pth_power_mem_frattini_of_isPGroup (p := 2) (⟨d,hd⟩ : D))
  · have hm := map_mono (f := A.subtype)
      (frattini_map_le_of_isPGroup (p := 2) (inclusion hDA))
    simpa only [map_map,subtype_comp_inclusion] using hm

/-- An escaping elementary seed gives both central supplements and an invariant Frattini image. -/
theorem index_two_centralizer_pair_frattini
    (S R U : Subgroup G) [Finite S] (e : G ≃* G)
    (hp : IsPGroup 2 S) (hU : IsElementaryAbelian 2 U)
    (hUR : U ≤ R) (hR : R = S ⊓ centralizer (U : Set G))
    (hi : R.relIndex S = 2) (heS : S.map e.toMonoidHom = S)
    (hout : ¬ U.map e.toMonoidHom ≤ R) :
    let R' := R.map e.toMonoidHom
    let D := R ⊓ R'
    R = U ⊔ D ∧ R' = U.map e.toMonoidHom ⊔ D ∧
      (frattini R).map R.subtype = (frattini D).map D.subtype ∧
      (frattini R').map R'.subtype = (frattini D).map D.subtype ∧
      ((frattini R).map R.subtype).map e.toMonoidHom = (frattini R).map R.subtype := by
  let R' := R.map e.toMonoidHom
  let U' := U.map e.toMonoidHom
  let D := R ⊓ R'
  have hRS : R ≤ S := hR ▸ inf_le_left
  have hR'S : R' ≤ S := (map_mono hRS).trans heS.le
  have hU'R' : U' ≤ R' := map_mono hUR
  have hc : R ≤ centralizer (U : Set G) := hR ▸ inf_le_right
  have hc' : R' ≤ centralizer (U' : Set G) :=
    (map_mono hc).trans (map_centralizer_le_centralizer_image _ _)
  have hR' : R' = S ⊓ centralizer (U' : Set G) := by
    apply le_antisymm (le_inf hR'S hc')
    intro g hg
    apply mem_map_equiv.mpr
    rw [hR]
    refine ⟨?_,?_⟩
    · have hh : g ∈ S.map e.toMonoidHom := heS.symm ▸ hg.1
      exact mem_map_equiv.mp hh
    · intro u hu
      apply e.injective
      simpa only [map_mul,e.apply_symm_apply] using hg.2 (e u) (mem_map_of_mem _ hu)
  have hUn : ¬ U ≤ R' := by
    intro hh
    apply hout
    rw [hR]
    exact le_inf (hU'R'.trans hR'S)
      (le_centralizer_iff.mp (hh.trans hc'))
  have hi' : R'.relIndex S = 2 := by
    rw [←heS,relIndex_map_map_of_injective R S e.injective,hi]
  have hn : S ≤ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hRS).mp (normal_of_index_eq_two hi)
  have hn' : S ≤ normalizer (R' : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hR'S).mp (normal_of_index_eq_two hi')
  have hgen := index_two_sup_eq S R U' hRS (hU'R'.trans hR'S) hi hout
  have hgen' := index_two_sup_eq S R' U hR'S (hUR.trans hRS) hi' hUn
  have hRD : R = U ⊔ D := central_supplement_intersection R U R' hUR
    (by rw [sup_comm,hgen']; exact hRS) ((hUR.trans hRS).trans hn')
  have hR'D : R' = U' ⊔ D := by
    simpa only [D,inf_comm] using central_supplement_intersection R' U' R hU'R'
      (by rw [sup_comm,hgen]; exact hR'S) ((hU'R'.trans hR'S).trans hn)
  let : Finite R := Finite.of_injective (inclusion hRS) (inclusion_injective _)
  let : Finite R' := Finite.of_injective (inclusion hR'S) (inclusion_injective _)
  have hphi := local_frattini_central_supplement R D U (hp.to_le hRS) hU
    (le_centralizer_iff.mp hc) hRD
  let := hU
  have hphi' := local_frattini_central_supplement R' D U' (hp.to_le hR'S)
    (IsElementaryAbelian.map e.toMonoidHom) (le_centralizer_iff.mp hc') hR'D
  exact ⟨hRD,hR'D,hphi,hphi', (frattini_image_map R e.toMonoidHom e.injective).symm.trans
    (hphi'.trans hphi.symm)⟩
/-- Only the finite subgroup being normalized is needed in the ambient odd-action criterion. -/
theorem elementary_relIndex_two_normalized_of_odd_finite (Q S : Subgroup G) [Finite S]
    [IsElementaryAbelian 2 Q] (hQS : Q ≤ S) (hi : Q.relIndex S = 2)
    (hself : S ⊓ centralizer (Q : Set G) = Q)
    (d : G) (hd : d ∈ normalizer (S : Set G)) (ho : Odd (orderOf d)) :
    d ∈ normalizer (Q : Set G) := by
  let P := Q.subgroupOf S
  let e : MulAut S := S.normalizerMonoidHom ⟨d, hd⟩
  let : IsElementaryAbelian 2 P := IsElementaryAbelian.subgroupOf hQS
  have hP : centralizer (P : Set S) = P := by
    apply le_antisymm
    · intro x hx
      have hx' : (x : G) ∈ S ⊓ centralizer (Q : Set G) := by
        refine ⟨x.property, ?_⟩
        intro q hq
        exact congrArg S.subtype (hx ⟨q, hQS hq⟩ hq)
      change (x : G) ∈ Q
      exact hself ▸ hx'
    · exact le_centralizer_iff_isMulCommutative.mpr inferInstance
  have heo : Odd (orderOf e) := ho.of_dvd_nat (by
    simpa only [← Subgroup.orderOf_coe] using
      orderOf_map_dvd S.normalizerMonoidHom (⟨d, hd⟩ : normalizer (S : Set G)))
  have he := elementary_index_two_fixed_of_odd P hi hP e heo
  apply mem_normalizer_iff_map_conj_eq.mpr
  calc
    Q.map (MulAut.conj d).toMonoidHom =
        (P.map e.toMonoidHom).map S.subtype := by
      rw [← map_subgroupOf_eq_of_le hQS, map_map, map_map]
      rfl
    _ = Q := by rw [he]; exact map_subgroupOf_eq_of_le hQS
end Subgroup
