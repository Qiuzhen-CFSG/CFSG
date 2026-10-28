module

public import Theory.GroupTheory.DihedralPresentation
public import Theory.GroupTheory.OddInvolutionEndpointModels


/-!
# Two involutions with product of order three

The dihedral presentation bounds the generated group by six. The generator
and its product force divisibility by two and three, hence exact order six.
The presentation equivalence then identifies the actual generated subgroup
with S₃. No internal or external conjugacy assumption is needed here.

Source application: Aschbacher–Smith,13.7.10(2), printed p.941.
-/

public section

open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem symmetricThree_of_involutions_product_three
    (a b : G) (ha : a^2=1) (hb : b^2=1) (hab : orderOf (a*b)=3) :
    Nonempty ((zpowers a ⊔ zpowers b : Subgroup G) ≃* Equiv.Perm (Fin 3)) := by
  let P := zpowers a ⊔ zpowers b
  have hP : P = closure ({a,b}:Set G) := by
    change zpowers a ⊔ zpowers b = _
    rw [zpowers_eq_closure, zpowers_eq_closure, ←closure_union]
    congr 1
  have haP : a∈P := mem_sup_left (mem_zpowers a)
  have hbP : b∈P := mem_sup_right (mem_zpowers b)
  have hainv : a⁻¹=a := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using ha)
  have hbinv : b⁻¹=b := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hb)
  have hane : a≠1 := by
    intro hh
    have hbo : orderOf b=3 := by simpa [hh] using hab
    have hd:=orderOf_dvd_of_pow_eq_one hb
    rw [hbo] at hd
    norm_num at hd
  have hao : orderOf a=2 := orderOf_eq_prime ha hane
  have hcard : Nat.card P=6 := by
    have hup := (closure_pair_finite_card_le_of_involutions (by decide : 0<3)
      b a hb ha (hab ▸ pow_orderOf_eq_one (a*b))).2
    have h3 : 3 ∣ Nat.card P := by
      have hh := P.orderOf_dvd_natCard (P.mul_mem haP hbP)
      rwa [hab] at hh
    have h2 : 2 ∣ Nat.card P := by
      have hh := P.orderOf_dvd_natCard haP
      rwa [hao] at hh
    have hlo := Nat.le_of_dvd (Nat.card_pos (α:=P))
      ((by decide : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd h2 h3)
    have hswap : closure ({b,a}:Set G) = P := by
      rw [hP]
      congr 1
      exact Set.pair_comm b a
    rw [hswap] at hup
    omega
  let c : P := ⟨a*b,P.mul_mem haP hbP⟩
  let d : P := ⟨a,haP⟩
  have hc : c^3=1 := Subtype.ext (hab ▸ pow_orderOf_eq_one (a*b))
  have hd : d^2=1 := Subtype.ext ha
  have hinv : d*c*d⁻¹=c⁻¹ := by
    apply Subtype.ext
    change a*(a*b)*a⁻¹=(a*b)⁻¹
    rw [mul_inv_rev,hainv,hbinv,←mul_assoc,show a*a=1 from by simpa only [pow_two] using ha,one_mul]
  have hg : closure ({c,d}:Set P)=⊤ := by
    let R := closure ({c,d}:Set P)
    have hcR : c∈R := subset_closure (by simp)
    have hdR : d∈R := subset_closure (by simp)
    have ham : a∈R.map P.subtype := mem_map_of_mem _ hdR
    have hbm : b∈R.map P.subtype := by
      have hh:= (R.map P.subtype).mul_mem ham (mem_map_of_mem _ hcR)
      change a*(a*b)∈R.map P.subtype at hh
      simpa only [←mul_assoc,show a*a=1 from by simpa only [pow_two] using ha,one_mul] using hh
    have hpR : P≤R.map P.subtype := sup_le (zpowers_le.mpr ham) (zpowers_le.mpr hbm)
    apply top_unique
    intro x _
    obtain ⟨r,hr,he⟩ := hpR x.property
    exact (Subtype.ext he : r=x) ▸ hr
  obtain ⟨e⟩ := dihedralGroup_equiv_of_relations (by decide : 0<3) c d hc hd hinv hg hcard
  obtain ⟨j⟩ := Theory.GroupTheory.nonempty_dihedralThreeEquivPerm
  exact ⟨e.trans j⟩

omit [Finite G] in
/-- The actual product word supplies the internal conjugator between the generators. -/
theorem involutions_product_three_conjugating_word
    (a b:G) (ha:a^2=1) (hb:b^2=1) (hab:(a*b)^3=1) :
    (b*a)⁻¹*a*(b*a)=b := by
  have hai : a⁻¹=a:=inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using ha)
  have hbi : b⁻¹=b:=inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hb)
  have he : (a*b*a*b*a)*b=1 := by simpa only [pow_succ,pow_zero,mul_one,one_mul,mul_assoc] using hab
  have he' : a*b*a*b*a=b := by simpa only [hbi] using mul_eq_one_iff_eq_inv.mp he
  simpa only [mul_inv_rev,hai,hbi,mul_assoc] using he'
end Subgroup

