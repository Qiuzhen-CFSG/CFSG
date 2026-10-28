module
public import Theory.GroupTheory.SemidihedralOmega
public import Theory.GroupTheory.DihedralGeneratedFactor
public import Stellmacher.ElementaryAbelianMaxDihedral

/-!
# The elementary Thompson subgroup of SD16

The involutions of the semidihedral presentation generate the dihedral
subgroup of order eight. The cyclic subgroup of index two bounds every
elementary subgroup by order four. Thus the maximum elementary subgroups
of the dihedral subgroup are also maximum in SD16 and generate its Thompson
subgroup. The conclusion retains an actual dihedral isomorphism.

Source: Aschbacher--Smith 15.1.22(6), printed p.1100, and the semidihedral
presentation in Alperin--Brauer--Gorenstein, Chapter II, section 1.
-/

public section
open Subgroup Stellmacher
namespace Semidihedral
variable {K : Type*} [Group K] [Finite K]

/-- The elementary Thompson subgroup of an actual SD16 presentation is D8. -/
theorem thompson_sixteen (a b : K) (hcard : Nat.card K = 16)
    (ha : orderOf a = 8) (hb : orderOf b = 2)
    (hab : b*a*b⁻¹ = a^3) (hgen : closure ({a,b} : Set K) = ⊤) :
    Nonempty (elementaryAbelianMaxJ (⊤ : Subgroup K) ≃* DihedralGroup 4) := by
  let D := zpowers (a^2) ⊔ zpowers b
  have ha4 : orderOf (a^2) = 4 := by rw [orderOf_pow,ha]; decide
  have hb2 : b^2 = 1 := hb ▸ pow_orderOf_eq_one b
  have hout : b ∉ zpowers (a^2) := by
    intro hh
    have hc : Commute a b := by
      obtain ⟨i,hi⟩ := hh
      rw [←hi]
      exact (Commute.self_pow a 2).zpow_right i
    exact generators_not_commute (by decide : 4 ≤ 4) ha hab hc
  have hinv : b*a^2*b⁻¹ = (a^2)⁻¹ := by
    have he := congrArg (fun x : K => x^2) hab
    rw [←MulAut.conj_apply, ←map_pow, MulAut.conj_apply, ←pow_mul] at he
    rw [he]
    apply mul_right_cancel (b := a^2)
    rw [←pow_add,show 3*2+2=8 from rfl,←ha,pow_orderOf_eq_one,inv_mul_cancel]
  obtain ⟨hD,⟨eD⟩⟩ := DihedralGroup.sup_zpowers_equiv_of_inversion
    (by decide : 0<4) (a^2) b ha4 hb2 hout hinv
  have hC : (zpowers a).index = 2 := by
    have hh := (zpowers a).index_mul_card
    rw [Nat.card_zpowers,ha,hcard] at hh
    omega
  have hbound (E : Subgroup K) (hE : IsElementaryAbelian 2 E) : Nat.card E ≤ 4 := by
    let := hE
    exact card_le_four_of_pow_two_of_cyclic_index_two (zpowers a) hC E
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 E))
  have hfull : zpowers a ⊔ zpowers b = ⊤ := by
    rwa [←Set.singleton_union,Subgroup.closure_union,←zpowers_eq_closure,←zpowers_eq_closure] at hgen
  have hJle : elementaryAbelianMaxJ (⊤ : Subgroup K) ≤ D := by
    have ho : omegaOneAmbient (⊤ : Subgroup K) = D := by
      rw [←hfull]
      exact omegaOneAmbient_sup_eq (by decide : 2≤3) a b ha hb2 hab
    rw [←ho]
    apply sSup_le
    intro E hE
    let := hE.2.1
    rw [←omegaOneAmbient_eq_self E]
    exact omegaOneAmbient_mono le_top
  have hDJ : D ≤ elementaryAbelianMaxJ (⊤ : Subgroup K) := by
    rw [←dihedral_maxJ D (by decide : 2≤2) eD]
    apply sSup_le
    intro E hE
    have hc : Nat.card E = 4 := ((dihedral_maxFamily_iff D (by decide : 2≤2) eD E).mp hE).2.2
    exact le_sSup ⟨le_top,hE.2.1,fun F _ hF => hc ▸ hbound F hF⟩
  exact ⟨(MulEquiv.subgroupCongr (le_antisymm hJle hDJ)).trans eD⟩
end Semidihedral
