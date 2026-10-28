module
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Outer.Mixed.SmallSubgroups
public import Theory.SpecificGroups.SymmetricFive.FiveNormalizerSuzuki

/-!
# The native order20 stabilizer is Sz(2)

The order20 point stabilizer has a normal Sylow5 subgroup. A nontrivial
2-core would centralize it, but the native PSL₂(25) calculation excludes
commuting elements of orders2 and5. The existing five-normalizer recognizer
then supplies the literal Suzuki equivalence.

Source: Aschbacher–Smith J.5.5(4), printed p.446.
-/

public noncomputable section
open Subgroup
namespace Tits.Max4Outer.Mixed
open Max4Projective
local instance : Fact (Nat.Prime 2):=⟨Nat.prime_two⟩
local instance : Fact (Nat.Prime 5):=⟨by decide⟩

theorem twenty_twoCore_eq_bot (H:Subgroup Plus) (hc:Nat.card H=20) : pCore 2 H=⊥ := by
  classical
  let P:Sylow 5 H:=default
  have hp:Nat.card P=5:=by rw [P.card_eq_multiplicity,hc];decide +kernel
  have hi:P.index=4:=by
    have hh:=P.toSubgroup.card_mul_index
    rw [hp,hc] at hh
    omega
  have hn:Nat.card (Sylow 5 H)=1:=by
    have hd:=P.card_dvd_index
    rw [hi] at hd
    have hb:=Nat.le_of_dvd (by decide:0<4) hd
    have hm:=card_sylow_modEq_one 5 H
    change Nat.card (Sylow 5 H)%5=1%5 at hm
    omega
  let : Subsingleton (Sylow 5 H):=(Nat.card_eq_one_iff_unique.mp hn).1
  let : P.Normal:=P.normal_of_subsingleton
  by_contra hne
  let : Nontrivial (pCore 2 H):=(Subgroup.nontrivial_iff_ne_bot _).mpr hne
  have hd:2∣Nat.card (pCore 2 H):=
    pCore_isPGroup.card_eq_or_dvd.resolve_left (Nat.ne_of_gt Finite.one_lt_card)
  obtain ⟨v,hv⟩:=exists_prime_orderOf_dvd_card' (G:=pCore 2 H) 2 hd
  obtain ⟨u,hu⟩:=exists_prime_orderOf_dvd_card' (G:=P) 5 (by rw [hp])
  have hvG:orderOf ((v:H):Plus)=2:=by simpa only [orderOf_coe] using hv
  have huG:orderOf ((u:H):Plus)=5:=by simpa only [orderOf_coe] using hu
  have hvpow:((v:H):Plus)^2=1:=
    (congrArg (fun n:ℕ=>((v:H):Plus)^n) hvG).symm.trans (pow_orderOf_eq_one _)
  have hvN:((v:H):Plus)∈pslCore:=square_one_mem_pslCore _ hvpow
  have huN:((u:H):Plus)∈pslCore:=by
    have hodd:Odd (Nat.card ((P:Subgroup H).map H.subtype)):=by
      rw [card_map_of_injective H.subtype_injective,hp];decide
    exact (GorensteinWalter.odd_card_subgroup_le_normal_index_two pslCore
      ((P:Subgroup H).map H.subtype) inferInstance pslCore_index hodd)
      (mem_map_of_mem H.subtype u.property)
  have hdis:Disjoint (pCore 2 H) (P:Subgroup H):=
    IsPGroup.disjoint_of_ne 2 5 (by decide) _ _ pCore_isPGroup P.isPGroup'
  have hcent:pCore 2 H≤centralizer (P:Set H):=
    commutator_eq_bot_iff_le_centralizer.mp (commutator_eq_bot_of_disjoint hdis)
  let uN:pslCore:=⟨((u:H):Plus),huN⟩
  let vN:pslCore:=⟨((v:H):Plus),hvN⟩
  have hcomm:Commute uN vN:=by
    apply Subtype.ext
    exact congrArg H.subtype (mem_centralizer_iff.mp (hcent v.property) u u.property)
  exact GorensteinWalter.psl2_no_commuting_distinct_prime_order
    (show Nat.card F=5^2 from field_card) (by decide:2≠5)
    ((pslCoreEquiv.symm.orderOf_eq uN).trans ((orderOf_coe uN).symm.trans huG))
    ((pslCoreEquiv.symm.orderOf_eq vN).trans ((orderOf_coe vN).symm.trans hvG))
    (hcomm.map pslCoreEquiv.symm.toMonoidHom)

theorem twenty_equiv_suzuki (H:Subgroup Plus) (hc:Nat.card H=20) :
    Nonempty (H≃*BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) :=
  Theory.SpecificGroups.SymmetricFive.FiveNormalizerOvergroups.equiv_suzuki_of_card_twenty
    hc (twenty_twoCore_eq_bot H hc)

end Tits.Max4Outer.Mixed
