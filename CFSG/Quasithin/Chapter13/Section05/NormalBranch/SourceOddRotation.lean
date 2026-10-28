module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourcePairCore
public import Theory.GroupTheory.Involution.OddRotation
public import Theory.GroupTheory.BaerSuzukiInternalPair
public import Theory.GroupTheory.PrimeOrderLift

/-!
# An actual cubic rotation for the original normal-branch pair

Baer–Suzuki selects an odd-prime rotation inverted by an original involution
in V outside Q_H. The rotation belongs to its original conjugate pair. Its
order is preserved modulo Q_H, so the already identified S₃ image forces
the actual rotation order to be three.

Source: Aschbacher–Smith13.5.15, printed p.920.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceOddRotation
open Section08.SourceCompletion
open SourceOrthogonal
open BenderSuzuki.PFAppendixIII
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L)≃*alternatingGroup (Fin 6))
  (hseed : D.Vplus=⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬IsMulCommutative D.UH)

include h hU in
theorem exists_odd_rotation : ∃v∈D.V, v∉D.QH ∧ v^2=1 ∧
    ∃p:ℕ,p.Prime ∧ p≠2 ∧ ∃r∈D.H,orderOf r=p ∧ v*r*v⁻¹=r⁻¹ := by
  obtain ⟨v,hv,hvq⟩ := Set.not_subset.mp (module_not_le_core h hU)
  let vH:D.H := ⟨v,h.V_le_H hv⟩
  have hv2 : vH^2=1 := by
    apply Subtype.ext
    let := h.elementary
    exact elemPow_eq_one_of_isElementaryAbelian v hv
  have hvn : vH≠1 := by
    intro hh
    have he : v=1 := congrArg Subtype.val hh
    exact hvq (he ▸ D.QH.one_mem)
  have hvc : vH∉pCore 2 D.H := fun hh=>hvq (mem_map_of_mem D.H.subtype hh)
  obtain ⟨p,hp,hp2,r,hr,hi⟩ :=
    BenderSuzuki.involution_outside_twoCore_inverts_odd_prime vH ⟨hvn,hv2⟩ hvc
  refine ⟨v,hv,hvq,congrArg Subtype.val hv2,p,hp,hp2,r,r.property,?_,?_⟩
  · exact (orderOf_coe r).trans hr
  · have hvi : vH⁻¹=vH := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hv2)
    have hh := congrArg Subtype.val hi
    change v⁻¹*(r:G)*v=(r:G)⁻¹ at hh
    have hvig : v⁻¹=v := congrArg Subtype.val hvi
    simpa only [hvig] using hh

omit [Finite G] in
theorem rotation_mem_pair (v r:G) (hv:v∈D.V) (hv2:v^2=1)
    {p:ℕ} (hp:p.Prime) (hp2:p≠2) (hr:orderOf r=p)
    (hi:v*r*v⁻¹=r⁻¹) : r∈D.V⊔D.V.map (MulAut.conj r).toMonoidHom := by
  let I := D.V⊔D.V.map (MulAut.conj r).toMonoidHom
  have hvi : v⁻¹=v := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hv2)
  have hh : v*r⁻¹*v=r := by
    have hh := congrArg Inv.inv hi
    simpa only [mul_inv_rev,inv_inv,hvi,mul_assoc] using hh
  have hr2 : r^2∈I := by
    have he : r^2=(r*v*r⁻¹)*v := by
      calc
        r^2=r*(v*r⁻¹*v) := by rw [hh,pow_two]
        _=_ := by group
    rw [he]
    exact I.mul_mem (mem_sup_right (mem_map_of_mem (MulAut.conj r).toMonoidHom hv)) (mem_sup_left hv)
  have hcop : Nat.Coprime 2 (orderOf r) := by
    rw [hr]
    exact Nat.prime_two.coprime_iff_not_dvd.mpr
      (fun hd=>hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hd).symm)
  obtain ⟨n,hn⟩ := exists_pow_eq_self_of_coprime hcop
  have hm := I.pow_mem hr2 n
  rwa [hn] at hm

include d h e hseed hn hU in
theorem odd_rotation_is_cubic (v r:G) (hv:v∈D.V) (hv2:v^2=1)
    {p:ℕ} (hp:p.Prime) (hp2:p≠2) (hr:orderOf r=p)
    (hrH:r∈D.H) (hi:v*r*v⁻¹=r⁻¹) : p=3 ∧
    ¬IsPGroup 2 (Section08.Source.starImage D.H (D.V⊔D.V.map (MulAut.conj r).toMonoidHom)) := by
  let I := D.V⊔D.V.map (MulAut.conj r).toMonoidHom
  have hrI := rotation_mem_pair v r hv hv2 hp hp2 hr hi
  let π := QuotientGroup.mk' (pCore 2 D.H)
  let rH:D.H := ⟨r,hrH⟩
  have hcop : Nat.Coprime 2 p := hp.coprime_iff_not_dvd.mpr (by
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)) |>.symm
  have hk : IsPGroup 2 π.ker := by rw [QuotientGroup.ker_mk'];exact pCore_isPGroup
  have hpr : orderOf (π rH)=p :=
    (π.orderOf_map_eq_of_coprime_of_isPGroup_ker hk rH (by
      rw [←orderOf_coe rH];exact hr ▸ hcop)).trans ((orderOf_coe rH).symm.trans hr)
  have hm : π rH∈Section08.Source.starImage D.H I := mem_map_of_mem π hrI
  have hnot : ¬IsPGroup 2 (Section08.Source.starImage D.H I) := by
    intro hh
    obtain ⟨n,hn⟩ := hh.exists_pow_pow_eq_one ⟨π rH,hm⟩
    have hd : p∣2^n := hpr ▸ orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hn)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
  obtain ⟨j⟩ := original_star_pair_symmetricThree d h e hseed hn hU r hrH hnot
  have hc : Nat.card (Section08.Source.starImage D.H I)=6 := by
    rw [Nat.card_congr j.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm]
    decide
  have hd : p∣6 := hc ▸ hpr ▸ (Section08.Source.starImage D.H I).orderOf_dvd_natCard hm
  have h3 : p=3 := by
    have hh : p∣2 ∨ p∣3 := hp.dvd_mul.mp (show p∣2*3 from hd)
    rcases hh with hh|hh
    · exact (hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hh)).elim
    · exact (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp hh
  exact ⟨h3,hnot⟩

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceOddRotation
end
