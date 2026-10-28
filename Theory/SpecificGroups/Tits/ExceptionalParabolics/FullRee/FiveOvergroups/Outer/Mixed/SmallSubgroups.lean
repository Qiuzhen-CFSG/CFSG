module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Outer.Mixed.Comparison
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Outer.Mixed.Thirteen
public import Theory.GroupTheory.SemidihedralSixteenInvolutions.MarkedCore
public import Theory.SpecificGroups.PSL2.TwentyFiveSmallSubgroups

/-!
# The bounded subgroup calculation for the literal mixed extension

The actual semidihedral Sylow generators put every involution in the
original PSL₂ core. The native core-preserving semilinear equivalence
transports this statement without replacing the extension. Consequently
any subgroup of the literal mixed PSL₂(25) model whose order divides
20480 has order at most twenty, as needed for the remaining 975-point
orbit in Aschbacher--Smith J.5.5(4), printed p.447.
-/

public noncomputable section
open Subgroup
namespace Tits.Max4Outer
open ExceptionalParabolics.FullRee.FiveOvergroups

theorem square_one_mem_core (x : candidateNormalizer) (hx : x^2=1) : x∈normalizerCore := by
  classical
  have hp : IsPGroup 2 (zpowers x) := IsPGroup.of_card
    (show Nat.card (zpowers x)=2^(if x=1 then 0 else 1) from by
      split_ifs with he
      · simp [he]
      · rw [Nat.card_zpowers,orderOf_eq_prime hx he];rfl)
  obtain ⟨Q,hQ⟩ := hp.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq candidateNormalizer Q sylow
  have hmem : g*x*g⁻¹∈sixteen := by
    rw [←sylow_coe,←hg]
    change g*x*g⁻¹∈(Q : Subgroup candidateNormalizer).map (MulAut.conj g).toMonoidHom
    exact mem_map_of_mem (MulAut.conj g).toMonoidHom (hQ (mem_zpowers x))
  have hsq : (g*x*g⁻¹)^2=1 := by rw [conj_pow,hx];group
  have hin := Semidihedral.square_one_mem_of_pair rotation reflector rotation_order
    (reflector_order ▸ pow_orderOf_eq_one reflector) rotation_conjugate normalizerCore
    (normalizerCore.sq_mem_of_index_two normalizerCore_index rotation) reflector_mem_core hmem hsq
  have hh := (inferInstance : normalizerCore.Normal).conj_mem _ hin g⁻¹
  convert hh using 1
  simp [mul_assoc]
end Tits.Max4Outer

namespace Tits.Max4Outer.Mixed
open Max4Projective GorensteinWalter

theorem square_one_mem_pslCore (x : Plus) (hx : x^2=1) : x∈pslCore := by
  obtain ⟨e,he,_⟩ := exists_normalizer_equiv_plus
  have hx' : (e.symm x)^2=1 := by rw [←map_pow,hx,map_one]
  have hcore := square_one_mem_core (e.symm x) hx'
  obtain ⟨y,hy⟩ := coreMap_bijective.surjective ⟨e.symm x,hcore⟩
  have hval := congrArg (fun z : normalizerCore => (z : ExceptionalParabolics.FullRee.FiveOvergroups.candidateNormalizer)) hy
  have her : e (coreMap y : ExceptionalParabolics.FullRee.FiveOvergroups.candidateNormalizer)=x := by
    rw [hval,e.apply_symm_apply]
  have hm := he y
  rw [her] at hm
  change x.val∈pGammaL2PSLRange F
  rw [hm]
  exact ⟨nativeEquiv y,rfl⟩
end Tits.Max4Outer.Mixed

namespace Tits.Max4Outer.Mixed
open Max4Projective Theory.PSL2.TwentyFive

theorem card_le_twenty_of_dvd_20480 (H : Subgroup Plus)
    (hdiv : Nat.card H∣20480) : Nat.card H≤20 :=
  IndexTwo.card_le_twenty_of_involutions_in_core pslCore pslCore_index
    pslCoreEquiv.symm field_card square_one_mem_pslCore H hdiv

end Tits.Max4Outer.Mixed
