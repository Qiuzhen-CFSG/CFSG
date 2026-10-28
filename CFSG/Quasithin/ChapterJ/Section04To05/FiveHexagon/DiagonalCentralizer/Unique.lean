module
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.DiagonalCentralizer.Whole

/-!
# Uniqueness of the SL₂(5) conjugate containing the original B₅

For a U-conjugate containing B₅, each commutator with B₅ lies in the central
Q-kernel of K. It has both two-power and five-power order, hence is trivial.
The conjugator therefore belongs to C_U(B₅)=Z and fixes K. The full I·U·K
factorization reduces every centralizer conjugate to this case.

Source: the precise conjugacy-orbit uniqueness assertion before J.4.8,
Aschbacher–Smith, printed p.443.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.DiagonalCentralizer
open Subgroup Centralizers Centralizers.Choices MarkedNormalizer MarkedInverter
open Tits.ExceptionalParabolics.FullRee
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
  (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
  {F : Subgroup G} (e : first ≃* F)

theorem U_inf_centralizer_five :
    d.toTypeRuSetup.U⊓centralizer (B5Image B5:Set G)=d.toTypeRuSetup.Z := by
  apply le_antisymm
  · intro u hu
    have hh : u∈CQ B5⊓d.toTypeRuSetup.U := ⟨⟨d.ru2.six.kernel_le hu.1,hu.2⟩,hu.1⟩
    rwa [five_centralizer_inf_U] at hh
  · intro z hz
    exact ⟨d.ru2.natural.kernel_le hz,((five_centralizer_inf_U B5).symm ▸ hz).1.2⟩

/-- In a U-conjugacy class, the actual B5 determines the SL2(5) uniquely. -/
theorem conjugate_eq_of_U (K : Subgroup G) (hKH : K≤d.toTypeRuSetup.H)
    (hBK : B5Image B5≤K) (eK : K≃*Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))
    (u : G) (hu : u∈d.toTypeRuSetup.U) (hBu : B5Image B5≤K.conjBy u) :
    K.conjBy u=K := by
  let := d.elementary_U
  have huc : u∈centralizer (B5Image B5:Set G) := by
    intro b hb
    have hbK := hBK hb
    have hbm := hBu hb
    obtain ⟨k,hk,hku⟩ := hbm
    change u*k*u⁻¹=b at hku
    have hconj : u⁻¹*b*u=k := by rw [← hku]; group
    let a := u⁻¹*b*u*b⁻¹
    have haK : a∈K := by
      change (u⁻¹*b*u)*b⁻¹∈K
      rw [hconj]
      exact K.mul_mem hk (K.inv_mem hbK)
    have haU : a∈d.toTypeRuSetup.U := by
      have hn := d.ru2.natural.normalized (hKH hbK)
      have hh := (mem_normalizer_iff.mp hn u).mp hu
      change u⁻¹*b*u*b⁻¹∈d.toTypeRuSetup.U
      simpa only [mul_assoc] using d.toTypeRuSetup.U.mul_mem (d.toTypeRuSetup.U.inv_mem hu) hh
    have hak : (⟨a,haK⟩:K)∈(componentMap K hKH).ker := by
      change d.ru2.quotientMap (⟨a,hKH haK⟩:d.toTypeRuSetup.H)=1
      apply MonoidHom.mem_ker.mp
      rw [d.ru2.quotient_kernel]
      exact d.ru2.six.kernel_le haU
    rw [(componentMap_structure B5 K hKH hBK eK).1] at hak
    have hac : Commute a b := by
      exact (congrArg Subtype.val (mem_center_iff.mp hak ⟨b,hbK⟩)).symm
    have ha2 : a^2=1 := elemPow_eq_one_of_isElementaryAbelian a haU
    have hb5 : b^5=1 := by
      have hh := pow_card_eq_one' (x := (⟨b,hb⟩:B5Image B5))
      rw [B5Image_card d.card_Z B5] at hh
      exact congrArg Subtype.val hh
    have hab : a*b=u⁻¹*b*u := by dsimp [a]; group
    have ha5 : a^5=1 := by
      have hh : (u⁻¹*b*u)^5=1 := by
        have hz : (MulAut.conj u⁻¹ b)^5=1 := by rw [← map_pow,hb5,map_one]
        simpa only [MulAut.conj_apply,inv_inv] using hz
      rw [← hab,hac.mul_pow,hb5,mul_one] at hh
      exact hh
    have ha1 : a=1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp
      (show orderOf a∣1 from Nat.dvd_gcd
        (orderOf_dvd_of_pow_eq_one ha2) (orderOf_dvd_of_pow_eq_one ha5)))
    have hh : u⁻¹*b*u=b := mul_inv_eq_one.mp ha1
    have he := congrArg (fun x:G => u*x) hh
    simpa only [mul_assoc,mul_inv_cancel_left] using he
  have huz : u∈d.toTypeRuSetup.Z := U_inf_centralizer_five B5 ▸ ⟨hu,huc⟩
  apply mem_normalizer_iff_map_conj_eq.mp
  apply Subgroup.centralizer_le_normalizer
  intro k hk
  exact ((hKH hk) u huz).symm

/-- B5 lies in a unique conjugate of the actual K under the full original
cyclic-four centralizer. This is the precise conjugacy-orbit claim on p.443. -/
theorem conjugate_eq_of_centralizer (hz : (e modelZ:G)=c.z)
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom)=B5Image B5)
    (K : Subgroup G) (hBK : B5Image B5≤K)
    (hKC : K≤centralizer (sourceIz e:Set G))
    (hIK : sourceI e≤normalizer K)
    (eK : K≃*Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))
    (g : G) (hg : g∈centralizer (sourceIz e:Set G))
    (hBg : B5Image B5≤K.conjBy g) : K.conjBy g=K := by
  let N := sourceI e⊔K
  have hKH := hKC.trans (centralizer_le_H c e hz)
  have hNH : N≤d.toTypeRuSetup.H := sup_le (sourceI_le_H c e hz) hKH
  have hNU : N≤normalizer d.toTypeRuSetup.U := hNH.trans d.ru2.natural.normalized
  have hNK : N≤normalizer K := sup_le hIK K.le_normalizer
  have hg' : g∈d.toTypeRuSetup.U⊔N := by
    have he := centralizer_eq c B5 e hz hfive K hBK hKC eK
    rw [he] at hg
    simpa only [N,sup_assoc,sup_comm,sup_left_comm] using hg
  have hp : g∈(d.toTypeRuSetup.U:Set G)*(N:Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hNU]
    exact hg'
  obtain ⟨u,hu,n,hn,rfl⟩ := hp
  rw [conjBy_mul,show K.conjBy n=K from mem_normalizer_iff_map_conj_eq.mp (hNK hn)] at hBg ⊢
  exact conjugate_eq_of_U B5 K hKH hBK eK u hu hBg

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.DiagonalCentralizer
