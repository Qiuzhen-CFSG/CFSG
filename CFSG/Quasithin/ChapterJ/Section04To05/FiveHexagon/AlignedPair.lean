module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.WeakClosure
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.MarkedTorus

/-!
# Simultaneous pair conjugacy preserving the original torus

The earlier source conjugates (u,C_P(u)) to (z,B₅). Its image of I is an
abelian sixteen in C_G(z)∩N_G(B₅). Sylow conjugacy in that literal local
normalizer moves it into the already constructed wreath complement R;
weak closure then makes it exactly the original I. The correction lies in
the pair normalizer, so both original pair markings are preserved.

Source: Aschbacher–Smith, paragraph before J.4.8, printed p.443.
-/

public section
noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.MarkedNormalizer
open Centralizers Centralizers.Choices MarkedInverter
open Tits.ExceptionalParabolics.FullRee
private instance : Fact (Nat.Prime 2) := ⟨by decide⟩
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
  (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
  {F : Subgroup G} (e : first ≃* F)

include c in
private theorem conjugate_into_complement
    (R J:Subgroup G) (hRH:R≤d.toTypeRuSetup.H)
    (hRN:R≤normalizer (B5Image B5:Set G)) (hR:Nat.card R=32)
    (hJN:J≤d.toTypeRuSetup.H⊓normalizer (B5Image B5:Set G)) (hJ:Nat.card J=16) :
    ∃ n:(d.toTypeRuSetup.H⊓normalizer (B5Image B5:Set G) : Subgroup G), J.conjBy (n:G)≤R := by
  let N := d.toTypeRuSetup.H⊓normalizer (B5Image B5:Set G)
  have hRN' : R≤N := le_inf hRH hRN
  let S:Sylow 2 N := Sylow.ofCard (R.subgroupOf N) (by
    rw [Nat.card_congr (subgroupOfEquivOfLe hRN').toEquiv,hR,
      Section03.local_five_normalizer_card c B5]
    decide +kernel)
  have hp : IsPGroup 2 J := IsPGroup.of_card (n:=4) hJ
  obtain ⟨P,hP⟩ := (hp.comap_subtype (K:=N)).exists_le_sylow
  obtain ⟨n,hn⟩ := MulAction.exists_smul_eq N P S
  have he := congrArg (fun T:Sylow 2 N => (T:Subgroup N)) hn
  change (P:Subgroup N).map (MulAut.conj n).toMonoidHom=R.subgroupOf N at he
  have hm : (J.subgroupOf N).map (MulAut.conj n).toMonoidHom≤R.subgroupOf N :=
    (map_mono hP).trans_eq he
  have hh := map_mono (f:=N.subtype) hm
  have hc : N.subtype.comp (MulAut.conj n).toMonoidHom=
      (MulAut.conj (n:G)).toMonoidHom.comp N.subtype := by ext; rfl
  rw [map_map,hc,← map_map,map_subgroupOf_eq_of_le hJN,
    map_subgroupOf_eq_of_le hRN'] at hh
  exact ⟨n,hh⟩

/-- Simultaneous source conjugacy can be aligned with the same original I. -/
theorem source_pair_conjugacy_preserving_I
    (hz : (e modelZ:G)=c.z)
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom)=B5Image B5)
    (hfusion : IsConj (sourceU e) c.z) :
    ∃ g:G, g*sourceU e*g⁻¹=c.z ∧
      (fixedFive B5 (sourceU e)).conjBy g=B5Image B5 ∧
      (sourceI e).conjBy g=sourceI e := by
  obtain ⟨hu,hi⟩ := source_inverter c B5 e hz hfive
  obtain ⟨g,hgu,hgA⟩ := pair_conjugacy c B5 (sourceU e) hfusion
    (source_three_fives c B5 (sourceU e) hu hfusion hi).1
  obtain ⟨R,hIR,hRH,hRN,hR,hCQ,hd,hgen,heR,hzc,hweak⟩ :=
    exists_source_weakly_closed_complement c B5 e hz hfive
  let J := (sourceI e).conjBy g
  have hJ : Nat.card J=16 :=
    (card_map_of_injective (MulAut.conj g).injective).trans (sourceI_card e)
  have hJH : J≤d.toTypeRuSetup.H := by
    rintro _ ⟨x,hx,rfl⟩
    rw [c.H_eq_centralizer_z,mem_centralizer_singleton_iff,← hgu]
    obtain ⟨a⟩ := sourceI_equiv e
    have he : (⟨x,hx⟩:sourceI e)*⟨sourceU e,(source_marks_mem c e hz).2⟩=
        ⟨sourceU e,(source_marks_mem c e hz).2⟩*(⟨x,hx⟩:sourceI e) := by
      apply a.injective
      rw [map_mul,map_mul,mul_comm]
    have hc := congrArg Subtype.val he
    exact (map_mul (MulAut.conj g) x (sourceU e)).symm.trans
      ((congrArg (MulAut.conj g) hc).trans (map_mul (MulAut.conj g) (sourceU e) x))
  have hJN : J≤normalizer (B5Image B5:Set G) := by
    have hn := (map_mono (f:=(MulAut.conj g).toMonoidHom)
      (sourceI_normalizes_fixed B5 e hfive _ (source_marks_mem c e hz).2)).trans
      ((fixedFive B5 (sourceU e)).le_normalizer_map (MulAut.conj g).toMonoidHom)
    change J≤normalizer ((fixedFive B5 (sourceU e)).conjBy g : Set G) at hn
    rw [hgA] at hn
    exact hn
  obtain ⟨n,hn⟩ := conjugate_into_complement c B5 R J hRH hRN hR (le_inf hJH hJN) hJ
  have hI : (sourceI e).conjBy ((n:G)*g)=sourceI e := by
    apply hweak
    rw [conjBy_mul]
    exact hn
  refine ⟨(n:G)*g,?_,?_,hI⟩
  · calc
      _ = (n:G)*(g*sourceU e*g⁻¹)*(n:G)⁻¹ := by group
      _ = (n:G)*c.z*(n:G)⁻¹ := by rw [hgu]
      _ = c.z := mul_inv_eq_iff_eq_mul.mpr
        (mem_centralizer_singleton_iff.mp (c.H_eq_centralizer_z ▸ n.property.1))
  · rw [conjBy_mul,hgA]
    exact mem_normalizer_iff_map_conj_eq.mp n.property.2

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.MarkedNormalizer
